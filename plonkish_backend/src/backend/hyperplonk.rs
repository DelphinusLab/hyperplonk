use crate::frontend;
use crate::util::expression::rotate::Lexical;
use crate::{
    backend::{
        hyperplonk::{
            preprocessor::{batch_size, preprocess},
            prover::{
                instance_polys, lookup_compressed_polys, lookup_h_polys, lookup_m_polys,
                permutation_z_polys, prove_zero_check,
            },
            verifier::verify_zero_check,
        },
        PlonkishBackend, PlonkishCircuit, PlonkishCircuitInfo, WitnessEncoding,
    },
    pcs::PolynomialCommitmentScheme,
    poly::multilinear::MultilinearPolynomial,
    util::{
        arithmetic::{powers, Curve, CurveAffine, PrimeField},
        chain, end_timer,
        expression::{rotate::Rotatable, Expression},
        start_timer,
        transcript::{TranscriptRead, TranscriptWrite},
        Deserialize, DeserializeOwned, Itertools, Serialize,
    },
    Error,
};
use halo2_proofs::arithmetic::MultiMillerLoop;
use halo2_proofs::helpers::Serializable;
use halo2_proofs::helpers::{read_u32, CurveRead};
use halo2_proofs::plonk::Circuit;
use halo2_proofs::poly::commitment as halo2_commitment;
use halo2_proofs::poly::Polynomial;

use rand::RngCore;
use std::{
    fmt::Debug,
    hash::Hash,
    io::{self},
    iter,
    marker::PhantomData,
};

pub(crate) mod preprocessor;
pub(crate) mod prover;
pub mod verifier;

#[cfg(any(test, feature = "benchmark"))]
pub mod util;

#[derive(Clone, Debug)]
pub struct HyperPlonk<Pcs>(PhantomData<Pcs>);

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct HyperPlonkProverSetupParam<F, Pcs>
where
    F: PrimeField,
    Pcs: PolynomialCommitmentScheme<F>,
{
    pub(crate) pcs: Pcs::ProverParam,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(bound = "C: Serialize + DeserializeOwned, C::ScalarExt: Serialize + DeserializeOwned")]
pub struct HyperPlonkProverParam<C: CurveAffine> {
    pub(crate) num_instances: usize,
    pub(crate) num_witness_polys: usize,
    pub(crate) lookups: Vec<Vec<(Expression<C::ScalarExt>, Expression<C::ScalarExt>)>>,
    pub(crate) num_permutation_z_polys: usize,
    pub(crate) num_vars: usize,
    pub(crate) expression: Expression<C::ScalarExt>,
    pub(crate) preprocess_polys: Vec<MultilinearPolynomial<C::ScalarExt>>,
    pub(crate) preprocess_comms: Vec<C>,
    pub(crate) permutation_polys: Vec<(usize, MultilinearPolynomial<C::ScalarExt>)>,
    pub(crate) permutation_comms: Vec<C>,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct HyperPlonkVerifierSetupParam<F, Pcs>
where
    F: PrimeField,
    Pcs: PolynomialCommitmentScheme<F>,
{
    pub pcs: Pcs::VerifierParam,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(bound = "C: Serialize + DeserializeOwned, C::ScalarExt: Serialize + DeserializeOwned")]
pub struct HyperPlonkVerifierParam<C: CurveAffine> {
    pub num_instances: usize,
    pub num_witness_polys: usize,
    pub num_lookups: usize,
    pub num_permutation_z_polys: usize,
    pub num_vars: usize,
    pub expression: Expression<C::ScalarExt>,
    pub named_advices: Vec<(String, u32)>,
    pub preprocess_comms: Vec<C>,
    pub permutation_comms: Vec<C>,
}

impl<C: CurveAffine> Serializable for HyperPlonkVerifierParam<C> {
    fn fetch<R: io::Read>(reader: &mut R) -> io::Result<Self> {
        let num_instances = read_u32(reader)? as usize;
        let num_witness_polys = read_u32(reader)? as usize;
        let num_lookups = read_u32(reader)? as usize;
        let num_permutation_z_polys = read_u32(reader)? as usize;
        let num_vars = read_u32(reader)? as usize;
        let expression = Expression::<C::ScalarExt>::fetch(reader)?;
        let named_advices = Vec::<(String, u32)>::fetch(reader)?;
        let num_preprocess_comms = read_u32(reader)? as usize;
        let preprocess_comms: Vec<_> = (0..num_preprocess_comms)
            .map(|_| C::read(reader))
            .collect::<Result<_, _>>()?;
        let num_permutation_comms = read_u32(reader)? as usize;
        let permutation_comms: Vec<_> = (0..num_permutation_comms)
            .map(|_| C::read(reader))
            .collect::<Result<_, _>>()?;
        Ok(Self {
            num_instances,
            num_witness_polys,
            num_lookups,
            num_permutation_z_polys,
            num_vars,
            expression,
            named_advices,
            preprocess_comms,
            permutation_comms,
        })
    }

    fn store<W: io::Write>(&self, writer: &mut W) -> io::Result<()> {
        writer.write(&(self.num_instances as u32).to_le_bytes())?;
        writer.write(&(self.num_witness_polys as u32).to_le_bytes())?;
        writer.write(&(self.num_lookups as u32).to_le_bytes())?;
        writer.write(&(self.num_permutation_z_polys as u32).to_le_bytes())?;
        writer.write(&(self.num_vars as u32).to_le_bytes())?;
        self.expression.store(writer)?;
        self.named_advices.store(writer)?;
        writer.write(&(self.preprocess_comms.len() as u32).to_le_bytes())?;
        for commitment in &self.preprocess_comms {
            writer.write_all(commitment.to_bytes().as_ref())?;
        }
        writer.write(&(self.permutation_comms.len() as u32).to_le_bytes())?;
        for commitment in &self.permutation_comms {
            writer.write_all(commitment.to_bytes().as_ref())?;
        }
        Ok(())
    }
}

impl<C, Pcs> PlonkishBackend<C> for HyperPlonk<Pcs>
where
    C: CurveAffine + Serialize + DeserializeOwned,
    C::ScalarExt: Hash + Serialize + DeserializeOwned,
    Pcs: PolynomialCommitmentScheme<
        C::ScalarExt,
        Polynomial = MultilinearPolynomial<C::ScalarExt>,
        CommitmentChunk = C,
    >,
{
    type Pcs = Pcs;
    type ProverParam = HyperPlonkProverParam<C>;
    type VerifierParam = HyperPlonkVerifierParam<C>;
    type ProverSetupParam = HyperPlonkProverSetupParam<C::ScalarExt, Pcs>;
    type VerifierSetupParam = HyperPlonkVerifierSetupParam<C::ScalarExt, Pcs>;

    fn setup(
        circuit_info: &PlonkishCircuitInfo<C::ScalarExt>,
        rng: impl RngCore,
    ) -> Result<Pcs::Param, Error> {
        assert!(circuit_info.is_well_formed());

        let num_vars = circuit_info.k;
        let poly_size = 1 << num_vars;
        let batch_size = batch_size(circuit_info);
        Pcs::setup(poly_size, batch_size, rng)
    }

    fn preprocess(
        param: &Pcs::Param,
        circuit_info: &PlonkishCircuitInfo<C::ScalarExt>,
    ) -> Result<
        (
            Self::ProverParam,
            Self::VerifierParam,
            Self::ProverSetupParam,
            Self::VerifierSetupParam,
        ),
        Error,
    > {
        preprocess(param, circuit_info, |pp, polys| {
            let comms = Pcs::batch_commit(pp, &polys)?;
            Ok((polys, comms))
        })
    }

    fn prove(
        ps: &Self::ProverSetupParam,
        pp: &Self::ProverParam,
        circuit: &impl PlonkishCircuit<C::ScalarExt>,
        transcript: &mut impl TranscriptWrite<C, C::ScalarExt>,
    ) -> Result<(), Error> {
        assert_eq!(circuit.instances().len(), pp.num_instances);
        let instance_polys = {
            let instances = circuit.instances();

            for instances in circuit.instances().iter() {
                for instance in instances.iter() {
                    transcript.common_field_element(instance)?;
                }
            }
            instance_polys::<_, Lexical>(pp.num_vars, instances)
        };

        // Round 0..n

        let mut witness_polys = Vec::with_capacity(pp.num_witness_polys);
        let mut witness_comms = Vec::with_capacity(pp.num_witness_polys);
        let mut challenges = Vec::with_capacity(4);

        let timer = start_timer(|| "witness_collector");
        let polys = circuit
            .synthesize()?
            .into_iter()
            .map(MultilinearPolynomial::new)
            .collect_vec();
        assert_eq!(polys.len(), pp.num_witness_polys);
        end_timer(timer);
        witness_comms.extend(Pcs::batch_commit_and_write(&ps.pcs, &polys, transcript)?);
        witness_polys.extend(polys);
        let polys = chain![&instance_polys, &pp.preprocess_polys, &witness_polys].collect_vec();

        // Round n

        let beta = transcript.squeeze_challenge();

        let timer = start_timer(|| format!("lookup_compressed_polys-{}", pp.lookups.len()));
        let lookup_compressed_polys = {
            let max_lookup_width = pp.lookups.iter().map(Vec::len).max().unwrap_or_default();
            let betas = powers(beta).take(max_lookup_width).collect_vec();
            lookup_compressed_polys::<_, Lexical>(&pp.lookups, &polys, &challenges, &betas)
        };
        end_timer(timer);
        let timer = start_timer(|| format!("lookup_m_polys-{}", pp.lookups.len()));
        let lookup_m_polys = lookup_m_polys(&lookup_compressed_polys)?;
        end_timer(timer);

        let lookup_m_comms = Pcs::batch_commit_and_write(&ps.pcs, &lookup_m_polys, transcript)?;

        // Round n+1

        let gamma = transcript.squeeze_challenge();

        let timer = start_timer(|| format!("lookup_h_polys-{}", pp.lookups.len()));
        let lookup_h_polys = lookup_h_polys(&lookup_compressed_polys, &lookup_m_polys, &gamma);
        end_timer(timer);

        let timer = start_timer(|| format!("permutation_z_polys-{}", pp.permutation_polys.len()));
        let permutation_z_polys = permutation_z_polys::<_, Lexical>(
            pp.num_permutation_z_polys,
            &pp.permutation_polys,
            &polys,
            &beta,
            &gamma,
        );
        end_timer(timer);

        let lookup_h_permutation_z_polys =
            chain![lookup_h_polys.iter(), permutation_z_polys.iter()].collect_vec();
        let lookup_h_permutation_z_comms =
            Pcs::batch_commit_and_write(&ps.pcs, lookup_h_permutation_z_polys.clone(), transcript)?;

        // Round n+2

        let alpha = transcript.squeeze_challenge();
        let y = transcript.squeeze_challenges(pp.num_vars);

        let polys = chain![
            polys,
            pp.permutation_polys.iter().map(|(_, poly)| poly),
            lookup_m_polys.iter(),
            lookup_h_permutation_z_polys,
        ]
        .collect_vec();
        challenges.extend([beta, gamma, alpha]);
        let (points, evals) = prove_zero_check(
            pp.num_instances,
            &pp.expression,
            &polys,
            challenges,
            y,
            transcript,
        )?;

        // PCS open

        let dummy_comm = Pcs::Commitment::default();
        let preprocess_comms = pp
            .preprocess_comms
            .iter()
            .map(|c| Pcs::Commitment::from(*c))
            .collect::<Vec<_>>();
        let permutation_comms = pp
            .permutation_comms
            .iter()
            .map(|c| Pcs::Commitment::from(*c))
            .collect::<Vec<_>>();

        let comms = chain![
            iter::repeat(&dummy_comm).take(pp.num_instances),
            &preprocess_comms,
            &witness_comms,
            &permutation_comms,
            &lookup_m_comms,
            &lookup_h_permutation_z_comms,
        ]
        .collect_vec();
        let timer = start_timer(|| format!("pcs_batch_open-{}", evals.len()));
        Pcs::batch_open_for_shift(&ps.pcs, polys, comms, &points, &evals, transcript)?;
        end_timer(timer);

        println!("prove_with_shift done");
        Ok(())
    }

    fn verify(
        vs: &Self::VerifierSetupParam,
        vp: &Self::VerifierParam,
        instances: &[Vec<C::ScalarExt>],
        transcript: &mut impl TranscriptRead<Pcs::CommitmentChunk, C::ScalarExt>,
    ) -> Result<(), Error> {
        assert_eq!(instances.len(), vp.num_instances);
        for instances in instances.iter() {
            for instance in instances.iter() {
                transcript.common_field_element(instance)?;
            }
        }
        // Round 0..n

        let mut witness_comms = Vec::with_capacity(vp.num_witness_polys);
        let mut challenges = Vec::with_capacity(4);
        witness_comms.extend(Pcs::read_commitments(
            &vs.pcs,
            vp.num_witness_polys,
            transcript,
        )?);

        // Round n

        let beta = transcript.squeeze_challenge();

        let lookup_m_comms = Pcs::read_commitments(&vs.pcs, vp.num_lookups, transcript)?;

        // Round n+1

        let gamma = transcript.squeeze_challenge();

        let lookup_h_permutation_z_comms = Pcs::read_commitments(
            &vs.pcs,
            vp.num_lookups + vp.num_permutation_z_polys,
            transcript,
        )?;

        // Round n+2

        let alpha = transcript.squeeze_challenge();
        let y = transcript.squeeze_challenges(vp.num_vars);

        challenges.extend([beta, gamma, alpha]);
        let (points, evals) = verify_zero_check(
            vp.num_vars,
            &vp.expression,
            instances,
            &challenges,
            &y,
            transcript,
        )?;
        // PCS verify

        let dummy_comm = Pcs::Commitment::default();
        let preprocess_comms = vp
            .preprocess_comms
            .iter()
            .map(|c| Pcs::Commitment::from(*c))
            .collect::<Vec<_>>();
        let permutation_comms = vp
            .permutation_comms
            .iter()
            .map(|c| Pcs::Commitment::from(*c))
            .collect::<Vec<_>>();
        let comms = chain![
            iter::repeat(&dummy_comm).take(vp.num_instances),
            &preprocess_comms,
            &witness_comms,
            &permutation_comms,
            &lookup_m_comms,
            &lookup_h_permutation_z_comms,
        ]
        .collect_vec();
        Pcs::batch_verify_for_shift(&vs.pcs, comms, &points, &evals, transcript)?;

        Ok(())
    }
}

impl<Pcs> WitnessEncoding for HyperPlonk<Pcs> {
    fn row_mapping(k: usize) -> Vec<usize> {
        Lexical::new(k).usable_indices()
    }
}

use preprocessor::compose;
//adapt halo2's Params directly, not take PCS:Params
pub fn keygen_vk<E: MultiMillerLoop, T: Circuit<E::Scalar>>(
    params: &halo2_commitment::Params<E::G1Affine>,
    circuit: &T,
) -> Result<HyperPlonkVerifierParam<E::G1Affine>, crate::Error> {
    let k = params.get_k();
    let circuit_info = frontend::halo2::get_circuit_info::<E, T>(k, circuit)?;

    let preprocess_comms = circuit_info
        .preprocess_polys
        .iter()
        .map(|values| params.commit(&Polynomial::new(values.clone())).to_affine())
        .collect();

    let permutation_polys = preprocessor::permutation_polys(
        k as usize,
        &circuit_info.permutation_polys(),
        &circuit_info.permutations,
    );
    let permutation_polys = permutation_polys
        .into_iter()
        .map(|p| Polynomial::new(p.into_evals()))
        .collect::<Vec<_>>();
    let permutation_comms = permutation_polys
        .iter()
        .map(|poly| params.commit(poly).to_affine())
        .collect();
    // Compose expression
    let (num_permutation_z_polys, expression) = compose(&circuit_info);

    Ok(HyperPlonkVerifierParam {
        num_instances: circuit_info.num_instances,
        num_witness_polys: circuit_info.num_witness_polys,
        num_lookups: circuit_info.lookups.len(),
        num_permutation_z_polys,
        num_vars: circuit_info.k,
        expression,
        named_advices: circuit_info.named_witnesses.clone(),
        preprocess_comms,
        permutation_comms,
    })
}

#[cfg(test)]
mod test {
    use crate::{
        backend::{
            hyperplonk::{
                util::{rand_vanilla_plonk_circuit, rand_vanilla_plonk_w_lookup_circuit},
                HyperPlonk,
            },
            test::run_plonkish_backend,
        },
        pcs::{
            multilinear::{
                Gemini, MultilinearBrakedown, MultilinearHyrax, MultilinearIpa, MultilinearKzg,
                Zeromorph,
            },
            univariate::UnivariateKzg,
        },
        util::{
            code::BrakedownSpec6, expression::rotate::BinaryField, hash::Keccak256,
            test::seeded_std_rng, transcript::Keccak256Transcript,
        },
    };
    use halo2_curves::{
        bn256::{self, Bn256},
        grumpkin,
    };

    macro_rules! tests {
        ($suffix:ident, $pcs:ty, $num_vars_range:expr) => {
            paste::paste! {
                #[test]
                fn [<vanilla_plonk_w_ $suffix>]() {
                    run_plonkish_backend::<_, HyperPlonk<$pcs>, Keccak256Transcript<_>, _>($num_vars_range, |num_vars| {
                        rand_vanilla_plonk_circuit::<_, BinaryField>(num_vars, seeded_std_rng(), seeded_std_rng())
                    });
                }

                #[test]
                fn [<vanilla_plonk_w_lookup_w_ $suffix>]() {
                    run_plonkish_backend::<_, HyperPlonk<$pcs>, Keccak256Transcript<_>, _>($num_vars_range, |num_vars| {
                        rand_vanilla_plonk_w_lookup_circuit::<_, BinaryField>(num_vars, seeded_std_rng(), seeded_std_rng())
                    });
                }
            }
        };
        ($suffix:ident, $pcs:ty) => {
            tests!($suffix, $pcs, 2..16);
        };
    }

    tests!(brakedown, MultilinearBrakedown<bn256::Fr, Keccak256, BrakedownSpec6>);
    tests!(hyrax, MultilinearHyrax<grumpkin::G1Affine>, 5..16);
    tests!(ipa, MultilinearIpa<grumpkin::G1Affine>);
    tests!(kzg, MultilinearKzg<Bn256>);
    tests!(gemini_kzg, Gemini<UnivariateKzg<Bn256>>);
    tests!(zeromorph_kzg, Zeromorph<UnivariateKzg<Bn256>>);
}
