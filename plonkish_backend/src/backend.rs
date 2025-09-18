use crate::{
    pcs::{CommitmentChunk, PolynomialCommitmentScheme},
    util::{
        arithmetic::CurveAffine,
        chain,
        expression::Expression,
        transcript::{TranscriptRead, TranscriptWrite},
        DeserializeOwned, Itertools, Serialize,
    },
    Error,
};
use rand::RngCore;
use std::{collections::BTreeSet, fmt::Debug};

pub mod hyperplonk;

pub trait PlonkishBackend<C: CurveAffine>: Clone + Debug {
    type Pcs: PolynomialCommitmentScheme<C::ScalarExt, CommitmentChunk = C>;
    type ProverParam: Clone + Debug + Serialize + DeserializeOwned;
    type VerifierParam: Clone + Debug + Serialize + DeserializeOwned;
    type ProverSetupParam: Clone + Debug;
    type VerifierSetupParam: Clone + Debug;

    fn setup(
        circuit_info: &PlonkishCircuitInfo<C::ScalarExt>,
        rng: impl RngCore,
    ) -> Result<<Self::Pcs as PolynomialCommitmentScheme<C::ScalarExt>>::Param, Error>;


    fn preprocess(
        param: &<Self::Pcs as PolynomialCommitmentScheme<C::ScalarExt>>::Param,
        circuit_info: &PlonkishCircuitInfo<C::ScalarExt>,
    ) -> Result<
        (
            Self::ProverParam,
            Self::VerifierParam,
            Self::ProverSetupParam,
            Self::VerifierSetupParam,
        ),
        Error,
    >;

    fn prove(
        ps: &Self::ProverSetupParam,
        pp: &Self::ProverParam,
        circuit: &impl PlonkishCircuit<C::ScalarExt>,
        transcript: &mut impl TranscriptWrite<CommitmentChunk<C::ScalarExt, Self::Pcs>, C::ScalarExt>,
    ) -> Result<(), Error>;

    fn verify(
        vs: &Self::VerifierSetupParam,
        vp: &Self::VerifierParam,
        instances: &[Vec<C::ScalarExt>],
        transcript: &mut impl TranscriptRead<CommitmentChunk<C::ScalarExt, Self::Pcs>, C::ScalarExt>,
    ) -> Result<(), Error>;
}

#[derive(Clone, Debug)]
pub struct PlonkishCircuitInfo<F> {
    /// 2^k is the size of the circuit
    pub k: usize,
    /// Number of instance columns.
    pub num_instances: usize,
    /// Preprocessed polynomials, which has index starts with offset
    /// `num_instances.len()`.
    pub preprocess_polys: Vec<Vec<F>>,
    /// Number of witness polynoimal in each phase.
    /// Witness polynomial index starts with offset `num_instances.len()` +
    /// `preprocess_polys.len()`.
    pub num_witness_polys: usize,
    /// named advices column
    pub named_witnesses: Vec<(String, u32)>,
    // /// Number of challenge in each phase.
    // pub num_challenges: Vec<usize>,
    /// Constraints.
    pub constraints: Vec<Expression<F>>,
    /// Each item inside outer vector repesents an independent vector lookup,
    /// which contains vector of tuples representing the input and table
    /// respectively.
    pub lookups: Vec<Vec<(Expression<F>, Expression<F>)>>,
    /// Each item inside outer vector repesents an closed permutation cycle,
    /// which contains vetor of tuples representing the polynomial index and
    /// row respectively.
    pub permutations: Vec<Vec<(usize, usize)>>,
    /// Maximum degree of constraints
    pub max_degree: Option<usize>,
}

impl<F: Clone> PlonkishCircuitInfo<F> {
    pub fn is_well_formed(&self) -> bool {
        let num_poly = self.num_poly();
        // let num_challenges = self.num_challenges.iter().sum::<usize>();
        let polys = chain![
            self.expressions().flat_map(Expression::used_poly),
            self.permutation_polys(),
        ]
        .collect::<BTreeSet<_>>();
        let challenges = chain![self.expressions().flat_map(Expression::used_challenge)]
            .collect::<BTreeSet<_>>();
        // Polynomial indices are in range
        self.num_witness_polys>0
            &&(polys.is_empty() || *polys.last().unwrap() < num_poly)
            // Challenge indices are in range
            && challenges.is_empty()
            // Every constraint has degree less equal than `max_degree`
            && self
                .max_degree
                .map(|max_degree| {
                    !self
                        .constraints
                        .iter()
                        .any(|constraint| constraint.degree() > max_degree)
                })
                .unwrap_or(true)
    }

    pub fn num_poly(&self) -> usize {
        self.num_instances + self.preprocess_polys.len() + self.num_witness_polys
    }

    pub fn permutation_polys(&self) -> Vec<usize> {
        self.permutations
            .iter()
            .flat_map(|cycle| cycle.iter().map(|(poly, _)| *poly))
            .unique()
            .sorted()
            .collect()
    }

    pub fn expressions(&self) -> impl Iterator<Item = &Expression<F>> {
        chain![
            &self.constraints,
            chain![&self.lookups]
                .flat_map(|lookup| lookup.iter().flat_map(|(input, table)| [input, table])),
        ]
    }
}

pub trait PlonkishCircuit<F> {
    fn circuit_info(&self) -> Result<PlonkishCircuitInfo<F>, Error>;

    fn instances(&self) -> &[Vec<F>];

    fn synthesize(&self) -> Result<Vec<Vec<F>>, Error>;
}

pub trait WitnessEncoding {
    fn row_mapping(k: usize) -> Vec<usize>;
}

#[cfg(any(test, feature = "benchmark"))]
mod mock {
    use crate::{
        backend::{PlonkishCircuit, PlonkishCircuitInfo},
        Error,
    };

    pub(crate) struct MockCircuit<F> {
        instances: Vec<Vec<F>>,
        witnesses: Vec<Vec<F>>,
    }

    impl<F> MockCircuit<F> {
        pub(crate) fn new(instances: Vec<Vec<F>>, witnesses: Vec<Vec<F>>) -> Self {
            Self {
                instances,
                witnesses,
            }
        }
    }

    impl<F: Clone> PlonkishCircuit<F> for MockCircuit<F> {
        fn circuit_info_without_preprocess(&self) -> Result<PlonkishCircuitInfo<F>, Error> {
            unreachable!()
        }

        fn circuit_info(&self) -> Result<PlonkishCircuitInfo<F>, Error> {
            unreachable!()
        }

        fn instances(&self) -> &[Vec<F>] {
            &self.instances
        }

        fn synthesize(&self, round: usize, challenges: &[F]) -> Result<Vec<Vec<F>>, Error> {
            assert!(round == 0 && challenges.is_empty());
            Ok(self.witnesses.clone())
        }
    }
}

#[cfg(test)]
pub(crate) mod test {
    use crate::{
        backend::{PlonkishBackend, PlonkishCircuit, PlonkishCircuitInfo},
        pcs::PolynomialCommitmentScheme,
        util::{
            arithmetic::PrimeField,
            end_timer, start_timer,
            test::seeded_std_rng,
            transcript::{InMemoryTranscript, TranscriptRead, TranscriptWrite},
            DeserializeOwned, Serialize,
        },
    };
    use std::{hash::Hash, ops::Range};

    pub fn run_plonkish_backend<F, Pb, T, C>(
        num_vars_range: Range<usize>,
        circuit_fn: impl Fn(usize) -> (PlonkishCircuitInfo<F>, C),
    ) where
        F: PrimeField + Hash + Serialize + DeserializeOwned,
        Pb: PlonkishBackend<F>,
        T: TranscriptRead<<Pb::Pcs as PolynomialCommitmentScheme<F>>::CommitmentChunk, F>
            + TranscriptWrite<<Pb::Pcs as PolynomialCommitmentScheme<F>>::CommitmentChunk, F>
            + InMemoryTranscript<Param = ()>,
        C: PlonkishCircuit<F>,
    {
        for num_vars in num_vars_range {
            let (circuit_info, circuit) = circuit_fn(num_vars);
            let instances = circuit.instances();

            let timer = start_timer(|| format!("setup-{num_vars}"));
            let param = Pb::setup(&circuit_info, seeded_std_rng()).unwrap();
            end_timer(timer);

            let timer = start_timer(|| format!("preprocess-{num_vars}"));
            let (pp, vp) = Pb::preprocess(&param, &circuit_info).unwrap();
            end_timer(timer);

            let timer = start_timer(|| format!("prove-{num_vars}"));
            let proof = {
                let mut transcript = T::new(());
                Pb::prove_with_shift(&pp, &circuit, &mut transcript, seeded_std_rng()).unwrap();
                transcript.into_proof()
            };
            end_timer(timer);

            let timer = start_timer(|| format!("verify-{num_vars}"));
            let result = {
                let mut transcript = T::from_proof((), proof.as_slice());
                Pb::verify_with_shift(&vp, instances, &mut transcript, seeded_std_rng())
            };
            assert_eq!(result, Ok(()));
            end_timer(timer);
        }
    }
}
