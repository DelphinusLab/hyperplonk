use crate::{
    backend::{PlonkishCircuit, PlonkishCircuitInfo},
    transform::circuit::ZKWASMCircuit,
    util::{
        chain,
        expression::{Expression, Query, Rotation},
        Itertools,
    },
};
use halo2_proofs::arithmetic::Field;
use halo2_proofs::plonk::{self, Any, Circuit, ConstraintSystem, Selector};
use halo2_proofs::{
    arithmetic::MultiMillerLoop,
    helpers::get_witness,
    plonk::{get_preprocess_polys_and_permutations, Circuit as ZkCircuit},
};
use rand::RngCore;
use std::collections::HashMap;

#[cfg(any(test, feature = "benchmark"))]
pub mod circuit;
#[cfg(test)]
mod test;

pub trait CircuitExt<F: Field>: Circuit<F> {
    fn rand(_k: usize, _rng: impl RngCore) -> Self
    where
        Self: Sized,
    {
        unimplemented!()
    }

    fn instances(&self) -> Vec<Vec<F>>;

    fn num_instances(&self) -> Vec<usize> {
        self.instances().iter().map(Vec::len).collect()
    }
}

impl<'a, E: MultiMillerLoop, C: ZkCircuit<E::Scalar>> PlonkishCircuit<E::Scalar>
    for ZKWASMCircuit<'a, E, C>
{
    fn circuit_info_without_preprocess(
        &self,
    ) -> Result<PlonkishCircuitInfo<E::Scalar>, crate::Error> {
        let Self {
            k, instances, cs, ..
        } = self;
        //todo for only 1 phase halo2, this challenge is not needed
        let challenge_idx = vec![];
        let advice_idx = advice_idx(cs);
        let constraints: Vec<Expression<E::Scalar>> = cs
            .gates
            .iter()
            .flat_map(|gate| {
                gate.polynomials().iter().map(|expression| {
                    convert_expression(cs, &advice_idx, &challenge_idx, expression)
                })
            })
            .collect();
        let lookups = cs
            .lookups_classic
            .iter()
            .map(|lookup| {
                lookup
                    .input_expressions
                    .iter()
                    .zip(lookup.table_expressions.iter())
                    .map(|(input, table)| {
                        let [input, table] = [input, table].map(|expression| {
                            convert_expression(cs, &advice_idx, &challenge_idx, expression)
                        });
                        (input, table)
                    })
                    .collect_vec()
            })
            .collect();

        let num_instances = instances.iter().map(Vec::len).collect_vec();
        let preprocess_polys =
            vec![vec![E::Scalar::zero(); 1 << k]; cs.num_selectors + cs.num_fixed_columns];
        Ok(PlonkishCircuitInfo {
            k: *k as usize,
            num_instances,
            preprocess_polys,
            //TODO: remove vector witnesses, keep one
            num_witness_polys: num_advice_poly(cs.num_advice_columns),
            named_witnesses: cs.named_advices.clone(),
            //for one phase halo2, challenge is not needed
            num_challenges: vec![0],
            constraints,
            lookups,
            permutations:vec![],
            max_degree: Some(cs.degree()),
        })
    }

    fn circuit_info(&self) -> Result<PlonkishCircuitInfo<E::Scalar>, crate::Error> {
        let Self {
            k,
            config,
            circuit,
            row_mapping,
            cs,
            ..
        } = self;
        let mut circuit_info = self.circuit_info_without_preprocess()?;
        let column_idx = column_idx(cs);
        let permutation_column_idx = cs
            .permutation
            .get_columns()
            .iter()
            .map(|column| {
                let key = (*column.column_type(), column.index());
                (key, column_idx[&key])
            })
            .collect();

        let (fixed, permutation) = get_preprocess_polys_and_permutations::<E::G1Affine, C>(
            k.clone(),
            row_mapping,
            permutation_column_idx,
            circuit,
            config,
        )
        .map_err(|e| {
            crate::Error::InvalidSnark(format!(
                "Preprocess: error in halo2-gpu-specific Synthesis: {:?}",
                e
            ))
        })?;

        circuit_info.preprocess_polys = fixed.into_iter().map(|poly| poly.values).collect();
        circuit_info.permutations = permutation;
        Ok(circuit_info)
    }

    fn instances(&self) -> &[Vec<E::Scalar>] {
        &self.instances
    }

    fn synthesize(
        &self,
        phase: usize,
        _: &[E::Scalar],
    ) -> Result<Vec<Vec<E::Scalar>>, crate::Error> {
        if phase != 0 {
            return Ok(vec![]);
        }

        let instances_slices: Vec<&[E::Scalar]> =
            self.instances_scalar.iter().map(|v| v.as_slice()).collect();

        let witness_polys = get_witness::<E::G1Affine, C>(
            self.k,
            instances_slices.as_slice(),
            &self.row_mapping,
            &self.circuit,
        )
        .map_err(|e| {
            crate::Error::InvalidSnark(format!(
                "Synthesis: error in halo2-gpu-specific Synthesis: {:?}",
                e
            ))
        })?;
        let advices: Vec<Vec<E::Scalar>> =
            witness_polys.into_iter().map(|poly| poly.values).collect();

        Ok(advices)
    }
}

fn get_advice_offset<F: Field>(cs: &ConstraintSystem<F>)->usize{
    cs.num_instance_columns + cs.num_fixed_columns + cs.num_selectors
}

//todo
fn advice_idx<F: Field>(cs: &ConstraintSystem<F>) -> Vec<usize> {
    let advice_offset = get_advice_offset(cs);
    (0..cs.num_advice_columns)
        .map(|idx| idx + advice_offset)
        .collect()
}

fn column_idx<F: Field>(cs: &ConstraintSystem<F>) -> HashMap<(Any, usize), usize> {
    let advice_idx = advice_idx(cs);
    chain![
        (0..cs.num_instance_columns).map(|idx| (Any::Instance, idx)),
        (0..cs.num_fixed_columns + cs.num_selectors).map(|idx| (Any::Fixed, idx)),
    ]
    .enumerate()
    .map(|(idx, column)| (column, idx))
    .chain((0..advice_idx.len()).map(|idx| ((Any::Advice, idx), advice_idx[idx])))
    .collect()
}

//similar with num_by_phase for just advice without phase
fn num_advice_poly(num_advice: usize) -> Vec<usize> {
    vec![num_advice]
}

fn convert_expression<F: Field>(
    cs: &ConstraintSystem<F>,
    advice_idx: &[usize],
    _challenge_idx: &[usize],
    expression: &plonk::Expression<F>,
) -> Expression<F> {
    expression.evaluate(
        &|constant| Expression::Constant(constant),
        &|selector: Selector| {
            let poly = cs.num_instance_columns + cs.num_fixed_columns + selector.index();

            Query::new(poly, Rotation::cur()).into()
        },
        &|_qry_idx, col_idx, rotation| {
            let poly = cs.num_instance_columns + col_idx;
            Query::new(poly, Rotation(rotation.0)).into()
        },
        &|_qry_idx, col_idx, rotation| {
            let poly = advice_idx[col_idx];

            Query::new(poly, Rotation(rotation.0)).into()
        },
        &|_qry_idx, col_idx, rotation| Query::new(col_idx, Rotation(rotation.0)).into(),
        &|value| -value,
        &|lhs, rhs| lhs + rhs,
        &|lhs, rhs| lhs() * rhs(),
        &|value, scalar| value * scalar,
    )
}
