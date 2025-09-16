use crate::util::expression::rotate::Lexical;
use crate::util::expression::Rotatable;
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
    arithmetic::MultiMillerLoop, helpers::get_witness, plonk::get_preprocess_polys_and_permutations,
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

pub fn circuit_info_without_preprocess<E: MultiMillerLoop>(
    k: usize,
    cs: &ConstraintSystem<E::Scalar>,
) -> PlonkishCircuitInfo<E::Scalar> {
    let advice_idx = advice_idx(cs);
    let constraints: Vec<Expression<E::Scalar>> = cs
        .gates
        .iter()
        .flat_map(|gate| {
            gate.polynomials()
                .iter()
                .map(|expression| convert_expression(cs, &advice_idx, expression))
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
                    let [input, table] = [input, table]
                        .map(|expression| convert_expression(cs, &advice_idx, expression));
                    (input, table)
                })
                .collect_vec()
        })
        .collect();

    // let num_instances = instances.iter().map(Vec::len).collect_vec();
    let preprocess_polys =
        vec![vec![E::Scalar::zero(); 1 << k]; cs.num_selectors + cs.num_fixed_columns];
    PlonkishCircuitInfo {
        k,
        num_instances: cs.num_instance_columns,
        preprocess_polys,
        //TODO: remove vector witnesses, keep one
        num_witness_polys: cs.num_advice_columns,
        named_witnesses: cs.named_advices.clone(),
        //for one phase halo2, challenge is not needed
        // num_challenges: vec![0],
        constraints,
        lookups,
        permutations: vec![],
        max_degree: Some(cs.degree()),
    }
}

pub fn get_circuit_info<E: MultiMillerLoop, T: Circuit<E::Scalar>>(
    k: u32,
    circuit: &T,
    // row_mapping:&Vec<usize>
) -> Result<PlonkishCircuitInfo<E::Scalar>, crate::Error> {
    let cs = ConstraintSystem::default();
    let (_, cs) = cs.circuit_configure::<T>();

    let mut circuit_info = circuit_info_without_preprocess::<E>(k as usize, &cs);
    let column_idx = column_idx(&cs);
    //get the permutation's global column index from respective column index in halo2
    let permutation_column_idx = cs
        .permutation
        .get_columns()
        .iter()
        .map(|column| {
            let key = (*column.column_type(), column.index());
            (key, column_idx[&key])
        })
        .collect();

    let (fixed, permutation) = get_preprocess_polys_and_permutations::<E::G1Affine, T>(
        k,
        &Lexical::new(k as usize).usable_indices(),
        permutation_column_idx,
        circuit,
        // config,
    )
    .map_err(|e| {
        crate::Error::InvalidSnark(format!(
            "Preprocess: error in halo2-gpu-specific Synthesis: {:?}",
            e
        ))
    })?;

    circuit_info.preprocess_polys = fixed.into_iter().map(|poly| poly.values).collect();
    circuit_info.permutations = permutation;
    println!("circuit_info={:?}",circuit_info);
    Ok(circuit_info)
}

impl<'a, E: MultiMillerLoop, C: Circuit<E::Scalar>> PlonkishCircuit<E::Scalar>
    for ZKWASMCircuit<'a, E, C>
{
    fn circuit_info(&self) -> Result<PlonkishCircuitInfo<E::Scalar>, crate::Error> {
        let Self {
            k,
            config,
            circuit,
            row_mapping,
            cs,
            ..
        } = self;
        let mut circuit_info = circuit_info_without_preprocess::<E>(*k as usize, cs);
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
            // config,
        )
        .map_err(|e| {
            crate::Error::InvalidSnark(format!(
                "Preprocess: error in halo2-gpu-specific Synthesis: {:?}",
                e
            ))
        })?;

        circuit_info.preprocess_polys = fixed.into_iter().map(|poly| poly.values).collect();
        //cycle(column,row), the column is global index
        circuit_info.permutations = permutation;
        Ok(circuit_info)
    }

    fn instances(&self) -> &[Vec<E::Scalar>] {
        &self.instances
    }

    fn synthesize(&self) -> Result<Vec<Vec<E::Scalar>>, crate::Error> {
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

fn get_advice_offset<F: Field>(cs: &ConstraintSystem<F>) -> usize {
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

fn convert_expression<F: Field>(
    cs: &ConstraintSystem<F>,
    advice_idx: &[usize],
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
