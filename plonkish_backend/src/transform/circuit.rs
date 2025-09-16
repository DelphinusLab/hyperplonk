use crate::backend::WitnessEncoding;
use crate::util::expression::rotate::{Lexical, Rotatable};
use halo2_proofs::{
    arithmetic::MultiMillerLoop,
    plonk::{Circuit, ConstraintSystem},
};

#[derive(Debug)]
pub struct ZKWASMCircuit<'a, E: MultiMillerLoop, C: Circuit<E::Scalar>> {
    pub circuit: &'a C,
    pub config: C::Config,
    pub cs: ConstraintSystem<E::Scalar>,
    pub k: u32,
    pub instances: Vec<Vec<E::Scalar>>,
    pub instances_scalar: Vec<Vec<E::Scalar>>,
    pub row_mapping: Vec<usize>,
}


pub fn get_zkwasm_circuit<E: MultiMillerLoop, T>(
    k: u32,
    circuit: &T,
    instances: Vec<Vec<E::Scalar>>,
) -> ZKWASMCircuit<E, T>
where
    T: Circuit<E::Scalar>,
{
    let cs = ConstraintSystem::default();
    let (config, cs) = cs.circuit_configure::<T>();
    // let (instances, instances_scalar) = if instances.len() > 0 {
    //     (vec![instances.clone()], vec![instances])
    // } else {
    //     (vec![], vec![])
    // };

    // Convert Gate Constraints.
    ZKWASMCircuit {
        circuit,
        config,
        cs,
        k,
        instances:instances.clone(),
        instances_scalar:instances,
        row_mapping: Lexical::new(k as usize).usable_indices(),
    }
}
