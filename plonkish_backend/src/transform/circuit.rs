use halo2_proofs::{
    arithmetic::MultiMillerLoop,
    plonk::{Circuit as ZkCircuit, ConstraintSystem as ZkConstraintSystem},
};

use crate::backend::WitnessEncoding;

#[derive(Debug)]
pub struct ZKWASMCircuit<'a, E: MultiMillerLoop, C: ZkCircuit<E::Scalar>> {
    pub circuit: &'a C,
    pub config: C::Config,
    pub cs: ZkConstraintSystem<E::Scalar>,
    pub k: u32,
    pub instances: Vec<Vec<E::Scalar>>,
    pub instances_scalar: Vec<Vec<E::Scalar>>,
    pub row_mapping: Vec<usize>,
}

pub fn get_zkwasm_circuit<D: WitnessEncoding, E: MultiMillerLoop, T>(
    k: u32,
    circuit: &[T],
    _instances: Vec<E::Scalar>,
) -> ZKWASMCircuit<E, T>
where
    T: ZkCircuit<E::Scalar>,
{
    let circuit = &circuit[0];
    let cs = ZkConstraintSystem::default();
    let (config, cs) = cs.circuit_configure::<T>();

    // Convert Gate Constraints.
    ZKWASMCircuit {
        circuit,
        config,
        cs,
        k,
        //for zkwasm
        // instances: vec![instances.clone()],
        // instances_scalar: vec![instances],
        //for zkwasm-host
        instances: vec![],
        instances_scalar: vec![],
        row_mapping: D::row_mapping(k as usize),
    }
}
