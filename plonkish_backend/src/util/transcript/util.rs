use halo2_proofs::arithmetic::BaseExt;
use num_bigint::BigUint;
use halo2_proofs::arithmetic::CurveAffine;
use halo2_proofs::arithmetic::Field;

pub fn field_to_bn<F: BaseExt>(f: &F) -> BigUint {
    let mut bytes: Vec<u8> = Vec::with_capacity(32);
    f.write(&mut bytes).unwrap();
    BigUint::from_bytes_le(&bytes[..])
}

pub fn bn_to_field<F: BaseExt>(bn: &BigUint) -> F {
    let modulus = field_to_bn(&-F::one()) + 1u64;
    let bn = bn % &modulus;
    let mut bytes = bn.to_bytes_le();
    bytes.resize((modulus.bits() as usize + 7) / 8, 0);
    let mut bytes = &bytes[..];
    F::read(&mut bytes).unwrap()
}


pub fn encode_point<C: CurveAffine>(point: &C) -> Vec<C::Scalar> {
    let x_y: Option<_> = point.coordinates().map(|c| (*c.x(), *c.y())).into();
    let (x, y) = x_y.unwrap_or((C::Base::zero(), C::Base::zero()));

    let x = field_to_bn(&x);
    let y = field_to_bn(&y);

    let shift = BigUint::from(1u64) << 108;

    vec![
        bn_to_field(&(&x % (&shift * &shift))),
        bn_to_field(&(x / (&shift * &shift) + (&y % &shift) * &shift)),
        bn_to_field(&(y / shift)),
    ]
}