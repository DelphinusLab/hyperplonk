use crate::{
    util::{
        arithmetic::{fe_mod_from_le_bytes, Coordinates, CurveAffine, PrimeField},
        hash::{Hash, Keccak256, Output, Update},
        Itertools,
    },
    Error,
};
use halo2_proofs::pairing::bn256;
use std::{
    fmt::Debug,
    io::{self, Cursor},
};

pub mod poseidon;
mod util;

pub trait FieldTranscript<F> {
    fn squeeze_challenge(&mut self) -> F;

    fn squeeze_challenges(&mut self, n: usize) -> Vec<F> {
        (0..n).map(|_| self.squeeze_challenge()).collect()
    }

    fn common_field_element(&mut self, fe: &F) -> Result<(), Error>;

    fn common_field_elements(&mut self, fes: &[F]) -> Result<(), Error> {
        fes.iter()
            .map(|fe| self.common_field_element(fe))
            .try_collect()
    }
}

pub trait FieldTranscriptRead<F>: FieldTranscript<F> {
    fn read_field_element(&mut self) -> Result<F, Error>;

    fn read_field_elements(&mut self, n: usize) -> Result<Vec<F>, Error> {
        (0..n).map(|_| self.read_field_element()).collect()
    }
}

pub trait FieldTranscriptWrite<F>: FieldTranscript<F> {
    fn write_field_element(&mut self, fe: &F) -> Result<(), Error>;

    fn write_field_elements<'a>(
        &mut self,
        fes: impl IntoIterator<Item = &'a F>,
    ) -> Result<(), Error>
    where
        F: 'a,
    {
        for fe in fes.into_iter() {
            self.write_field_element(fe)?;
        }
        Ok(())
    }
}

pub trait Transcript<C, F>: FieldTranscript<F> {
    fn common_commitment(&mut self, comm: &C) -> Result<(), Error>;

    fn common_commitments(&mut self, comms: &[C]) -> Result<(), Error> {
        comms
            .iter()
            .map(|comm| self.common_commitment(comm))
            .try_collect()
    }
}

pub trait TranscriptRead<C, F>: Transcript<C, F> + FieldTranscriptRead<F> {
    fn read_commitment(&mut self) -> Result<C, Error>;

    fn read_commitments(&mut self, n: usize) -> Result<Vec<C>, Error> {
        (0..n).map(|_| self.read_commitment()).collect()
    }
}

pub trait TranscriptWrite<C, F>: Transcript<C, F> + FieldTranscriptWrite<F> {
    fn write_commitment(&mut self, comm: &C) -> Result<(), Error>;

    fn write_commitments<'a>(&mut self, comms: impl IntoIterator<Item = &'a C>) -> Result<(), Error>
    where
        C: 'a,
    {
        for comm in comms.into_iter() {
            self.write_commitment(comm)?;
        }
        Ok(())
    }
}

pub trait InMemoryTranscript {
    type Param: Clone + Debug;

    fn new(param: Self::Param) -> Self;

    fn into_proof(self) -> Vec<u8>;

    fn from_proof(param: Self::Param, proof: &[u8]) -> Self;
}

//Keccak256Transcript<S> 是确定了H为Kecc256的FiatShamirTranscript
pub type Keccak256Transcript<S> = FiatShamirTranscript<Keccak256, S>;

#[derive(Debug, Default)]
pub struct FiatShamirTranscript<H, S> {
    state: H,
    stream: S,
}

//如果引入了InMemoryTranscript,调用了from_proof/into_proof接口，默认就是采用了Cursor<Vec<u8>>作为S
impl<H: Hash> InMemoryTranscript for FiatShamirTranscript<H, Cursor<Vec<u8>>> {
    type Param = ();

    fn new(_: Self::Param) -> Self {
        Self::default()
    }

    fn into_proof(self) -> Vec<u8> {
        self.stream.into_inner()
    }

    fn from_proof(_: Self::Param, proof: &[u8]) -> Self {
        Self {
            state: H::default(),
            stream: Cursor::new(proof.to_vec()),
        }
    }
}

impl<H: Hash, F: PrimeField, S> FieldTranscript<F> for FiatShamirTranscript<H, S> {
    fn squeeze_challenge(&mut self) -> F {
        let hash = self.state.finalize_fixed_reset();
        self.state.update(&hash);
        fe_mod_from_le_bytes(hash)
    }

    fn common_field_element(&mut self, fe: &F) -> Result<(), Error> {
        self.state.update_field_element(fe);
        Ok(())
    }
}

impl<H: Hash, F: PrimeField, R: io::Read> FieldTranscriptRead<F> for FiatShamirTranscript<H, R> {
    fn read_field_element(&mut self) -> Result<F, Error> {
        let mut repr = <F as PrimeField>::Repr::default();
        self.stream
            .read_exact(repr.as_mut())
            .map_err(|err| Error::Transcript(err.kind(), err.to_string()))?;
        // repr.as_mut().reverse();
        let fe = F::from_repr_vartime(repr).ok_or_else(|| {
            Error::Transcript(
                io::ErrorKind::Other,
                "Invalid field element encoding in proof".to_string(),
            )
        })?;
        self.common_field_element(&fe)?;
        Ok(fe)
    }
}

impl<H: Hash, F: PrimeField, W: io::Write> FieldTranscriptWrite<F> for FiatShamirTranscript<H, W> {
    fn write_field_element(&mut self, fe: &F) -> Result<(), Error> {
        self.common_field_element(fe)?;
        let mut repr = fe.to_repr();
        // repr.as_mut().reverse();
        self.stream
            .write_all(repr.as_ref())
            .map_err(|err| Error::Transcript(err.kind(), err.to_string()))
    }
}

macro_rules! impl_fs_transcript_curve_commitment {
    ($($curve:ty),*$(,)?) => {
        $(
            impl<H: Hash, S> Transcript<$curve, <$curve as CurveAffine>::ScalarExt> for FiatShamirTranscript<H, S> {
                fn common_commitment(&mut self, comm: &$curve) -> Result<(), Error> {
                    let coordinates =
                        Option::<Coordinates<_>>::from(comm.coordinates()).ok_or_else(|| {
                            Error::Transcript(
                                io::ErrorKind::Other,
                                "Invalid elliptic curve point encoding".to_string(),
                            )
                        })?;
                    self.state.update_field_element(coordinates.x());
                    self.state.update_field_element(coordinates.y());
                    Ok(())
                }
            }

            impl<H: Hash, R: io::Read> TranscriptRead<$curve, <$curve as CurveAffine>::ScalarExt>
                for FiatShamirTranscript<H, R>
            {
                fn read_commitment(&mut self) -> Result<$curve, Error> {
                    let mut reprs = [<<$curve as CurveAffine>::Base as PrimeField>::Repr::default(); 2];
                    for repr in &mut reprs {
                        self.stream
                            .read_exact(repr.as_mut())
                            .map_err(|err| Error::Transcript(err.kind(), err.to_string()))?;
                        // repr.as_mut().reverse();
                    }
                    let [x, y] =
                        reprs.map(<<$curve as CurveAffine>::Base as PrimeField>::from_repr_vartime);
                    let ec_point = x
                        .zip(y)
                        .and_then(|(x, y)| CurveAffine::from_xy(x, y).into())
                        .ok_or_else(|| {
                            Error::Transcript(
                                io::ErrorKind::Other,
                                "Invalid elliptic curve point encoding in proof".to_string(),
                            )
                        })?;
                    self.common_commitment(&ec_point)?;
                    Ok(ec_point)
                }
            }

            impl<H: Hash, W: io::Write> TranscriptWrite<$curve, <$curve as CurveAffine>::ScalarExt>
                for FiatShamirTranscript<H, W>
            {
                fn write_commitment(&mut self, ec_point: &$curve) -> Result<(), Error> {
                    self.common_commitment(ec_point)?;
                    let coordinates = ec_point.coordinates().unwrap();
                    for coordinate in [coordinates.x(), coordinates.y()] {
                        let mut repr = coordinate.to_repr();
                        // repr.as_mut().reverse();
                        self.stream
                            .write_all(repr.as_ref())
                            .map_err(|err| Error::Transcript(err.kind(), err.to_string()))?;
                    }
                    Ok(())
                }
            }
        )*
    };
}

//这里是trait<C,F>泛型的静态分发，也就是trait也支持泛型，不同泛型对应不同trait_C_F类型,和结构体支持泛型类似，只不过这里是trait泛型
//这里实现了Transcript的bn256的泛型支持
//同时，这里实现了对所有FiatShamirTranscript<H,S>的几个Transcript的bn256的支持，同样，也包括了Keccak256Transcript<S>
impl_fs_transcript_curve_commitment!(bn256::G1Affine,);

//这里的Transcript的C是Output<Keccak256>, 和bn256::G1Affine不同
impl<F: PrimeField, S> Transcript<Output<Keccak256>, F> for Keccak256Transcript<S> {
    fn common_commitment(&mut self, comm: &Output<Keccak256>) -> Result<(), Error> {
        self.state.update(comm);
        Ok(())
    }
}

impl<F: PrimeField, R: io::Read> TranscriptRead<Output<Keccak256>, F> for Keccak256Transcript<R> {
    fn read_commitment(&mut self) -> Result<Output<Keccak256>, Error> {
        let mut hash = Output::<Keccak256>::default();
        self.stream
            .read_exact(hash.as_mut())
            .map_err(|err| Error::Transcript(err.kind(), err.to_string()))?;
        //这里没有state.update，需要手动调用common_commitment()才能更新transcript
        Ok(hash)
    }
}

impl<F: PrimeField, W: io::Write> TranscriptWrite<Output<Keccak256>, F> for Keccak256Transcript<W> {
    fn write_commitment(&mut self, hash: &Output<Keccak256>) -> Result<(), Error> {
        //这里没有state.update，需要手动调用common_commitment()才能更新transcript
        self.stream
            .write_all(hash)
            .map_err(|err| Error::Transcript(err.kind(), err.to_string()))?;
        Ok(())
    }
}
