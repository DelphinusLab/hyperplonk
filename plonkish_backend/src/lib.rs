#![allow(clippy::op_ref)]

// pub mod accumulation;
pub mod backend;
pub mod frontend;
pub mod pcs;
pub mod piop;
pub mod poly;
pub mod transform;
pub mod util;

#[derive(Clone, Debug, PartialEq)]
pub enum Error {
    InvalidSumcheck(String),
    InvalidPcsParam(String),
    InvalidPcsOpen(String),
    InvalidSnark(String),
    Serialization(String),
    Transcript(std::io::ErrorKind, String),
    NotImplemented(String),
    InternalError(String),
    InvalidRotation(String),
    InvalidQuotient(String),
    InvalidInput(String),
}

use halo2_proofs::plonk::Error as Halo2Error;
pub trait IntoHalo2Error<T> {
    fn into_error_halo2(self) -> Result<T, Halo2Error>;
}

impl<T> IntoHalo2Error<T> for Result<T, Error> {
    fn into_error_halo2(self) -> Result<T, Halo2Error> {
        self.map_err(|err| match err {
            Error::InvalidSumcheck(s) => Halo2Error::Other(format!("InvalidSumcheck: {}", s)),
            Error::InvalidPcsParam(s) => Halo2Error::Other(format!("InvalidPcsParam: {}", s)),
            Error::InvalidPcsOpen(s) => Halo2Error::Other(format!("InvalidPcsOpen: {}", s)),
            Error::InvalidSnark(s) => Halo2Error::Other(format!("InvalidSnark: {}", s)),
            Error::Serialization(s) => Halo2Error::Other(format!("Serialization: {}", s)),
            Error::NotImplemented(s) => Halo2Error::Other(format!("NotImplemented: {}", s)),
            Error::InternalError(s) => Halo2Error::Other(format!("InternalError: {}", s)),
            Error::InvalidRotation(s) => Halo2Error::Other(format!("InvalidRotation: {}", s)),
            Error::InvalidQuotient(s) => Halo2Error::Other(format!("InvalidQuotient: {}", s)),
            Error::InvalidInput(s) => Halo2Error::Other(format!("InvalidInput: {}", s)),

            Error::Transcript(e, _s) => {
                Halo2Error::Other(format!("InvalidSumcheckTranscript: {}", e))
            }
        })
    }
}
