use crate::{
    poly::multilinear::MultilinearPolynomial,
    util::{arithmetic::Field, end_timer, izip, parallel::parallelize, start_timer, Itertools},
    Error,
};

// mod gemini;
// mod hyrax;
// mod ipa;
mod kzg;
mod zeromorph;

// pub use gemini::Gemini;
// pub use hyrax::{MultilinearHyrax, MultilinearHyraxCommitment, MultilinearHyraxParam};
// pub use ipa::{MultilinearIpa, MultilinearIpaCommitment, MultilinearIpaParam};
pub use kzg::{
    MultilinearKzg, MultilinearKzgCommitment, MultilinearKzgParam, MultilinearKzgProverParam,
    MultilinearKzgVerifierParam,
};
pub use zeromorph::{Zeromorph, ZeromorphKzgProverParam, ZeromorphKzgVerifierParam};

fn validate_input<'a, F: Field>(
    function: &str,
    param_num_vars: usize,
    polys: impl IntoIterator<Item = &'a MultilinearPolynomial<F>>,
    points: impl IntoIterator<Item = &'a Vec<F>>,
) -> Result<(), Error> {
    let polys = polys.into_iter().collect_vec();
    let points = points.into_iter().collect_vec();
    for poly in polys.iter() {
        if param_num_vars < poly.num_vars() {
            return Err(err_too_many_variates(
                function,
                param_num_vars,
                poly.num_vars(),
            ));
        }
    }
    let input_num_vars = polys
        .iter()
        .map(|poly| poly.num_vars())
        .chain(points.iter().map(|point| point.len()))
        .next()
        .expect("To have at least 1 poly or point");
    for point in points.into_iter() {
        if point.len() != input_num_vars {
            return Err(Error::InvalidPcsParam(format!(
                "Invalid point (expect point to have {input_num_vars} variates but got {})",
                point.len()
            )));
        }
    }
    Ok(())
}

fn err_too_many_variates(function: &str, upto: usize, got: usize) -> Error {
    Error::InvalidPcsParam(if function == "trim" {
        format!(
            "Too many variates to {function} (param supports variates up to {upto} but got {got})"
        )
    } else {
        format!(
            "Too many variates of poly to {function} (param supports variates up to {upto} but got {got})"
        )
    })
}

fn quotients<F: Field, T>(
    poly: &MultilinearPolynomial<F>,
    point: &[F],
    f: impl Fn(usize, Vec<F>) -> T,
) -> (Vec<T>, F) {
    assert_eq!(poly.num_vars(), point.len());

    let mut remainder = poly.evals().to_vec();
    let mut quotients = point
        .iter()
        .zip(0..poly.num_vars())
        .rev()
        .map(|(x_i, num_vars)| {
            let timer = start_timer(|| "quotients");
            // here modification will change remainder value
            let (remaimder_lo, remainder_hi) = remainder.split_at_mut(1 << num_vars);
            let mut quotient = vec![F::zero(); remaimder_lo.len()];

            parallelize(&mut quotient, |(quotient, start)| {
                izip!(quotient, &remaimder_lo[start..], &remainder_hi[start..])
                    .for_each(|(q, r_lo, r_hi)| *q = *r_hi - r_lo);
            });
            parallelize(remaimder_lo, |(remaimder_lo, start)| {
                izip!(remaimder_lo, &remainder_hi[start..])
                    .for_each(|(r_lo, r_hi)| *r_lo += (*r_hi - r_lo as &_) * x_i);
            });

            remainder.truncate(1 << num_vars);
            end_timer(timer);

            f(num_vars, quotient)
        })
        .collect_vec();
    quotients.reverse();

    (quotients, remainder[0])
}

mod additive {
    use crate::{
        pcs::{
            multilinear::validate_input, Additive, Evaluation, EvaluationForShift, Point,
            PolynomialCommitmentScheme,
        },
        piop::sum_check::{
            classic::{ClassicSumCheck, CoefficientsProver},
            eq_xy_eval, SumCheck as _, VirtualPolynomial,
        },
        poly::multilinear::MultilinearPolynomial,
        util::{
            arithmetic::{fe_to_bytes, inner_product, PrimeField},
            end_timer,
            expression::{Expression, Query, Rotation},
            start_timer,
            transcript::{TranscriptRead, TranscriptWrite},
            Itertools,
        },
        Error,
    };
    use std::{borrow::Cow, collections::HashMap, ops::Deref, ptr::addr_of};

    type SumCheck<F> = ClassicSumCheck<CoefficientsProver<F>>;

    pub fn batch_open<F, Pcs>(
        pp: &Pcs::ProverParam,
        num_vars: usize,
        polys: Vec<&Pcs::Polynomial>,
        comms: Vec<&Pcs::Commitment>,
        points: &[Point<F, Pcs::Polynomial>],
        evals: &[Evaluation<F>],
        transcript: &mut impl TranscriptWrite<Pcs::CommitmentChunk, F>,
    ) -> Result<(), Error>
    where
        F: PrimeField,
        Pcs: PolynomialCommitmentScheme<F, Polynomial = MultilinearPolynomial<F>>,
        Pcs::Commitment: Additive<F>,
    {
        validate_input("batch open", num_vars, polys.clone(), points)?;

        if cfg!(feature = "sanity-check") {
            assert_eq!(
                points
                    .iter()
                    .map(|point| point.iter().map(fe_to_bytes::<F>).collect_vec())
                    .unique()
                    .count(),
                points.len()
            );
            for eval in evals.iter() {
                let (poly, point) = (&polys[eval.poly()], &points[eval.point()]);
                assert_eq!(poly.evaluate(point), *eval.value());
            }
        }

        let ell = evals.len().next_power_of_two().ilog2() as usize;
        let t = transcript.squeeze_challenges(ell);

        let timer = start_timer(|| "merged_polys");
        let eq_xt = MultilinearPolynomial::eq_xy(&t);
        let merged_polys = evals.iter().zip(eq_xt.evals().iter()).fold(
            vec![(F::one(), Cow::<MultilinearPolynomial<_>>::default()); points.len()],
            |mut merged_polys, (eval, eq_xt_i)| {
                if merged_polys[eval.point()].1.is_empty() {
                    merged_polys[eval.point()] = (*eq_xt_i, Cow::Borrowed(polys[eval.poly()]));
                } else {
                    let coeff = merged_polys[eval.point()].0;
                    if coeff != F::one() {
                        merged_polys[eval.point()].0 = F::one();
                        *merged_polys[eval.point()].1.to_mut() *= &coeff;
                    }
                    *merged_polys[eval.point()].1.to_mut() += (eq_xt_i, polys[eval.poly()]);
                }
                merged_polys
            },
        );
        end_timer(timer);

        let unique_merged_polys = merged_polys
            .iter()
            .unique_by(|(_, poly)| addr_of!(*poly.deref()))
            .collect_vec();
        let unique_merged_poly_indices = unique_merged_polys
            .iter()
            .enumerate()
            .map(|(idx, (_, poly))| (addr_of!(*poly.deref()), idx))
            .collect::<HashMap<_, _>>();
        let expression = merged_polys
            .iter()
            .enumerate()
            .map(|(idx, (scalar, poly))| {
                let poly = unique_merged_poly_indices[&addr_of!(*poly.deref())];
                Expression::<F>::eq_xy(idx)
                    * Expression::Polynomial(Query::new(poly, Rotation::cur()))
                    * scalar
            })
            .sum();
        let virtual_poly = VirtualPolynomial::new(
            &expression,
            unique_merged_polys.iter().map(|(_, poly)| poly.deref()),
            &[],
            points,
        );
        let tilde_gs_sum =
            inner_product(evals.iter().map(Evaluation::value), &eq_xt[..evals.len()]);
        let (g_prime_eval, challenges, _) =
            SumCheck::prove(&(), num_vars, virtual_poly, tilde_gs_sum, transcript)?;

        let timer = start_timer(|| "g_prime");
        let eq_xy_evals = points
            .iter()
            .map(|point| eq_xy_eval(&challenges, point))
            .collect_vec();
        let g_prime = merged_polys
            .into_iter()
            .zip(eq_xy_evals.iter())
            .map(|((scalar, poly), eq_xy_eval)| (scalar * eq_xy_eval, poly.into_owned()))
            .sum::<MultilinearPolynomial<_>>();
        end_timer(timer);

        let g_prime_comm = if cfg!(feature = "sanity-check") {
            let scalars = evals
                .iter()
                .zip(eq_xt.evals())
                .map(|(eval, eq_xt_i)| eq_xy_evals[eval.point()] * eq_xt_i)
                .collect_vec();
            let bases = evals.iter().map(|eval| comms[eval.poly()]);
            Pcs::Commitment::msm(&scalars, bases)
        } else {
            Pcs::Commitment::default()
        };
        Pcs::open(
            pp,
            &g_prime,
            &g_prime_comm,
            &challenges,
            &g_prime_eval,
            transcript,
        )
    }

    // merge all rotated polys to one and commit in advance.
    // un-rotated poly add the merged rotated poly directly.
    pub fn batch_open_for_shift<F, Pcs>(
        pp: &Pcs::ProverParam,
        num_vars: usize,
        polys: Vec<&Pcs::Polynomial>,
        comms: Vec<&Pcs::Commitment>,
        points: &[Point<F, Pcs::Polynomial>],
        evals: &[EvaluationForShift<F>],
        transcript: &mut impl TranscriptWrite<Pcs::CommitmentChunk, F>,
    ) -> Result<(), Error>
    where
        F: PrimeField,
        Pcs: PolynomialCommitmentScheme<F, Polynomial = MultilinearPolynomial<F>>,
        Pcs::Commitment: Additive<F>,
    {
        // validate poly and point
        validate_input("batch open", num_vars, polys.clone(), points)?;

        if cfg!(feature = "sanity-check") {
            assert_eq!(
                points
                    .iter()
                    .map(|point| point.iter().map(fe_to_bytes::<F>).collect_vec())
                    .unique()
                    .count(),
                points.len()
            );
            for eval in evals {
                assert_eq!(
                    polys[eval.poly()].evaluate_for_rotation(&points[0], eval.rotation())[0],
                    *eval.value()
                );
            }
        }

        //  merge Rotation::cur() and not Rotation::cur() evaluations ---
        let ell = evals.len().next_power_of_two().ilog2() as usize;
        let t = transcript.squeeze_challenges(ell);

        let eq_xt = MultilinearPolynomial::eq_xy(&t);

        let evals_cur = evals
            .iter()
            .filter(|eval| eval.rotation() == Rotation::cur())
            .collect_vec();

        let evals_rotate = evals
            .iter()
            .filter(|eval| eval.rotation() != Rotation::cur())
            .collect_vec();

        // merge all rotated polys, not limited to identical rotated polys
        let rotate_polys = evals_rotate
            .iter()
            .map(|eval| {
                // Use the i32 value to check the sign, and distance() for magnitude
                let signed_d = eval.rotation().0;
                let abs_d = eval.rotation().distance(); // Get magnitude (usize)
                let mut poly_d_evals = polys[eval.poly()].evals().to_vec();
                //notice: just rotate the poly but not the eval point
                // the eval points are same to rotated poly and non-rotated poly.
                if signed_d > 0 {
                    poly_d_evals.rotate_left(abs_d);
                } else {
                    poly_d_evals.rotate_right(abs_d);
                }
                MultilinearPolynomial::new(poly_d_evals)
            })
            .collect_vec();

        let merged_polys_fn =
            |evals: &[&EvaluationForShift<F>], eq_xt: &[F]| -> (F, Cow<MultilinearPolynomial<F>>) {
                evals.iter().zip(eq_xt.iter()).enumerate().fold(
                    (F::one(), Cow::<MultilinearPolynomial<_>>::default()),
                    |mut merged_polys, (i, (&eval, eq_xt_i))| {
                        let poly_ref = if eval.rotation != Rotation::cur() {
                            &rotate_polys[i]
                        } else {
                            polys[eval.poly()]
                        };
                        if merged_polys.1.is_empty() {
                            merged_polys = (*eq_xt_i, Cow::Borrowed(poly_ref));
                        } else {
                            let coeff = merged_polys.0;
                            if coeff != F::one() {
                                merged_polys.0 = F::one();
                                *merged_polys.1.to_mut() *= &coeff;
                            }
                            // Ensure the polynomial being added has the correct number of variables
                            assert_eq!(
                                merged_polys.1.num_vars(),
                                poly_ref.num_vars(),
                                "Mismatched num_vars in merging"
                            );
                            *merged_polys.1.to_mut() += (*eq_xt_i, poly_ref);
                        }
                        merged_polys
                    },
                )
            };
        //TODO test no rotate case  and all rotate case
        let mut merged_polys_rotate = merged_polys_fn(&evals_rotate, &eq_xt[evals_cur.len()..]);
        if merged_polys_rotate.0 != F::one() {
            *merged_polys_rotate.1.to_mut() *= &merged_polys_rotate.0;
            merged_polys_rotate.0 = F::one();
        }

        let merged_evals_rotate = inner_product(
            evals_rotate.iter().map(|eval| eval.value()),
            &eq_xt[evals_cur.len()..evals.len()],
        );

        let rotate_polys_comms = Pcs::commit_and_write(pp, &merged_polys_rotate.1, transcript)?;
        if cfg!(feature = "sanity-check") {
            if evals_rotate.len() > 0 {
                assert_eq!(
                    merged_polys_rotate.1.evaluate(&points[0]),
                    merged_evals_rotate
                );
            }
        }
        let mut merged_polys_cur = merged_polys_fn(&evals_cur, &eq_xt.evals());
        if merged_polys_cur.0 != F::one() {
            *merged_polys_cur.1.to_mut() *= &merged_polys_cur.0;
            merged_polys_cur.0 = F::one();
        }
        *merged_polys_cur.1.to_mut() += merged_polys_rotate;

        let tilde_gs_sum_cur = inner_product(
            evals_cur.iter().map(|eval| eval.value()),
            &eq_xt[..evals_cur.len()],
        );
        let tilde_gs_sum_cur = tilde_gs_sum_cur + merged_evals_rotate;
        if cfg!(feature = "sanity-check") {
            assert_eq!(merged_polys_cur.1.evaluate(&points[0]), tilde_gs_sum_cur);
        }

        let commitment_cur = if cfg!(feature = "sanity-check") {
            let mut scalars = eq_xt.evals()[..evals_cur.len()].to_vec();
            scalars.push(F::one()); //scalar for rotate_polys_comms

            let mut bases = evals_cur
                .iter()
                .map(|eval| comms[eval.poly()])
                .collect_vec();
            bases.push(&rotate_polys_comms);

            Pcs::Commitment::msm(&scalars, bases)
        } else {
            Pcs::Commitment::default()
        };
        Pcs::open(
            pp,
            &merged_polys_cur.1,
            &commitment_cur,
            &points[0],
            &tilde_gs_sum_cur,
            transcript,
        )?;

        Ok(())
    }

    // merge all rotated polys to one and commit in advance.
    pub fn batch_verify_for_shift<F, Pcs>(
        vp: &Pcs::VerifierParam,
        num_vars: usize,
        comms: Vec<&Pcs::Commitment>,
        points: &[Point<F, Pcs::Polynomial>],
        evals: &[EvaluationForShift<F>],
        transcript: &mut impl TranscriptRead<Pcs::CommitmentChunk, F>,
    ) -> Result<(), Error>
    where
        F: PrimeField,
        Pcs: PolynomialCommitmentScheme<F, Polynomial = MultilinearPolynomial<F>>,
        Pcs::Commitment: Additive<F>,
    {
        validate_input("batch verify", num_vars, [], points)?;

        let ell = evals.len().next_power_of_two().ilog2() as usize;
        let t = transcript.squeeze_challenges(ell);

        //read rotate poly's commits
        let rotate_polys_comm = Pcs::read_commitment(vp, transcript)?;

        let eq_xt = MultilinearPolynomial::eq_xy(&t);

        let evals_cur = evals
            .iter()
            .filter(|eval| eval.rotation() == Rotation::cur())
            .collect_vec();

        let tilde_gs_sum = inner_product(
            evals_cur.iter().map(|eval| eval.value()),
            &eq_xt[..evals_cur.len()],
        );

        let evals_rotate = evals
            .iter()
            .filter(|eval| eval.rotation() != Rotation::cur())
            .collect_vec();

        let rotate_evals_sum = inner_product(
            evals_rotate.iter().map(|eval| eval.value()),
            &eq_xt[evals_cur.len()..evals.len()],
        );
        let tilde_gs_sum = tilde_gs_sum + rotate_evals_sum;
        let commitment_cur = {
            let mut scalars = eq_xt.evals()[..evals_cur.len()].to_vec();
            //rotate_polys_comm has already multiplied ex_xts, here set scalar to 1
            scalars.push(F::one());

            let bases = evals_cur
                .iter()
                .map(|eval| comms[eval.poly()])
                .chain(std::iter::once(&rotate_polys_comm))
                .collect::<Vec<_>>();
            Pcs::Commitment::msm(&scalars, bases)
        };
        Pcs::verify(vp, &commitment_cur, &points[0], &tilde_gs_sum, transcript)
    }

    pub fn batch_verify<F, Pcs>(
        vp: &Pcs::VerifierParam,
        num_vars: usize,
        comms: Vec<&Pcs::Commitment>,
        points: &[Point<F, Pcs::Polynomial>],
        evals: &[Evaluation<F>],
        transcript: &mut impl TranscriptRead<Pcs::CommitmentChunk, F>,
    ) -> Result<(), Error>
    where
        F: PrimeField,
        Pcs: PolynomialCommitmentScheme<F, Polynomial = MultilinearPolynomial<F>>,
        Pcs::Commitment: Additive<F>,
    {
        validate_input("batch verify", num_vars, [], points)?;

        let ell = evals.len().next_power_of_two().ilog2() as usize;
        let t = transcript.squeeze_challenges(ell);

        let eq_xt = MultilinearPolynomial::eq_xy(&t);
        let tilde_gs_sum =
            inner_product(evals.iter().map(Evaluation::value), &eq_xt[..evals.len()]);
        let (g_prime_eval, challenges) =
            SumCheck::verify(&(), num_vars, 2, tilde_gs_sum, transcript)?;

        let eq_xy_evals = points
            .iter()
            .map(|point| eq_xy_eval(&challenges, point))
            .collect_vec();
        let g_prime_comm = {
            let scalars = evals
                .iter()
                .zip(eq_xt.evals())
                .map(|(eval, eq_xt_i)| eq_xy_evals[eval.point()] * eq_xt_i)
                .collect_vec();
            let bases = evals.iter().map(|eval| comms[eval.poly()]);
            Pcs::Commitment::msm(&scalars, bases)
        };
        Pcs::verify(vp, &g_prime_comm, &challenges, &g_prime_eval, transcript)
    }
}
