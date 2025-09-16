use crate::{
    pcs::EvaluationForShift,
    piop::sum_check::{
        classic::{ClassicSumCheck, EvaluationsProver},
        evaluate, lagrange_eval, SumCheck,
    },
    poly::multilinear::rotation_eval_points,
    util::{
        arithmetic::{inner_product, PrimeField},
        expression::{
            rotate::{Lexical, Rotatable},
            Expression, Query, Rotation,
        },
        transcript::FieldTranscriptRead,
        Itertools,
    },
    Error,
};
use std::collections::{BTreeMap, BTreeSet, HashMap};

#[allow(clippy::type_complexity)]
pub(super) fn verify_zero_check<F: PrimeField>(
    num_vars: usize,
    expression: &Expression<F>,
    instances: &[Vec<F>],
    challenges: &[F],
    y: &[F],
    transcript: &mut impl FieldTranscriptRead<F>,
) -> Result<(Vec<Vec<F>>, Vec<EvaluationForShift<F>>), Error> {
    verify_sum_check(
        num_vars,
        expression,
        F::zero(),
        instances,
        challenges,
        y,
        transcript,
    )
}

#[allow(clippy::type_complexity)]
pub(crate) fn verify_sum_check<F: PrimeField>(
    num_vars: usize,
    expression: &Expression<F>,
    sum: F,
    instances: &[Vec<F>],
    challenges: &[F],
    y: &[F],
    transcript: &mut impl FieldTranscriptRead<F>,
) -> Result<(Vec<Vec<F>>, Vec<EvaluationForShift<F>>), Error> {
    let (x_eval, x) = ClassicSumCheck::<EvaluationsProver<_>, Lexical>::verify(
        &(),
        num_vars,
        expression.degree(),
        sum,
        transcript,
    )?;

    let pcs_query = pcs_query(expression, instances.len());

    let evals = pcs_query
        .iter()
        .map(|query| {
            let eval = transcript.read_field_elements(1).unwrap();
            (*query, eval[0])
        })
        .collect_vec();

    let evals: BTreeMap<Query, F> =
        instance_evals::<_, Lexical>(num_vars, expression, instances, &x)
            .into_iter()
            .chain(evals)
            .collect();
    if evaluate::<F, Lexical>(expression, num_vars, &evals, challenges, &[y], &x) != x_eval {
        return Err(Error::InvalidSnark(
            "Unmatched between sum_check output and query evaluation".to_string(),
        ));
    }

    let evals = pcs_query
        .iter()
        .map(|query| EvaluationForShift::new(query.poly(), query.rotation(), evals[query]))
        .collect_vec();

    Ok((vec![x], evals))
}

//TODO how about take rotated poly way instead of rotate eval point here?
pub(crate) fn instance_evals<F: PrimeField, R: Rotatable + From<usize>>(
    num_vars: usize,
    expression: &Expression<F>,
    instances: &[Vec<F>],
    x: &[F],
) -> Vec<(Query, F)> {
    let mut instance_query = expression.used_query();
    instance_query.retain(|query| query.poly() < instances.len());

    let (min_rotation, max_rotation) = instance_query.iter().fold((0, 0), |(min, max), query| {
        (min.min(query.rotation().0), max.max(query.rotation().0))
    });
    let lagrange_evals = {
        let rotatable = R::from(num_vars);
        let max_instance_len = instances.iter().map(Vec::len).max().unwrap_or_default();
        (-max_rotation..max_instance_len as i32 + min_rotation.abs())
            .map(|i| lagrange_eval(x, rotatable.nth(i)))
            .collect_vec()
    };

    instance_query
        .into_iter()
        .map(|query| {
            //here just poly*rotated x,
            //in general,it rotate poly,rotation>0, left rotate poly, rotation<0, right rotate poly
            //here just fix poly, rotate x points,if rotation>0,
            let offset = (max_rotation - query.rotation().0) as usize;
            let eval = inner_product(
                &instances[query.poly()],
                &lagrange_evals[offset..offset + instances[query.poly()].len()],
            );
            (query, eval)
        })
        .collect()
}

pub fn pcs_query<F: PrimeField>(
    expression: &Expression<F>,
    num_instance_poly: usize,
) -> BTreeSet<Query> {
    let mut used_query = expression.used_query();
    used_query.retain(|query| query.poly() >= num_instance_poly);
    used_query
}

#[allow(dead_code)]
pub(super) fn points<F: PrimeField>(pcs_query: &BTreeSet<Query>, x: &[F]) -> Vec<Vec<F>> {
    pcs_query
        .iter()
        .map(Query::rotation)
        .collect::<BTreeSet<_>>()
        .into_iter()
        .flat_map(|rotation| rotation_eval_points(x, rotation))
        .collect_vec()
}

#[allow(dead_code)]
pub(crate) fn point_offset(pcs_query: &BTreeSet<Query>) -> HashMap<Rotation, usize> {
    let rotations = pcs_query
        .iter()
        .map(Query::rotation)
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect_vec();
    rotations.windows(2).fold(
        HashMap::from_iter([(rotations[0], 0)]),
        |mut point_offset, rotations| {
            let last_rotation = rotations[0];
            let offset = point_offset[&last_rotation] + (1 << last_rotation.distance());
            point_offset.insert(rotations[1], offset);
            point_offset
        },
    )
}
