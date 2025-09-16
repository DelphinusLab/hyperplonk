use crate::util::{
    arithmetic::Field, arithmetic::FieldExt, izip, Deserialize, Itertools, Serialize,
};
use halo2_proofs::helpers::read_u32;
use halo2_proofs::helpers::Serializable;
use num;
use num::FromPrimitive;
use num_derive::FromPrimitive;
use std::{
    borrow::Borrow,
    collections::BTreeSet,
    fmt::Debug,
    io::{self, Cursor},
    iter::{self, Product, Sum},
    ops::{Add, Mul, Neg, Sub},
};

pub mod evaluator;
pub mod relaxed;
pub mod rotate;

pub use rotate::Rotatable;
pub use rotate::Rotation;

//TODO how to refactor to halo2's Query(Advice,Fix..), thus, poly will be relative index,not global idx
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct Query {
    poly: usize,
    rotation: Rotation,
}

impl Query {
    pub fn new(poly: usize, rotation: impl Into<Rotation>) -> Self {
        Self {
            poly,
            rotation: rotation.into(),
        }
    }

    pub fn poly(&self) -> usize {
        self.poly
    }

    pub fn rotation(&self) -> Rotation {
        self.rotation
    }
}

impl<T: Into<Rotation>> From<(usize, T)> for Query {
    fn from((poly, rotation): (usize, T)) -> Self {
        Self::new(poly, rotation)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub enum CommonPolynomial {
    Identity,
    Lagrange(i32),
    EqXY(usize),
}

#[derive(FromPrimitive)]
enum CommonPolynomialCode {
    Identity = 0,
    Lagrange,
    EqXY,
}

fn common_poly_code(p: &CommonPolynomial) -> CommonPolynomialCode {
    match p {
        CommonPolynomial::Identity => CommonPolynomialCode::Identity,
        CommonPolynomial::Lagrange(_) => CommonPolynomialCode::Lagrange,
        CommonPolynomial::EqXY(_) => CommonPolynomialCode::EqXY,
    }
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub enum Expression<F> {
    Constant(F),
    CommonPolynomial(CommonPolynomial),
    Polynomial(Query),
    Challenge(usize),
    Negated(Box<Expression<F>>),
    Sum(Box<Expression<F>>, Box<Expression<F>>),
    Product(Box<Expression<F>>, Box<Expression<F>>),
    Scaled(Box<Expression<F>>, F),
    DistributePowers(Vec<Expression<F>>, Box<Expression<F>>),
}

impl<F: Clone> Expression<F> {
    pub fn identity() -> Self {
        Expression::CommonPolynomial(CommonPolynomial::Identity)
    }

    pub fn lagrange(i: i32) -> Self {
        Expression::CommonPolynomial(CommonPolynomial::Lagrange(i))
    }

    pub fn eq_xy(idx: usize) -> Self {
        Expression::CommonPolynomial(CommonPolynomial::EqXY(idx))
    }

    pub fn distribute_powers(
        exprs: impl IntoIterator<Item = impl Borrow<Self>>,
        base: impl Borrow<Self>,
    ) -> Self {
        let exprs = exprs
            .into_iter()
            .map(|expr| expr.borrow().clone())
            .collect_vec();
        match exprs.len() {
            0 => unreachable!(),
            1 => exprs.into_iter().next().unwrap(),
            _ => Expression::DistributePowers(exprs, base.borrow().clone().into()),
        }
    }

    #[allow(clippy::too_many_arguments)]
    pub fn evaluate<T: Clone>(
        &self,
        constant: &impl Fn(F) -> T,
        common_poly: &impl Fn(CommonPolynomial) -> T,
        poly: &impl Fn(Query) -> T,
        challenge: &impl Fn(usize) -> T,
        negated: &impl Fn(T) -> T,
        sum: &impl Fn(T, T) -> T,
        product: &impl Fn(T, T) -> T,
        scaled: &impl Fn(T, F) -> T,
    ) -> T {
        let evaluate = |expr: &Expression<F>| {
            expr.evaluate(
                constant,
                common_poly,
                poly,
                challenge,
                negated,
                sum,
                product,
                scaled,
            )
        };
        match self {
            Expression::Constant(scalar) => constant(scalar.clone()),
            Expression::CommonPolynomial(poly) => common_poly(*poly),
            Expression::Polynomial(query) => poly(*query),
            Expression::Challenge(index) => challenge(*index),
            Expression::Negated(a) => {
                let a = evaluate(a);
                negated(a)
            }
            Expression::Sum(a, b) => {
                let a = evaluate(a);
                let b = evaluate(b);
                sum(a, b)
            }
            Expression::Product(a, b) => {
                let a = evaluate(a);
                let b = evaluate(b);
                product(a, b)
            }
            Expression::Scaled(a, scalar) => {
                let a = evaluate(a);
                scaled(a, scalar.clone())
            }
            Expression::DistributePowers(exprs, scalar) => {
                assert!(!exprs.is_empty());
                if exprs.len() == 1 {
                    return evaluate(&exprs[0]);
                }
                let scalar = evaluate(scalar);
                let scalars = iter::successors(Some(scalar.clone()), |power| {
                    Some(product(power.clone(), scalar.clone()))
                });
                izip!(&exprs[1..], scalars).fold(evaluate(&exprs[0]), |acc, (expr, scalar)| {
                    sum(acc, product(scalar, evaluate(expr)))
                })
            }
        }
    }

    pub fn degree(&self) -> usize {
        self.evaluate(
            &|_| 0,
            &|_| 1,
            &|_| 1,
            &|_| 0,
            &|a| a,
            &|a, b| a.max(b),
            &|a, b| a + b,
            &|a, _| a,
        )
    }

    pub fn used_langrange(&self) -> BTreeSet<i32> {
        self.used_primitive(
            &|poly| match poly {
                CommonPolynomial::Lagrange(i) => i.into(),
                _ => None,
            },
            &|_| None,
        )
    }

    pub fn used_query(&self) -> BTreeSet<Query> {
        self.used_primitive(&|_| None, &|query| query.into())
    }

    pub fn used_poly(&self) -> BTreeSet<usize> {
        self.used_primitive(&|_| None, &|query| query.poly().into())
    }

    pub fn used_rotation(&self) -> BTreeSet<Rotation> {
        self.used_primitive(&|_| None, &|query| query.rotation().into())
    }

    pub fn max_used_rotation_distance(&self) -> usize {
        self.used_rotation()
            .into_iter()
            .map(|rotation| rotation.0.unsigned_abs())
            .max()
            .unwrap_or_default() as usize
    }

    pub fn used_challenge(&self) -> BTreeSet<usize> {
        self.evaluate(
            &|_| None,
            &|_| None,
            &|_| None,
            &|challenge| Some(BTreeSet::from([challenge])),
            &|a| a,
            &merge_left_right,
            &merge_left_right,
            &|a, _| a,
        )
        .unwrap_or_default()
    }

    fn used_primitive<T: Clone + Ord>(
        &self,
        common_poly: &impl Fn(CommonPolynomial) -> Option<T>,
        poly: &impl Fn(Query) -> Option<T>,
    ) -> BTreeSet<T> {
        self.evaluate(
            &|_| None,
            &|poly| common_poly(poly).map(|t| BTreeSet::from([t])),
            &|query| poly(query).map(|t| BTreeSet::from([t])),
            &|_| None,
            &|a| a,
            &merge_left_right,
            &merge_left_right,
            &|a, _| a,
        )
        .unwrap_or_default()
    }

    pub fn write(&self, writer: &mut impl io::Write) -> io::Result<()>
    where
        F: Debug,
    {
        match self {
            Expression::Constant(constant) => write!(writer, "{:?}", *constant),
            Expression::CommonPolynomial(poly) => match poly {
                CommonPolynomial::Identity => write!(writer, "id"),
                CommonPolynomial::Lagrange(i) => write!(writer, "l_{i}"),
                CommonPolynomial::EqXY(idx) => write!(writer, "eq_{idx}"),
            },
            Expression::Polynomial(query) => {
                write!(writer, "p_{}_{}", query.poly(), query.rotation().0)
            }
            Expression::Challenge(challenge) => write!(writer, "c_{challenge}"),
            Expression::Negated(value) => {
                writer.write_all(b"(-")?;
                value.write(writer)?;
                writer.write_all(b")")
            }
            Expression::Sum(lhs, rhs) => {
                writer.write_all(b"(")?;
                lhs.write(writer)?;
                writer.write_all(b" + ")?;
                rhs.write(writer)?;
                writer.write_all(b")")
            }
            Expression::Product(lhs, rhs) => {
                lhs.write(writer)?;
                writer.write_all(b" * ")?;
                rhs.write(writer)
            }
            Expression::Scaled(value, scalar) => {
                write!(writer, "{:?} * ", *scalar)?;
                value.write(writer)
            }
            Expression::DistributePowers(exprs, scalar) => {
                for (expr, exp) in exprs.iter().zip((1..exprs.len()).rev()) {
                    scalar.write(writer)?;
                    write!(writer, "^{exp} * ")?;
                    expr.write(writer)?;
                    write!(writer, " + ")?;
                }
                exprs.last().unwrap().write(writer)?;
                Ok(())
            }
        }
    }

    pub fn identifier(&self) -> String
    where
        F: Debug,
    {
        let mut buf = Cursor::new(Vec::new());
        self.write(&mut buf).unwrap();
        String::from_utf8(buf.into_inner()).unwrap()
    }
}

impl<F: Clone> From<Query> for Expression<F> {
    fn from(query: Query) -> Self {
        Self::Polynomial(query)
    }
}

impl<F: Clone> From<CommonPolynomial> for Expression<F> {
    fn from(common_poly: CommonPolynomial) -> Self {
        Self::CommonPolynomial(common_poly)
    }
}

impl<F: Field> Expression<F> {
    pub fn zero() -> Self {
        Expression::Constant(F::zero())
    }

    pub fn one() -> Self {
        Expression::Constant(F::one())
    }

    pub fn simplified(&self, challenges: Option<&[F]>) -> Option<Expression<F>> {
        #[derive(Clone)]
        enum Case<F> {
            Constant(F),
            Sum(F, Expression<F>),
            Scaled(F, F, Expression<F>),
        }

        impl<F: Field> Case<F> {
            fn into_simplified(self) -> Self {
                match self {
                    Case::Scaled(scalar, constant, expression) => {
                        if scalar == F::zero() {
                            Case::Constant(F::zero())
                        } else if scalar == F::one() {
                            Case::Sum(constant, expression)
                        } else if scalar == -F::one() {
                            Case::Sum(-constant, -expression)
                        } else {
                            Case::Scaled(scalar, constant, expression)
                        }
                    }
                    rest => rest,
                }
            }

            fn into_expression(self) -> Option<Expression<F>> {
                match self {
                    Case::Constant(constant) => Some(Expression::Constant(constant)),
                    Case::Sum(constant, expression) => {
                        if constant == F::zero() {
                            Some(expression)
                        } else {
                            Some(expression + Expression::Constant(constant))
                        }
                    }
                    Case::Scaled(scalar, constant, expression) => {
                        debug_assert!(![F::zero(), F::one(), -F::one()].contains(&scalar));
                        Case::Sum(scalar * constant, expression * scalar).into_expression()
                    }
                }
            }
        }

        impl<F: Field> Add for Case<F> {
            type Output = Self;

            fn add(self, rhs: Self) -> Self::Output {
                match (self, rhs) {
                    (Case::Constant(lhs), Case::Constant(rhs)) => Case::Constant(lhs + rhs),
                    (Case::Constant(lhs), Case::Sum(rhs, expression))
                    | (Case::Sum(rhs, expression), Case::Constant(lhs)) => {
                        Case::Sum(lhs + rhs, expression)
                    }
                    (
                        Case::Sum(lhs_constant, lhs_expression),
                        Case::Sum(rhs_constant, rhs_expression),
                    ) => Case::Sum(lhs_constant + rhs_constant, lhs_expression + rhs_expression),
                    (Case::Constant(lhs), Case::Scaled(scalar, rhs, expression))
                    | (Case::Scaled(scalar, rhs, expression), Case::Constant(lhs)) => {
                        Case::Sum(lhs + scalar * rhs, expression * scalar)
                    }
                    (
                        Case::Sum(lhs_constant, lhs_expression),
                        Case::Scaled(rhs_scalar, rhs_constant, rhs_expression),
                    )
                    | (
                        Case::Scaled(rhs_scalar, rhs_constant, rhs_expression),
                        Case::Sum(lhs_constant, lhs_expression),
                    ) => {
                        let rhs_constant = rhs_scalar * rhs_constant;
                        let rhs_expression = rhs_expression * rhs_scalar;
                        Case::Sum(lhs_constant + rhs_constant, lhs_expression + rhs_expression)
                    }
                    (
                        Case::Scaled(lhs_scalar, lhs_constant, lhs_expression),
                        Case::Scaled(rhs_scalar, rhs_constant, rhs_expression),
                    ) => {
                        let lhs_constant = lhs_scalar * lhs_constant;
                        let lhs_expression = lhs_expression * lhs_scalar;
                        let rhs_constant = rhs_scalar * rhs_constant;
                        let rhs_expression = rhs_expression * rhs_scalar;
                        Case::Sum(lhs_constant + rhs_constant, lhs_expression + rhs_expression)
                    }
                }
            }
        }

        impl<F: Field> Neg for Case<F> {
            type Output = Self;

            fn neg(self) -> Self::Output {
                match self {
                    Case::Constant(constant) => Case::Constant(-constant),
                    Case::Sum(constant, expression) => Case::Sum(-constant, -expression),
                    Case::Scaled(scalar, constant, expression) => {
                        Case::Scaled(-scalar, constant, expression)
                    }
                }
                .into_simplified()
            }
        }

        impl<F: Field> Mul for Case<F> {
            type Output = Self;

            fn mul(self, rhs: Self) -> Self::Output {
                match (self, rhs) {
                    (Case::Constant(lhs), Case::Constant(rhs)) => Case::Constant(lhs * rhs),
                    (Case::Constant(scalar), Case::Sum(constant, expression))
                    | (Case::Sum(constant, expression), Case::Constant(scalar)) => {
                        Case::Scaled(scalar, constant, expression)
                    }
                    (Case::Constant(lhs), Case::Scaled(rhs, constant, expression))
                    | (Case::Scaled(rhs, constant, expression), Case::Constant(lhs)) => {
                        Case::Scaled(lhs * rhs, constant, expression)
                    }
                    (lhs, rhs) => match (lhs.into_expression(), rhs.into_expression()) {
                        (Some(lhs), Some(rhs)) => Case::Sum(F::zero(), lhs * rhs),
                        (Some(expression), None) | (None, Some(expression)) => {
                            Case::Sum(F::zero(), expression)
                        }
                        (None, None) => Case::Constant(F::zero()),
                    },
                }
                .into_simplified()
            }
        }

        impl<F: Field> Mul<F> for Case<F> {
            type Output = Self;

            fn mul(self, rhs: F) -> Self::Output {
                match self {
                    Case::Constant(lhs) => Case::Constant(lhs * rhs),
                    Case::Sum(constant, expression) => Case::Scaled(rhs, constant, expression),
                    Case::Scaled(lhs, constant, expression) => {
                        Case::Scaled(lhs * rhs, constant, expression)
                    }
                }
                .into_simplified()
            }
        }

        self.evaluate(
            &|constant| Case::Constant(constant),
            &|poly| Case::Sum(F::zero(), poly.into()),
            &|query| Case::Sum(F::zero(), query.into()),
            &|challenge| {
                challenges
                    .map(|challenges| Case::Constant(challenges[challenge]))
                    .unwrap_or_else(|| Case::Sum(F::zero(), Expression::Challenge(challenge)))
            },
            &|case| -case,
            &|lhs, rhs| lhs + rhs,
            &|lhs, rhs| lhs * rhs,
            &|lhs, rhs| lhs * rhs,
        )
        .into_expression()
    }
}

macro_rules! impl_expression_ops {
    ($trait:ident, $op:ident, $variant:ident, $rhs:ty, $rhs_expr:expr) => {
        impl<F: Clone> $trait<$rhs> for Expression<F> {
            type Output = Expression<F>;
            fn $op(self, rhs: $rhs) -> Self::Output {
                Expression::$variant((self).into(), $rhs_expr(rhs).into())
            }
        }
        impl<F: Clone> $trait<$rhs> for &Expression<F> {
            type Output = Expression<F>;
            fn $op(self, rhs: $rhs) -> Self::Output {
                Expression::$variant((self.clone()).into(), $rhs_expr(rhs).into())
            }
        }
        impl<F: Clone> $trait<&$rhs> for Expression<F> {
            type Output = Expression<F>;
            fn $op(self, rhs: &$rhs) -> Self::Output {
                Expression::$variant((self).into(), $rhs_expr(rhs.clone()).into())
            }
        }
        impl<F: Clone> $trait<&$rhs> for &Expression<F> {
            type Output = Expression<F>;
            fn $op(self, rhs: &$rhs) -> Self::Output {
                Expression::$variant((self.clone()).into(), $rhs_expr(rhs.clone()).into())
            }
        }
    };
}

impl_expression_ops!(Mul, mul, Product, Expression<F>, std::convert::identity);
impl_expression_ops!(Mul, mul, Scaled, F, std::convert::identity);
impl_expression_ops!(Add, add, Sum, Expression<F>, std::convert::identity);
impl_expression_ops!(Sub, sub, Sum, Expression<F>, Neg::neg);

impl<F: Clone> Neg for Expression<F> {
    type Output = Expression<F>;
    fn neg(self) -> Self::Output {
        -&self
    }
}

impl<F: Clone> Neg for &Expression<F> {
    type Output = Expression<F>;
    fn neg(self) -> Self::Output {
        Expression::Negated(Box::new(self.clone()))
    }
}

impl<'a, F: Field> Sum<&'a Expression<F>> for Expression<F> {
    fn sum<I: Iterator<Item = &'a Expression<F>>>(iter: I) -> Self {
        iter.cloned().sum()
    }
}

impl<F: Field> Sum for Expression<F> {
    fn sum<I: Iterator<Item = Self>>(iter: I) -> Self {
        iter.reduce(|acc, item| acc + item)
            .unwrap_or_else(Expression::zero)
    }
}

impl<'a, F: Field> Product<&'a Expression<F>> for Expression<F> {
    fn product<I: Iterator<Item = &'a Expression<F>>>(iter: I) -> Self {
        iter.cloned().product()
    }
}

impl<F: Field> Product for Expression<F> {
    fn product<I: Iterator<Item = Self>>(iter: I) -> Self {
        iter.reduce(|acc, item| acc * item)
            .unwrap_or_else(Expression::one)
    }
}

fn merge_left_right<T: Ord>(
    lhs: Option<BTreeSet<T>>,
    rhs: Option<BTreeSet<T>>,
) -> Option<BTreeSet<T>> {
    match (lhs, rhs) {
        (Some(lhs), None) | (None, Some(lhs)) => Some(lhs),
        (Some(mut lhs), Some(mut rhs)) => {
            lhs.append(&mut rhs);
            Some(lhs)
        }
        _ => None,
    }
}

#[derive(FromPrimitive)]
enum ExpressionCode {
    Constant = 0,
    CommonPolynomial,
    Polynomial,
    Challenge,
    Negated,
    Sum,
    Product,
    Scaled,
    DistributePowers,
}

fn expression_code<F: Field>(e: &Expression<F>) -> ExpressionCode {
    match e {
        Expression::Constant(_) => ExpressionCode::Constant,
        Expression::CommonPolynomial(_) => ExpressionCode::CommonPolynomial,
        Expression::Polynomial(_) => ExpressionCode::Polynomial,
        Expression::Challenge(_) => ExpressionCode::Challenge,
        Expression::Negated(_) => ExpressionCode::Negated,
        Expression::Sum(_, _) => ExpressionCode::Sum,
        Expression::Product(_, _) => ExpressionCode::Product,
        Expression::Scaled(_, _) => ExpressionCode::Scaled,
        Expression::DistributePowers(_, _) => ExpressionCode::DistributePowers,
    }
}

impl<F: FieldExt> Serializable for Expression<F> {
    fn fetch<R: io::Read>(reader: &mut R) -> io::Result<Expression<F>> {
        let code = read_u32(reader)?;
        match num::FromPrimitive::from_u32(code).unwrap() {
            ExpressionCode::Constant => {
                let scalar = F::read(reader)?;
                Ok(Expression::Constant(scalar))
            }
            ExpressionCode::CommonPolynomial => {
                let code = read_u32(reader)?;
                match num::FromPrimitive::from_u32(code).unwrap() {
                    CommonPolynomialCode::Identity => {
                        Ok(Expression::CommonPolynomial(CommonPolynomial::Identity))
                    }
                    CommonPolynomialCode::Lagrange => {
                        let v = read_u32(reader)? as i32;
                        Ok(Expression::CommonPolynomial(CommonPolynomial::Lagrange(v)))
                    }
                    CommonPolynomialCode::EqXY => {
                        let v = read_u32(reader)? as usize;
                        Ok(Expression::CommonPolynomial(CommonPolynomial::EqXY(v)))
                    }
                }
            }
            ExpressionCode::Polynomial => {
                let poly = read_u32(reader)? as usize;
                let rotation = read_u32(reader)? as i32;
                Ok(Expression::Polynomial(Query::new(poly, rotation)))
            }
            ExpressionCode::Challenge => {
                let v = read_u32(reader)? as usize;
                Ok(Expression::Challenge(v))
            }
            ExpressionCode::Negated => Ok(Expression::Negated(Box::new(Self::fetch(reader)?))),

            ExpressionCode::Sum => {
                let a = Self::fetch(reader)?;
                let b = Self::fetch(reader)?;
                Ok(Expression::Sum(Box::new(a), Box::new(b)))
            }

            ExpressionCode::Product => {
                let a = Self::fetch(reader)?;
                let b = Self::fetch(reader)?;
                Ok(Expression::Product(Box::new(a), Box::new(b)))
            }

            ExpressionCode::Scaled => {
                let a = Self::fetch(reader)?;
                let f = F::read(reader)?;
                Ok(Expression::Scaled(Box::new(a), f))
            }
            ExpressionCode::DistributePowers => {
                let a: Vec<Expression<_>> = Vec::<Expression<F>>::fetch(reader)?;
                let b = Self::fetch(reader)?;
                Ok(Expression::DistributePowers(a, Box::new(b)))
            }
        }
    }

    fn store<W: io::Write>(&self, writer: &mut W) -> io::Result<()> {
        writer.write(&mut (expression_code(self) as u32).to_le_bytes())?;
        match self {
            Expression::Constant(scalar) => {
                writer.write(&mut scalar.to_repr().as_ref())?;
                Ok(())
            }
            Expression::CommonPolynomial(poly) => {
                writer.write(&mut (common_poly_code(poly) as u32).to_le_bytes())?;
                match poly {
                    CommonPolynomial::Identity => Ok(()),
                    CommonPolynomial::Lagrange(v) => {
                        writer.write(&v.to_le_bytes())?;
                        Ok(())
                    }
                    CommonPolynomial::EqXY(v) => {
                        writer.write(&(*v as u32).to_le_bytes())?;
                        Ok(())
                    }
                }
            }
            Expression::Polynomial(query) => {
                writer.write(&(query.poly() as u32).to_le_bytes())?;
                writer.write(&(query.rotation().0 as u32).to_le_bytes())?;
                Ok(())
            }
            Expression::Challenge(v) => {
                writer.write(&(*v as u32).to_le_bytes())?;
                Ok(())
            }
            Expression::Negated(a) => a.store(writer),
            Expression::Sum(a, b) => {
                a.store(writer)?;
                b.store(writer)?;
                Ok(())
            }
            Expression::Product(a, b) => {
                a.store(writer)?;
                b.store(writer)?;
                Ok(())
            }
            Expression::Scaled(a, f) => {
                a.store(writer)?;
                writer.write(&mut f.to_repr().as_ref())?;
                Ok(())
            }
            Expression::DistributePowers(a, b) => {
                a.store(writer)?;
                b.store(writer)?;
                Ok(())
            }
        }
    }
}
