use crate::numbersystem::Number;
use std::{collections::HashMap, fmt::Display};

pub type Environment = HashMap<String, Term>;

// let's start by pharsing expressions
#[derive(PartialEq, Debug)]
pub enum Term {
    // DualOperators. Functions like + - * /, which take a right hand side and a left hand side.
    DuOp (
        Box<Term>,
        Operator,
        Box<Term>,
    ),
    // placeholder for a number
    Var(String),
    // number with value and unit
    Num(Number),
    // A empty set. The result of dividing by zero.
    Empty,
}

impl Display for Term {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Term::DuOp(term1, operator, term2) => {
                let op_sym = match operator {
                    Operator::Infix(sym) => {sym},
                    _ => "¿"
                };
                write!(f, "({}{}{})", term1, op_sym, term2)
            },
            Term::Var(sym) => write!(f, "{}", sym),
            Term::Num(number) => number.fmt(f),
            Term::Empty => write!(f, "{{}}"),
        }
    }
    //write!(f, "{} [{}]", {self.value}, {&self.unit})
}

impl Term {
    pub fn evaluate(&self, env_tracker: &Environment) -> Result<Number, String> {
        match self {
            Term::DuOp(term1, operator, term2) => {
                match operator {
                    Operator::Add => todo!(),
                    Operator::Sub => todo!(),
                    Operator::Mul => todo!(),
                    Operator::Div => todo!(),
                    Operator::Infix(op) => {
                        match op {
                            val if *val == "*".to_string() => Ok(term1.evaluate(&env_tracker)? * term2.evaluate(&env_tracker)?),
                            val if *val == "/".to_string() => term1.evaluate(&env_tracker)? / term2.evaluate(&env_tracker)?,
                            val if *val == "+".to_string() => term1.evaluate(&env_tracker)? + term2.evaluate(&env_tracker)?,
                            val if *val == "-".to_string() => term1.evaluate(&env_tracker)? - term2.evaluate(&env_tracker)?,
                            op => Err(format!("unknown operator: {}", op))
                        }
                    }
                }
            },
            Term::Var(sym) => {
                match env_tracker.get(sym) {
                    Some(term) => term.evaluate(env_tracker),
                    None => Err(format!("use of undefined variable '{}' (couldn't find it when evaluating the expression)", {sym})),
                }
            },
            Term::Num(number) => Ok(number.clone()),
            Term::Empty => Err("Trying to evaluate Empty".to_owned()),
        }
    }
}

// this isn't expandable at runtime.
#[derive(PartialEq, Debug)]
pub enum Operator {
    Add,
    Sub,
    Mul,
    Div,
    Infix(String)
}