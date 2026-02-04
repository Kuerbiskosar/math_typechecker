use crate::numbersystem::Number;
use crate::pharsers::{Info, Span};
use std::{collections::HashMap, fmt::Display};

pub type Environment = HashMap<String, PTerm>;

/// Programming Term. It contains a mathematical term and metadata
#[derive(PartialEq, Debug)]
pub struct PTerm {
    pub content: Term,
    pub span: Span,
}
// let's start by pharsing expressions
#[derive(PartialEq, Debug)]
pub enum Term {
    // DualOperators. Functions like + - * /, which take a right hand side and a left hand side.
    DuOp (
        Box<PTerm>,
        Operator,
        Box<PTerm>,
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
                write!(f, "({}{}{})", term1.content, op_sym, term2.content)
            },
            Term::Var(sym) => write!(f, "{}", sym),
            Term::Num(number) => number.fmt(f),
            Term::Empty => write!(f, "{{}}"),
        }
    }
    //write!(f, "{} [{}]", {self.value}, {&self.unit})
}

impl PTerm {
    pub fn evaluate(& self, env_tracker: &Environment) -> Result<Number, Vec<Info>> {
        match &self.content {
            Term::DuOp(term1, operator, term2) => {
                match operator {
                    Operator::Add => todo!(),
                    Operator::Sub => todo!(),
                    Operator::Mul => todo!(),
                    Operator::Div => todo!(),
                    Operator::Infix(op) => self.evaluate_infix_op(env_tracker, op, term1, term2),
                }
            },
            Term::Var(sym) => {
                match env_tracker.get(sym) {
                    Some(term) => term.evaluate(env_tracker),
                    None => {
                        let info = Info { msg: format!("use of undefined variable '{}' (couldn't find it when evaluating the expression)", {sym}),
                                                pos: self.span };
                        Err(vec![info])
                    },
                }
            },
            Term::Num(number) => Ok(number.clone()),
            Term::Empty => Err(vec![Info{msg: "Trying to evaluate Empty".to_owned(), pos: self.span}]),
        }
    }

    fn evaluate_infix_op (&self, env_tracker: &Environment, op: &String, term1: &PTerm, term2: &PTerm) -> Result<Number, Vec<Info>> {
    // evaluate right and left hand side. Return error, if left or right fail.
        let left = term1.evaluate(&env_tracker);
        let right = term2.evaluate(&env_tracker);
        // if left or right failed, we don't divide, but return both error vectors merged.
        if left.is_err() || right.is_err() {
            let mut info= match left {
                Ok(_) => Vec::new(),
                Err(e) => e,
            };
            match right {
                Ok(_) => (),
                Err(mut e) => info.append(&mut e),
            }
            return Err(info)
        }

        // left and right evaluated sucessfully.
        let left = left.expect("must be Ok because I run an .is_err check");
        let right = right.expect("must be Ok because I run an .is_err check");
        let res = match op {
            val if *val == "*".to_string() => Ok(left * right),
            val if *val == "/".to_string() => left / right,
            val if *val == "+".to_string() => left + right,
            val if *val == "-".to_string() => left - right,
            op => return Err(
            vec![Info {
                msg: format!("unknown operator: {}", op),
                pos: Span{ start:term1.span.end, end: term2.span.start }
                }]
            )
        };
        match res {
            Ok(x) => Ok(x),
            Err(e) => Err(vec![Info{ msg: e, pos: self.span }]),
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