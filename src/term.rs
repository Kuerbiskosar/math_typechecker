use crate::numbersystem::{Number, Quantity, Unit};
use crate::pharsers::{Info, Span, Spanned};
use std::{collections::HashMap, fmt::Display};

#[derive(Debug, Clone, PartialEq)]
pub struct Environment {
    // list of infix operators with their precedence, for term parsing purposes
    infix_operators: String, // TODO: make datastructure for this
    // holds all the quanititys explicitly defined. This is used to assign the quantitys to new base units.
    // The key is the quantity symbol (which is used in the program like Unit: Metre (l) <- l is the length symbol).
    // The given position is where the Quantity is defined
    quantitys: HashMap<String, Spanned<Quantity>>,
    // holds all the unitss explicitly defined. This will be used to convert Numbers to different units.
    // The key is the unit symbol. (which is used in the program like: 5 kg = {[g]} <- g is the unit symbol.)
    units: HashMap<String, Spanned<Unit>>,
    // holds all the terms defined in the program. They all get typechecked.
    // todo make datastructure to hold evaluated value and type
    // The following types hold the index of the term within this vector.
    terms: Vec<PTerm>,
    // lookup table for the terms assigned to variables
    variables: HashMap<String, usize>,
    // Holding pairs of terms which should be equal to each other.
    equations: Vec<(usize, usize)>,
    // Terms whose results should be displayed
    to_evaluate: Vec<(usize, Span)>,

    // everything which doesn't have to do with terms
    texts: Vec<Text>,
}

impl Environment {
    pub fn new() -> Environment {
        Environment {
            infix_operators: "".to_string(),
            quantitys: HashMap::default(),
            units: HashMap::default(),
            terms: Vec::new(),
            variables: HashMap::default(),
            equations: Vec::new(),
            to_evaluate: Vec::new(),
            texts: Vec::new()
        }
    }
    pub fn get_quantitys(&self) -> &HashMap<String, Spanned<Quantity>>{
        &self.quantitys
    }
    /// inserts the the given term inside the environment and links the given variable to it.
    /// Returns a reference to the overwritten term, if the variable already existed.
    pub fn insert_variable(&mut self, var:String, expression: PTerm) -> Option<&PTerm>{
        self.terms.push(expression);
        let term_index = self.terms.len()-1;

        let overwritten_term = self.variables.insert(var, term_index).clone();
        match &overwritten_term {
            Some(old_index) => Some(&self.terms[*old_index]),
            None => None,
        }
    }
    /// inserts the term into the environment and links it inside the "to_evaluate" vector.
    /// Also takes the position, where the result should be placed in the parsed file.
    pub fn insert_to_evaluate(&mut self, expression: PTerm, position: Span) {
        self.terms.push(expression);
        let term_index = self.terms.len()-1;

        self.to_evaluate.push((term_index, position));
    }
    /// combination of insert_variable and insert_to_evaluate
    /// meant to store expressions like a = 5+5 = {}
    pub fn insert_evaluated_variable(&mut self, var:String, expression: PTerm, result_position: Span) -> Option<&PTerm>{
        self.terms.push(expression);
        let term_index = self.terms.len()-1;

        self.to_evaluate.push((term_index, result_position));
        let overwritten_term = self.variables.insert(var, term_index).clone();

        match &overwritten_term {
            Some(old_index) => Some(&self.terms[*old_index]),
            None => None,
        }
    }

    pub fn insert_text(&mut self, text:Text) {
        self.texts.push(text);
    }
    // returns the replaced quantity, if the key already existed
    pub fn insert_quantity(&mut self, symbol: String, quantity: Spanned<Quantity>) -> Option<Spanned<Quantity>> {
        self.quantitys.insert(symbol, quantity)
    }

    pub fn evaluate_and_print_to_evaluate(&mut self, full: &str) {
        for (term_index, res_position) in self.to_evaluate.clone() { // cloned to not run into borrow issues
            let result = self.evaluate_term(term_index);
            match result {
                Ok(num) => println!("{} = {num}\tat {} (Term at {})", self.terms[term_index].content, res_position.to_text_pos(full), self.terms[term_index].span.to_text_pos(full)),
                Err(msg) => println!("{} -> \tevaluation failed with error: {msg:?}", self.terms[term_index].content),
            }
        }    
    }
    pub fn evaluate_and_print_all_variables(& mut self) {
        // pretty print the environment
        let iterator = self.variables.clone(); // cloned to not run into borrow issues
        for (key, term_index) in iterator {
            println!("variable name: {key}, \n\tvalue: {}\n", self.terms[term_index].content);
            let result = self.evaluate_term(term_index);
            match result {
                Ok(num) => println!("\tevaluates to: {num}"),
                Err(msg) => println!("\tevaluation failed with error: {msg:?}"),
            }
        }
    }
    pub fn print_all_comment_locations(&self, full: &str) {
        println!("--- comment locations ---");
        for comment in &self.texts {
            println!("{:?} at {}", comment.text_type, comment.span.to_text_pos(full))
        }
        println!("------")
    }

    fn evaluate_term(&mut self, term_index: usize) -> Result<Number, Vec<Info>> {
        // check if that therm was already evaluated
        match &self.terms[term_index].evaluated {
            // I think cloning here is necessary, because we borrow a mutable reference.
            Some(result) => return result.clone(),
            None => {
                let result = self.terms[term_index].first_evaluate(&self);
                let output = result.clone();
                self.terms[term_index].evaluated = Some(result);
                output
            },
        }
    }
}

/// Programming Term. It contains a mathematical term and metadata
#[derive(PartialEq, Debug, Clone)]
pub struct PTerm {
    pub content: Term,
    pub span: Span,
    // to prevent double evaluation of terms
    evaluated: Option<Result<Number, Vec<Info>>>,
    // to "typecheck" (compare the units of two terms which should be equal)
    // chose unit instead of quantity, because it contains the quantity information.
    unit: Option<Unit>,
}
// let's start by pharsing expressions
#[derive(PartialEq, Debug, Clone)]
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
    pub fn new(content: Term, span: Span) -> PTerm {
        PTerm { content: content, span: span, evaluated: None, unit: None }
    }
    /// evaluates the therm. Needs a mutable reference, because it stores the result in the term for future evaluations.
    /// The env_tracker holds the Term definitions of the variables
    pub fn evaluate(&mut self, env_tracker: &Environment) -> Result<Number, Vec<Info>>{
        match &self.evaluated {
            Some(evaluated) => evaluated.clone(),
            None => {
                let res = self.first_evaluate(env_tracker);
                self.evaluated = Some(res.clone());
                res
            },
        }
    }
    fn first_evaluate(& self, env_tracker: &Environment) -> Result<Number, Vec<Info>> {
        // check if result was evaluated before TODO: actually write the evaluated result
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
                match env_tracker.variables.get(sym) {
                    Some(term_index) => {
                        match env_tracker.terms[*term_index].first_evaluate(env_tracker) {
                            ok @ Ok(_) => ok,
                            Err(mut info) => {
                                info.push(Info{ msg: format!("variable {} failed to evaluate", sym), pos: self.span});
                                Err(info)
                            },
                        }
                    },
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
        let left = term1.first_evaluate(&env_tracker);
        let right = term2.first_evaluate(&env_tracker);
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

/// Everything which can't be evaluated is text. This struct serves to hold the position of such text
/// to render it in a different font than the equations.
#[derive(Debug, Clone, PartialEq)]
pub struct Text {
    pub text_type: TextType,
    pub span: Span,
}
// to choose how to render the text
#[derive(Debug, Clone, PartialEq)]
pub enum TextType {
    // Prosa text
    Normal,
    // I often use comments to stop compiler warnings of non-working code, which I want to fix later
    // Such Terms should be visually striked through.
    StrikeThrough,
    // the usize declares the nesting level of the title starting at zero
    // subsubsubtitle whould be SubTitle(3)
    Title(usize),
    
}

// this isn't expandable at runtime.
#[derive(PartialEq, Debug, Clone)]
pub enum Operator {
    Add,
    Sub,
    Mul,
    Div,
    Infix(String)
}