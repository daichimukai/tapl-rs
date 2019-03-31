#![feature(box_syntax, box_patterns)]
#![feature(bind_by_move_pattern_guards)]
#![feature(type_alias_enum_variants)]

#[macro_use]
extern crate pest_derive;

use std::{
    fmt::{self, Display},
    io::{self, Write},
};

use pest::{iterators::Pairs, Parser};

#[derive(Debug, PartialEq)]
enum Term {
    True,
    False,
    If(Box<Term>, Box<Term>, Box<Term>),
    Zero,
    Succ(Box<Term>),
    Pred(Box<Term>),
    IsZero(Box<Term>),
}

impl Display for Term {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::True => write!(f, "true"),
            Self::False => write!(f, "false"),
            Self::If(pred, t_true, t_false) => {
                write!(f, "if {} then {} else {}", pred, t_true, t_false)
            }
            Self::Zero => write!(f, "0"),
            Self::Succ(term) => match term.as_numeric_val() {
                Some(n) => write!(f, "{}", n + 1),
                None => write!(f, "succ {}", term),
            },
            Self::Pred(term) => write!(f, "pred {}", term),
            Self::IsZero(term) => write!(f, "iszero {}", term),
        }
    }
}

impl From<usize> for Term {
    fn from(source: usize) -> Self {
        if source == 0 {
            return Term::Zero;
        }

        Self::Succ(box (source - 1).into())
    }
}

impl<'a> From<Pairs<'a, Rule>> for Term {
    fn from(mut pairs: Pairs<Rule>) -> Self {
        let pair = pairs.next().unwrap();

        match pair.as_rule() {
            Rule::term => pair.into_inner().into(),
            Rule::if_expression => {
                let mut terms = pair.into_inner();
                let pred = terms.next().unwrap().into_inner().into();
                let t_term = terms.next().unwrap().into_inner().into();
                let f_term = terms.next().unwrap().into_inner().into();
                Term::If(box pred, box t_term, box f_term)
            }
            Rule::number => pair.as_str().trim_end().parse::<usize>().unwrap().into(),
            Rule::succ => Term::Succ(box pair.into_inner().into()),
            Rule::pred => Term::Pred(box pair.into_inner().into()),
            Rule::iszero => Term::IsZero(box pair.into_inner().into()),
            Rule::boolean => match pair.as_str() {
                "true" => Term::True,
                "false" => Term::False,
                _ => unreachable!(),
            },
            _ => unreachable!(),
        }
    }
}

impl Term {
    fn is_numeric_val(&self) -> bool {
        match self {
            Term::Zero => true,
            Term::Succ(t) => t.is_numeric_val(),
            _ => false,
        }
    }

    fn as_numeric_val(&self) -> Option<usize> {
        match self {
            Term::Zero => Some(0),
            Term::Succ(t) => t.as_numeric_val().map(|n| n + 1),
            _ => None,
        }
    }

    #[allow(dead_code)]
    fn is_val(&self) -> bool {
        match self {
            Term::True => true,
            Term::False => true,
            t => t.is_numeric_val(),
        }
    }

    #[allow(dead_code)]
    fn get_type(&self) -> Option<TermType> {
        match self {
            Term::True | Term::False => Some(TermType::Bool),
            Term::Zero => Some(TermType::Nat),
            Term::If(pred, t_term, f_term) => {
                let t_term_type = t_term.get_type();
                if pred.get_type() == Some(TermType::Bool)
                    && t_term_type.is_some()
                    && t_term_type == f_term.get_type()
                {
                    t_term.get_type()
                } else {
                    None
                }
            }
            Term::Succ(term) if term.get_type() == Some(TermType::Nat) => Some(TermType::Nat),
            Term::Pred(term) if term.get_type() == Some(TermType::Nat) => Some(TermType::Nat),
            Term::IsZero(term) if term.get_type() == Some(TermType::Nat) => Some(TermType::Bool),
            _ => None,
        }
    }

    fn eval1(self) -> Result<Term, Term> {
        match self {
            Term::If(box Term::True, box t_term, _) => Ok(t_term),
            Term::If(box Term::False, _, box f_term) => Ok(f_term),
            Term::If(box pred, t_term, f_term) => match pred.eval1() {
                Ok(term) => Ok(Term::If(box term, t_term, f_term)),
                Err(term) => Err(Term::If(box term, t_term, f_term)),
            },
            Term::Succ(box term) => term
                .eval1()
                .map(|e| Term::Succ(box e))
                .map_err(|v| Term::Succ(box v)),
            Term::Pred(box term) => match term {
                Term::Zero => Ok(Term::Zero),
                Term::Succ(box nv) if nv.is_numeric_val() => Ok(nv),
                term => term
                    .eval1()
                    .map(|e| Term::Pred(box e))
                    .map_err(|v| Term::Pred(box v)),
            },
            Term::IsZero(box term) => match term {
                Term::Zero => Ok(Term::True),
                Term::Succ(box nv) if nv.is_numeric_val() => Ok(Term::False),
                term => term
                    .eval1()
                    .map(|e| Term::IsZero(box e))
                    .map_err(|v| Term::IsZero(box v)),
            },
            _ => Err(self),
        }
    }
}

#[derive(Debug, PartialEq)]
enum TermType {
    Bool,
    Nat,
}

impl Display for TermType {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::Bool => write!(f, "Bool"),
            Self::Nat => write!(f, "Nat"),
        }
    }
}

#[derive(Parser)]
#[grammar = "grammar.pest"]
struct TermParser;

fn main() {
    println!("Untyped arithmetics interpreter");
    println!("Press Ctrl-c to abort.");
    println!();

    loop {
        print!("> ");
        io::stdout().flush().unwrap();
        let mut input = String::new();
        match io::stdin().read_line(&mut input) {
            Ok(_) => match TermParser::parse(Rule::term, &input) {
                Ok(parsed) => {
                    let mut expr: Term = parsed.into();

                    loop {
                        match expr.eval1() {
                            Ok(evaled) => {
                                expr = evaled;
                            }
                            Err(evaled) => {
                                expr = evaled;
                                break;
                            }
                        }
                    }
                    println!("▸ {}", expr);
                }
                _ => eprintln!("Parse error"),
            },
            Err(error) => eprintln!("Error: {}", error),
        }
    }
}
