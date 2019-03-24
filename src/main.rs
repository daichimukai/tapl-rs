#![feature(box_syntax, box_patterns)]
#![feature(bind_by_move_pattern_guards)]
#![feature(type_alias_enum_variants)]

#[macro_use]
extern crate pest_derive;

use std::env;
use std::fmt::{self, Display};
use std::process;

use pest::iterators::Pairs;
use pest::Parser;

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
            Self::Succ(term) => write!(f, "succ {}", term),
            Self::Pred(term) => write!(f, "pred {}", term),
            Self::IsZero(term) => write!(f, "iszero {}", term),
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

    #[allow(dead_code)]
    fn is_val(&self) -> bool {
        match self {
            Term::True => true,
            Term::False => true,
            t => t.is_numeric_val(),
        }
    }

    fn eval1(self) -> Result<Term, Term> {
        match self {
            Term::If(box Term::True, box t_term, _) => Ok(t_term),
            Term::If(box Term::False, _, box f_term) => Ok(f_term),
            Term::If(box pred, t_term, f_term) => Ok(Term::If(box pred.eval1()?, t_term, f_term)),
            Term::Succ(box term) => Ok(Term::Succ(box term.eval1()?)),
            Term::Pred(box term) => match term {
                Term::Zero => Ok(Term::Zero),
                Term::Succ(box nv) if nv.is_numeric_val() => Ok(nv),
                _ => Ok(Term::Pred(box term.eval1()?)),
            },
            Term::IsZero(box term) => match term {
                Term::Zero => Ok(Term::True),
                Term::Succ(box nv) if nv.is_numeric_val() => Ok(Term::False),
                _ => Ok(Term::IsZero(box term.eval1()?)),
            },
            _ => Err(self),
        }
    }
}

#[derive(Parser)]
#[grammar = "grammar.pest"]
struct TermParser;

fn consume(mut pairs: Pairs<Rule>) -> Term {
    let pair = pairs.next().unwrap();

    match pair.as_rule() {
        Rule::term => consume(pair.into_inner()),
        Rule::if_expression => {
            let mut terms = pair.into_inner();
            let pred = consume(terms.next().unwrap().into_inner());
            let t_term = consume(terms.next().unwrap().into_inner());
            let f_term = consume(terms.next().unwrap().into_inner());
            Term::If(Box::new(pred), Box::new(t_term), Box::new(f_term))
        }
        Rule::zero => Term::Zero,
        Rule::succ => Term::Succ(Box::new(consume(pair.into_inner()))),
        Rule::pred => Term::Pred(Box::new(consume(pair.into_inner()))),
        Rule::iszero => Term::IsZero(Box::new(consume(pair.into_inner()))),
        Rule::boolean => match pair.as_str() {
            "true" => Term::True,
            "false" => Term::False,
            _ => unreachable!(),
        },
        _ => unreachable!(),
    }
}

fn main() {
    let args: Vec<_> = env::args().collect();
    if args.len() != 2 {
        eprintln!("Usage: {} <expression>", args[0]);
        process::exit(1);
    }

    let parsed = TermParser::parse(Rule::term, &args[1]).unwrap();

    let mut expr = consume(parsed);
    println!("{}", &expr);

    while let Ok(evaled) = expr.eval1() {
        println!("-> {}", &evaled);
        expr = evaled;
    }
}
