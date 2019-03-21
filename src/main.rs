#[derive(Debug)]
pub enum Term {
    True,
    False,
    If(Box<Term>, Box<Term>, Box<Term>),
    Zero,
    Succ(Box<Term>),
    Pred(Box<Term>),
    IsZero(Box<Term>),
}

impl Term {
    pub fn is_numeric_val(&self) -> bool {
        match self {
            Term::Zero => true,
            Term::Succ(t) => t.is_numeric_val(),
            _ => false,
        }
    }

    pub fn is_val(&self) -> bool {
        match self {
            Term::True => true,
            Term::False => true,
            t => t.is_numeric_val(),
        }
    }
}

fn main() {}
