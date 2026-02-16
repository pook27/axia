use std::fmt;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Term {
    Var(String),
    Const(String),
    Apply(String, Vec<Term>), 
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Formula {
    Eq(Term, Term),
    Pred(String, Vec<Term>),
    And(Box<Formula>, Box<Formula>),
    Or(Box<Formula>, Box<Formula>),
    Not(Box<Formula>),
    Implies(Box<Formula>, Box<Formula>),
}

#[derive(Debug, Clone)]
pub enum Statement {
    TypeDecl(String), 
    PredDecl(String, ()), 
    AxiomDecl {
        name: String,
        vars: Vec<(String, String)>,
        body: Formula,
    },
    Goal(Formula),
}

impl fmt::Display for Term {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Term::Var(name) => write!(f, "{}", name),
            Term::Const(name) => write!(f, "{}", name),
            Term::Apply(name, args) => {
                write!(f, "{}(", name)?;
                for (i, arg) in args.iter().enumerate() {
                    if i > 0 { write!(f, ", ")?; }
                    write!(f, "{}", arg)?;
                }
                write!(f, ")")
            }
        }
    }
}

impl fmt::Display for Formula {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Formula::Eq(lhs, rhs) => write!(f, "{} = {}", lhs, rhs),
            Formula::Pred(name, args) => {
                write!(f, "{}(", name)?;
                for (i, arg) in args.iter().enumerate() {
                    if i > 0 { write!(f, ", ")?; }
                    write!(f, "{}", arg)?;
                }
                write!(f, ")")
            },
            Formula::And(left, right) => write!(f, "({}) ∧ ({})", left, right),
            Formula::Or(l, r) => write!(f, "({}) ∨ ({})", l, r),
            Formula::Not(inner) => write!(f, "¬({})", inner),
            Formula::Implies(l, r) => write!(f, "({}) → ({})", l, r),
        }
    }
}
