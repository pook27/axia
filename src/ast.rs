use std::fmt;

/// A sort/type in the object language, e.g. "Nat", "Pt", "Line", "Prop".
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Sort(pub String);

impl Sort {
    pub fn object() -> Self { Sort("Object".to_string()) }
    pub fn prop() -> Self   { Sort("Prop".to_string()) }
}

impl fmt::Display for Sort {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result { write!(f, "{}", self.0) }
}

/// A term in the object language.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Term {
    /// A logic variable (unknown), carrying its declared sort.
    Var(String, Sort),
    /// A ground constant.
    Const(String),
    /// A function application: `f(t1, t2, ...)`.
    Apply(String, Vec<Term>),
}

/// A first-order formula, now including existential quantification.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Formula {
    Eq(Term, Term),
    Pred(String, Vec<Term>),
    And(Box<Formula>, Box<Formula>),
    Or(Box<Formula>, Box<Formula>),
    Not(Box<Formula>),
    Implies(Box<Formula>, Box<Formula>),
    /// ∃ var : Sort, body
    ///
    /// During proof search the engine replaces `var` with a fresh Skolem
    /// constant `?wN` and attempts to prove `body[var := ?wN]`.  If the
    /// sub-proof succeeds the final bindings tell us what `?wN` resolved to,
    /// giving the explicit witness.
    Exists {
        var:  String,
        sort: Sort,
        body: Box<Formula>,
    },
}

/// A top-level declaration.
#[derive(Debug, Clone)]
pub enum Statement {
    TypeDecl(String),
    /// A ground constant with a declared sort, e.g. `A : Pt`.
    /// Unlike `TypeDecl`, the sort is not `"Type"` but a concrete object sort.
    ConstDecl(String, Sort),
    /// Predicate / function signature declaration: `(name, arg_sorts, return_sort)`.
    PredDecl(String, Vec<Sort>, Sort),
    AxiomDecl {
        name: String,
        vars: Vec<(String, Sort)>,
        body: Formula,
    },
    /// `import <universe_name>` — pull all axioms from another universe.
    Import(String),
}

// ---------------------------------------------------------------------------
// Display impls
// ---------------------------------------------------------------------------

impl fmt::Display for Term {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Term::Var(name, _sort) => write!(f, "{}", name),
            Term::Const(name)      => write!(f, "{}", name),
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
            Formula::Eq(lhs, rhs)   => write!(f, "{} = {}", lhs, rhs),
            Formula::Pred(name, args) => {
                write!(f, "{}(", name)?;
                for (i, arg) in args.iter().enumerate() {
                    if i > 0 { write!(f, ", ")?; }
                    write!(f, "{}", arg)?;
                }
                write!(f, ")")
            }
            Formula::And(l, r)      => write!(f, "({}) ∧ ({})", l, r),
            Formula::Or(l, r)       => write!(f, "({}) ∨ ({})", l, r),
            Formula::Not(inner)     => write!(f, "¬({})", inner),
            Formula::Implies(l, r)  => write!(f, "({}) → ({})", l, r),
            Formula::Exists { var, sort, body } => {
                if sort == &Sort::object() {
                    write!(f, "∃ {}, {}", var, body)
                } else {
                    write!(f, "∃ {} : {}, {}", var, sort, body)
                }
            }
        }
    }
}
