use std::{borrow::Borrow, fmt, ops::Deref};

/// A sort/type in the object language, e.g. "Nat", "Pt", "Line", "Prop".
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Sort(pub String);

impl Sort {
    pub fn object() -> Self { Sort("Object".to_string()) }
    pub fn prop() -> Self { Sort("Prop".to_string()) }
}

impl fmt::Display for Sort {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result { write!(f, "{}", self.0) }
}

/// Opaque identity of a logical variable.
///
/// The payload is deliberately private: source names are presentation metadata,
/// never the identity used by unification, substitution, or the proof kernel.
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct VarId(String);

impl VarId {
    pub fn fresh(display_name: &str) -> Self {
        static NEXT_ID: std::sync::atomic::AtomicU64 =
            std::sync::atomic::AtomicU64::new(1);
        let id = NEXT_ID.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        Self(format!("__axia_var_{id}__{display_name}"))
    }

    pub fn display_name(&self) -> &str {
        let key = self.0.split_once("__instance").map_or(self.0.as_str(), |(base, _)| base);
        let key = key.split_once("__alpha").map_or(key, |(base, _)| base);
        key.strip_prefix("__axia_var_")
            .and_then(|rest| rest.split_once("__").map(|(_, name)| name))
            .unwrap_or(key)
    }

    pub(crate) fn derived(&self, suffix: &str) -> Self {
        Self(format!("{}{suffix}", self.0))
    }
}

impl From<String> for VarId {
    fn from(value: String) -> Self { Self(value) }
}
impl From<&str> for VarId {
    fn from(value: &str) -> Self { Self(value.to_string()) }
}
impl Deref for VarId {
    type Target = str;
    fn deref(&self) -> &Self::Target { &self.0 }
}
impl Borrow<str> for VarId {
    fn borrow(&self) -> &str { &self.0 }
}
impl fmt::Display for VarId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result { f.write_str(self.display_name()) }
}

pub fn variable_display_name(key: &VarId) -> &str { key.display_name() }

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Term {
    Var(VarId, Sort),
    Const(String),
    Apply(String, Vec<Term>),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Formula {
    Eq(Term, Term),
    Pred(String, Vec<Term>),
    And(Box<Formula>, Box<Formula>),
    Or(Box<Formula>, Box<Formula>),
    Not(Box<Formula>),
    Implies(Box<Formula>, Box<Formula>),
    Exists { var: VarId, sort: Sort, body: Box<Formula> },
}

#[derive(Debug, Clone)]
pub enum Statement {
    TypeDecl(String),
    ConstDecl(String, Sort),
    PredDecl(String, Vec<Sort>, Sort),
    AxiomDecl { name: String, vars: Vec<(VarId, Sort)>, body: Formula },
    Import(String),
    GivenDecl(String, Formula),
}

impl fmt::Display for Term {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Term::Var(name, _) => write!(f, "{}", name.display_name()),
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
            }
            Formula::And(l, r) => write!(f, "({}) ∧ ({})", l, r),
            Formula::Or(l, r) => write!(f, "({}) ∨ ({})", l, r),
            Formula::Not(inner) => write!(f, "¬({})", inner),
            Formula::Implies(l, r) => write!(f, "({}) → ({})", l, r),
            Formula::Exists { var, sort, body } => {
                if sort == &Sort::object() {
                    write!(f, "∃ {}, {}", var.display_name(), body)
                } else {
                    write!(f, "∃ {} : {}, {}", var.display_name(), sort, body)
                }
            }
        }
    }
}


#[cfg(test)]
mod variable_identity_tests {
    use super::VarId;

    #[test]
    fn same_spelling_gets_distinct_opaque_identities() {
        let first = VarId::fresh("x");
        let second = VarId::fresh("x");
        assert_ne!(first, second);
        assert_eq!(first.display_name(), "x");
        assert_eq!(second.display_name(), "x");
    }

    #[test]
    fn derived_identity_preserves_display_name_without_aliasing() {
        let original = VarId::fresh("x");
        let instance = original.derived("__instance7");
        assert_ne!(original, instance);
        assert_eq!(instance.display_name(), "x");
    }
}
