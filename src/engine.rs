use std::collections::HashMap;
use crate::ast::{Term, Formula};

pub type Bindings = HashMap<String, Term>;

#[derive(Debug, Clone)]
pub struct ProofStep {
    pub goal: Formula,
    pub rule_name: String,
    pub sub_proofs: Vec<ProofStep>,
}

pub struct Axiom {
    pub name: String,
    pub vars: Vec<String>,
    pub premises: Vec<Formula>,
    pub conclusion: Formula,
}

impl Term {
    pub fn substitute(&self, bindings: &Bindings) -> Term {
        match self {
            Term::Var(n) => bindings.get(n).cloned().unwrap_or_else(|| Term::Var(n.clone())),
            Term::Const(_) => self.clone(),
            Term::Apply(n, args) => Term::Apply(n.clone(), args.iter().map(|a| a.substitute(bindings)).collect()),
        }
    }
}

impl Formula {
    pub fn substitute(&self, bindings: &Bindings) -> Formula {
        match self {
            Formula::Eq(l, r) => Formula::Eq(l.substitute(bindings), r.substitute(bindings)),
            Formula::Pred(n, args) => Formula::Pred(n.clone(), args.iter().map(|a| a.substitute(bindings)).collect()),
            Formula::And(l, r) => Formula::And(Box::new(l.substitute(bindings)), Box::new(r.substitute(bindings))),
        }
    }

    pub fn unify(&self, goal: &Formula) -> Option<Bindings> {
        let mut bindings = HashMap::new();
        if self.unify_inner(goal, &mut bindings) { Some(bindings) } else { None }
    }

    fn unify_inner(&self, goal: &Formula, bindings: &mut Bindings) -> bool {
        match (self, goal) {
            (Formula::Pred(n1, a1), Formula::Pred(n2, a2)) => {
                if n1 != n2 || a1.len() != a2.len() { return false; }
                a1.iter().zip(a2).all(|(x, y)| Self::unify_term(x, y, bindings))
            },
            (Formula::Eq(l1, r1), Formula::Eq(l2, r2)) => {
                Self::unify_term(l1, l2, bindings) && Self::unify_term(r1, r2, bindings)
            },
            _ => false 
        }
    }

    fn unify_term(p: &Term, t: &Term, bindings: &mut Bindings) -> bool {
        match (p, t) {
            (Term::Var(n), val) | (val, Term::Var(n)) => {
                if let Some(existing) = bindings.get(n) { existing == val } 
                else { bindings.insert(n.clone(), val.clone()); true }
            },
            (Term::Const(a), Term::Const(b)) => a == b,
            (Term::Apply(n1, a1), Term::Apply(n2, a2)) => {
                n1 == n2 && a1.len() == a2.len() && a1.iter().zip(a2).all(|(x, y)| Self::unify_term(x, y, bindings))
            },
            _ => false,
        }
    }
}

pub fn prove(goal: &Formula, axioms: &[Axiom], depth: u32) -> Option<ProofStep> {
    if depth > 10 { return None; }
    
    if let Formula::And(left, right) = goal {
        let p1 = prove(left, axioms, depth)?;
        let p2 = prove(right, axioms, depth)?;
        return Some(ProofStep {
            goal: goal.clone(),
            rule_name: "Conjunction".to_string(),
            sub_proofs: vec![p1, p2],
        });
    }

    for axiom in axioms {
        if let Some(bindings) = axiom.conclusion.unify(goal) {
            let required_premises: Vec<Formula> = axiom.premises.iter().map(|p| p.substitute(&bindings)).collect();
            let mut sub_proofs = Vec::new();
            
            let mut possible = true;
            for premise in required_premises {
                if let Some(p) = prove(&premise, axioms, depth + 1) { sub_proofs.push(p); } 
                else { possible = false; break; }
            }
            
            if possible {
                return Some(ProofStep { goal: goal.clone(), rule_name: axiom.name.clone(), sub_proofs });
            }
        }
    }
    None
}
