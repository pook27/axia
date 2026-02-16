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
            Formula::Or(l, r) => Formula::Or(Box::new(l.substitute(bindings)), Box::new(r.substitute(bindings))),
            Formula::Not(i) => Formula::Not(Box::new(i.substitute(bindings))),
            Formula::Implies(l, r) => Formula::Implies(Box::new(l.substitute(bindings)), Box::new(r.substitute(bindings))),
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
            (Formula::Not(i1), Formula::Not(i2)) => i1.unify_inner(i2, bindings),
            (Formula::Or(l1, r1), Formula::Or(l2, r2)) => l1.unify_inner(l2, bindings) && r1.unify_inner(r2, bindings),
            (Formula::Implies(l1, r1), Formula::Implies(l2, r2)) => l1.unify_inner(l2, bindings) && r1.unify_inner(r2, bindings),
            _ => false 
        }
    }

    fn unify_term(p: &Term, t: &Term, bindings: &mut Bindings) -> bool {
        match (p, t) {
            (Term::Var(n), val) | (val, Term::Var(n)) => {
                if let Some(existing) = bindings.get(n).cloned() {
                    Self::unify_term(&existing, val, bindings)
                } else { 
                    bindings.insert(n.clone(), val.clone()); 
                    true 
                }
            },
            (Term::Const(a), Term::Const(b)) => a == b,
            (Term::Apply(n1, a1), Term::Apply(n2, a2)) => {
                n1 == n2 && a1.len() == a2.len() && a1.iter().zip(a2).all(|(x, y)| Self::unify_term(x, y, bindings))
            },
            _ => false,
        }
    }
}

pub fn prove(goal: &Formula, axioms: &[Axiom], max_depth: u32) -> Option<ProofStep> {
    for depth in 1..=max_depth {
        // Start with empty bindings
        if let Some((proof, _)) = prove_dfs(goal, axioms, depth, &HashMap::new(), &vec![]) {
            return Some(proof);
        }
    }
    None
}

fn prove_dfs(
    goal: &Formula, 
    axioms: &[Axiom], 
    depth: u32, 
    bindings: &Bindings, 
    path: &Vec<Formula>
) -> Option<(ProofStep, Bindings)> {
    if depth == 0 { return None; }

    let current_goal = goal.substitute(bindings);

    if path.contains(&current_goal) { return None; }
    let mut new_path = path.clone();
    new_path.push(current_goal.clone());

    if let Formula::And(left, right) = &current_goal {
        let (p1, b1) = prove_dfs(left, axioms, depth, bindings, &new_path)?;

        let right_sub = right.substitute(&b1);
        let (p2, b2) = prove_dfs(&right_sub, axioms, depth, &b1, &new_path)?;

        return Some((
                ProofStep { goal: current_goal.clone(), rule_name: "Conjunction".to_string(), sub_proofs: vec![p1, p2] },
                b2 // Return combined knowledge
        ));
    }

    if let Formula::Or(left, right) = &current_goal {
        if let Some((p1, b1)) = prove_dfs(left, axioms, depth, bindings, &new_path) {
            return Some((ProofStep { goal: current_goal.clone(), rule_name: "Disjunction_Left".to_string(), sub_proofs: vec![p1] }, b1));
        }
        if let Some((p2, b2)) = prove_dfs(right, axioms, depth, bindings, &new_path) {
            return Some((ProofStep { goal: current_goal.clone(), rule_name: "Disjunction_Right".to_string(), sub_proofs: vec![p2] }, b2));
        }
    }

    for axiom in axioms {
        if let Some(new_bindings) = axiom.conclusion.unify(&current_goal) {
            let mut total_bindings = bindings.clone();
            total_bindings.extend(new_bindings);

            let mut sub_proofs = Vec::new();
            let mut possible = true;

            for premise in &axiom.premises {
                let p_sub = premise.substitute(&total_bindings);

                if let Some((proof, b_out)) = prove_dfs(&p_sub, axioms, depth - 1, &total_bindings, &new_path) {
                    sub_proofs.push(proof);
                    total_bindings.extend(b_out); // Update knowledge for next premise
                } else {
                    possible = false;
                    break;
                }
            }

            if possible {
                return Some((
                        ProofStep { goal: current_goal.clone(), rule_name: axiom.name.clone(), sub_proofs },
                        total_bindings
                ));
            }
        }
    }
    None
}
