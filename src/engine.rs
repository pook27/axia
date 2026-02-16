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
    // Basic substitution (shallow)
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

    fn occurs_check(n: &str, t: &Term, bindings: &Bindings) -> bool {
        let t_res = Self::resolve(t, bindings);
        match t_res {
            Term::Var(v) => v == n,
            Term::Apply(_, args) => args.iter().any(|arg| Self::occurs_check(n, arg, bindings)),
            Term::Const(_) => false,
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
                a1.iter().zip(a2).all(|(x, y)| Self::unify_term(x, &y, bindings))
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

fn unify_term(t1: &Term, t2: &Term, bindings: &mut Bindings) -> bool {
        let t1_res = Self::resolve(t1, bindings).clone();
        let t2_res = Self::resolve(t2, bindings).clone();

        match (t1_res, t2_res) {
            (Term::Var(n1), Term::Var(n2)) => {
                if n1 == n2 { return true; }
                bindings.insert(n1, Term::Var(n2));
                true
            },
            (Term::Var(n), val) | (val, Term::Var(n)) => {
                // SAFETY: Don't bind if it creates a cycle!
                if Self::occurs_check(&n, &val, bindings) { return false; }
                bindings.insert(n, val);
                true
            },
            (Term::Const(a), Term::Const(b)) => a == b,
            (Term::Apply(n1, a1), Term::Apply(n2, a2)) => {
                n1 == n2 && a1.len() == a2.len() && 
                a1.iter().zip(a2).all(|(x, y)| Self::unify_term(x, &y, bindings))
            },
            _ => false,
        }
    }

    fn resolve<'a>(t: &'a Term, bindings: &'a Bindings) -> &'a Term {
        let mut current = t;
        while let Term::Var(n) = current {
            match bindings.get(n) {
                Some(next) => {
                    if next == current { break; } // Cycle detected, stop
                    current = next;
                },
                None => break, // End of chain
            }
        }
        current
    }
}

// --- PRO ENGINE (IDDFS) ---

pub fn prove(goal: &Formula, axioms: &[Axiom], max_depth: u32) -> Option<ProofStep> {
    for depth in 1..=max_depth {
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
    
    // Apply current knowledge to the goal
    let current_goal = goal.substitute(bindings);
    
    // Cycle Check
    if path.contains(&current_goal) { return None; }
    let mut new_path = path.clone();
    new_path.push(current_goal.clone());

    // 1. Structural Rules
    if let Formula::And(left, right) = &current_goal {
        let (p1, b1) = prove_dfs(left, axioms, depth, bindings, &new_path)?;
        let right_sub = right.substitute(&b1);
        let (p2, b2) = prove_dfs(&right_sub, axioms, depth, &b1, &new_path)?;

        return Some((
            ProofStep { goal: current_goal.clone(), rule_name: "Conjunction".to_string(), sub_proofs: vec![p1, p2] },
            b2
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

    // 2. Axiom Matching
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
                    total_bindings.extend(b_out);
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
