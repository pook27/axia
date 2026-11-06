//! Independent checker for proof trees produced by the search engine.
//!
//! This module deliberately does not call proof search. It re-derives the
//! obligation represented by each proof node and checks its children against
//! the active logical context. A successful search result is only a candidate
//! until it passes this checker.

use crate::ast::Formula;
use crate::engine::{ProofRule, ProofStep, Universe};
use std::collections::HashMap;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct KernelError {
    pub path: Vec<usize>,
    pub message: String,
}

impl KernelError {
    fn at(path: &[usize], message: impl Into<String>) -> Self {
        Self { path: path.to_vec(), message: message.into() }
    }
}

impl std::fmt::Display for KernelError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.path.is_empty() {
            write!(f, "{}", self.message)
        } else {
            write!(f, "proof node {:?}: {}", self.path, self.message)
        }
    }
}

impl std::error::Error for KernelError {}

/// Check a candidate proof tree without invoking the search engine.
pub fn check_proof(proof: &ProofStep, universe: &Universe) -> Result<(), KernelError> {
    check_node(proof, universe, &mut Vec::new())
}

/// Check the proof tree and bind its root to the caller's original goal.
pub fn check_proof_for_goal(
    proof: &ProofStep,
    requested_goal: &Formula,
    universe: &Universe,
) -> Result<(), KernelError> {
    if proof.goal.unify(requested_goal).is_none() {
        return Err(KernelError::at(
            &[],
            format!(
                "proof establishes {}, not the requested goal {}",
                proof.goal, requested_goal
            ),
        ));
    }
    check_proof(proof, universe)
}

fn check_node(
    proof: &ProofStep,
    universe: &Universe,
    path: &mut Vec<usize>,
) -> Result<(), KernelError> {
    let fail = |message: String, path: &[usize]| KernelError::at(path, message);

    match &proof.rule {
        ProofRule::EqualityReflexivity => {
            match &proof.goal {
                Formula::Eq(left, right)
                    if left == right
                        && proof.sub_proofs.is_empty()
                        && proof.witnesses.is_empty() =>
                {
                    return Ok(());
                }
                _ => return Err(fail("malformed equality-reflexivity proof".into(), path)),
            }
        }
        ProofRule::Given(name) => {
            let facts = universe.all_facts();
            let Some(fact) = facts.get(name) else {
                return Err(fail(
                    format!("unknown assumption or derived fact '{}'", name),
                    path,
                ));
            };
            if !proof.sub_proofs.is_empty()
                || !proof.witnesses.is_empty()
                || fact.unify(&proof.goal).is_none()
            {
                return Err(fail(
                    format!("fact '{}' does not establish {}", name, proof.goal),
                    path,
                ));
            }
            return Ok(());
        }
        ProofRule::ConjunctionIntroduction => {
            let Formula::And(left, right) = &proof.goal else {
                return Err(fail(
                    "conjunction rule used for a non-conjunction goal".into(),
                    path,
                ));
            };
            if proof.sub_proofs.len() != 2
                || !proof.witnesses.is_empty()
                || proof.sub_proofs[0].goal != **left
                || proof.sub_proofs[1].goal != **right
            {
                return Err(fail(
                    "conjunction requires proofs of both conjuncts".into(),
                    path,
                ));
            }
        }
        ProofRule::DisjunctionIntroductionLeft | ProofRule::DisjunctionIntroductionRight => {
            let Formula::Or(left, right) = &proof.goal else {
                return Err(fail(
                    "disjunction rule used for a non-disjunction goal".into(),
                    path,
                ));
            };
            let expected = if matches!(&proof.rule, ProofRule::DisjunctionIntroductionLeft) {
                &**left
            } else {
                &**right
            };
            if proof.sub_proofs.len() != 1
                || !proof.witnesses.is_empty()
                || proof.sub_proofs[0].goal != *expected
            {
                return Err(fail(
                    "disjunction proof must establish the selected branch".into(),
                    path,
                ));
            }
        }
        ProofRule::ExistentialIntroduction => {
            let Formula::Exists { var, body, .. } = &proof.goal else {
                return Err(fail(
                    "existential rule used for a non-existential goal".into(),
                    path,
                ));
            };
            if proof.sub_proofs.len() != 1
                || proof.witnesses.len() != 1
                || proof.witnesses[0].0 != *var
            {
                return Err(fail(
                    "existential proof requires one matching witness and one sub-proof".into(),
                    path,
                ));
            }
            let bindings =
                HashMap::from([(var.clone(), proof.witnesses[0].1.clone())]);
            let instantiated = body.substitute(&bindings);
            if proof.sub_proofs[0].goal != instantiated {
                return Err(fail(
                    "existential sub-proof does not match the supplied witness".into(),
                    path,
                ));
            }
        }
        ProofRule::Axiom(axiom_name) => {
            let Some(axiom) = universe.axioms.iter().find(|a| a.name == *axiom_name) else {
                return Err(fail(
                    format!("unknown axiom proof rule '{}'", axiom_name),
                    path,
                ));
            };
            if !proof.witnesses.is_empty() {
                return Err(fail(
                    "axiom application cannot introduce existential witnesses".into(),
                    path,
                ));
            }
            let Some(bindings) = axiom.conclusion.unify(&proof.goal) else {
                return Err(fail(
                    format!(
                        "axiom '{}' conclusion does not match {}",
                        axiom.name, proof.goal
                    ),
                    path,
                ));
            };
            if axiom.premises.len() != proof.sub_proofs.len() {
                return Err(fail(
                    format!(
                        "axiom '{}' requires {} premise proof(s), found {}",
                        axiom.name,
                        axiom.premises.len(),
                        proof.sub_proofs.len()
                    ),
                    path,
                ));
            }
            for (index, (premise, child)) in
                axiom.premises.iter().zip(&proof.sub_proofs).enumerate()
            {
                let expected = premise.substitute(&bindings);
                if child.goal != expected {
                    return Err(fail(
                        format!(
                            "premise {} of '{}' should be {}, not {}",
                            index + 1,
                            axiom.name,
                            expected,
                            child.goal
                        ),
                        path,
                    ));
                }
            }
        }
    }

    for (index, child) in proof.sub_proofs.iter().enumerate() {
        path.push(index);
        let result = check_node(child, universe, path);
        path.pop();
        result?;
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::Term;
    use crate::engine::{Axiom, ProofRule, ProofStep};

    fn pred(name: &str) -> Formula {
        Formula::Pred(name.into(), vec![])
    }

    fn leaf(goal: Formula, rule: ProofRule) -> ProofStep {
        ProofStep {
            goal,
            rule,
            sub_proofs: vec![],
            witnesses: vec![],
        }
    }

    #[test]
    fn rejects_a_valid_proof_of_a_different_goal() {
        let universe = Universe::new();
        let proof = leaf(
            Formula::Eq(Term::Const("b".into()), Term::Const("b".into())),
            ProofRule::EqualityReflexivity,
        );
        let requested = Formula::Eq(
            Term::Const("a".into()),
            Term::Const("b".into()),
        );

        assert!(check_proof_for_goal(&proof, &requested, &universe).is_err());
        check_proof_for_goal(&proof, &proof.goal, &universe).unwrap();
    }

    #[test]
    fn accepts_a_named_assumption() {
        let mut universe = Universe::new();
        universe.add_given("P_fact".into(), pred("P"));
        let proof = leaf(pred("P"), ProofRule::Given("P_fact".into()));
        check_proof(&proof, &universe).unwrap();
    }

    #[test]
    fn checks_both_sides_of_conjunction() {
        let mut universe = Universe::new();
        universe.assumptions.insert("p".into(), pred("P"));
        universe.assumptions.insert("q".into(), pred("Q"));
        let proof = ProofStep {
            goal: Formula::And(Box::new(pred("P")), Box::new(pred("Q"))),
            rule: ProofRule::ConjunctionIntroduction,
            sub_proofs: vec![
                leaf(pred("P"), ProofRule::Given("p".into())),
                leaf(pred("Q"), ProofRule::Given("q".into())),
            ],
            witnesses: vec![],
        };
        check_proof(&proof, &universe).unwrap();

        let forged = ProofStep {
            sub_proofs: vec![
                leaf(pred("P"), ProofRule::Given("p".into())),
                leaf(pred("P"), ProofRule::Given("p".into())),
            ],
            ..proof
        };
        assert!(check_proof(&forged, &universe).is_err());
    }

    #[test]
    fn checks_axiom_conclusion_and_every_premise() {
        let mut universe = Universe::new();
        universe.add_axiom(Axiom {
            name: "P_to_Q".into(),
            vars: vec![],
            premises: vec![pred("P")],
            conclusion: pred("Q"),
        });
        universe.add_given("p".into(), pred("P"));
        let proof = ProofStep {
            goal: pred("Q"),
            rule: ProofRule::Axiom("P_to_Q".into()),
            sub_proofs: vec![leaf(pred("P"), ProofRule::Given("p".into()))],
            witnesses: vec![],
        };
        check_proof(&proof, &universe).unwrap();

        let forged = ProofStep { sub_proofs: vec![], ..proof };
        assert!(check_proof(&forged, &universe).is_err());
    }

    #[test]
    fn rejects_unknown_axioms_and_false_reflexivity() {
        let universe = Universe::new();
        assert!(check_proof(
            &leaf(pred("P"), ProofRule::Axiom("TrustMe".into())),
            &universe,
        )
        .is_err());
        assert!(check_proof(
            &leaf(
                Formula::Eq(Term::Const("a".into()), Term::Const("b".into())),
                ProofRule::EqualityReflexivity,
            ),
            &universe,
        )
        .is_err());
    }
}
