//! Independent checker for proof trees produced by the search engine.
//!
//! This module deliberately does not call proof search. It re-derives the
//! obligation represented by each proof node and checks its children against
//! the active logical context. A successful search result is only a candidate
//! until it passes this checker.

use crate::ast::{Formula, Sort, Term, VarId};
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
    if !formulas_alpha_equivalent(&proof.goal, requested_goal) {
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


/// Compare formulas modulo renaming of bound variables. Free variables retain
/// their identity: unification is deliberately not sufficient for a kernel
/// goal check because it could turn a proof of P(a) into a proof of P(x).
fn formulas_alpha_equivalent(left: &Formula, right: &Formula) -> bool {
    fn terms(
        left: &Term,
        right: &Term,
        bound: &[(VarId, VarId)],
    ) -> bool {
        match (left, right) {
            (Term::Var(left_id, left_sort), Term::Var(right_id, right_sort)) => {
                if left_sort != right_sort {
                    return false;
                }
                let left_binding = bound.iter().rev().find(|(id, _)| id == left_id);
                let right_binding = bound.iter().rev().find(|(_, id)| id == right_id);
                match (left_binding, right_binding) {
                    (Some((_, mapped_right)), Some((mapped_left, _))) => {
                        mapped_right == right_id && mapped_left == left_id
                    }
                    (None, None) => left_id == right_id,
                    _ => false,
                }
            }
            (Term::Const(left), Term::Const(right)) => left == right,
            (Term::Apply(left_name, left_args), Term::Apply(right_name, right_args)) => {
                left_name == right_name
                    && left_args.len() == right_args.len()
                    && left_args.iter().zip(right_args).all(|(l, r)| terms(l, r, bound))
            }
            _ => false,
        }
    }

    fn formulas(
        left: &Formula,
        right: &Formula,
        bound: &mut Vec<(VarId, VarId)>,
    ) -> bool {
        match (left, right) {
            (Formula::Eq(ll, lr), Formula::Eq(rl, rr)) => {
                terms(ll, rl, bound) && terms(lr, rr, bound)
            }
            (Formula::Pred(ln, la), Formula::Pred(rn, ra)) => {
                ln == rn
                    && la.len() == ra.len()
                    && la.iter().zip(ra).all(|(l, r)| terms(l, r, bound))
            }
            (Formula::And(ll, lr), Formula::And(rl, rr))
            | (Formula::Or(ll, lr), Formula::Or(rl, rr))
            | (Formula::Implies(ll, lr), Formula::Implies(rl, rr)) => {
                formulas(ll, rl, bound) && formulas(lr, rr, bound)
            }
            (Formula::Not(left), Formula::Not(right)) => formulas(left, right, bound),
            (
                Formula::Exists { var: left_var, sort: left_sort, body: left_body },
                Formula::Exists { var: right_var, sort: right_sort, body: right_body },
            ) => {
                if left_sort != right_sort {
                    return false;
                }
                bound.push((left_var.clone(), right_var.clone()));
                let equivalent = formulas(left_body, right_body, bound);
                bound.pop();
                equivalent
            }
            _ => false,
        }
    }

    formulas(left, right, &mut Vec::new())
}

fn witness_sort(term: &Term, universe: &Universe) -> Result<Sort, String> {
    match term {
        Term::Var(_, sort) => Ok(sort.clone()),
        Term::Const(name) => universe.constants.get(name).cloned().ok_or_else(|| {
            format!("existential witness constant '{}' has no declared sort", name)
        }),
        Term::Apply(_, _) => universe
            .infer_term_sort(term)?
            .ok_or_else(|| "existential witness function has no known return sort".to_string()),
    }
}

fn check_node(
    proof: &ProofStep,
    universe: &Universe,
    path: &mut Vec<usize>,
) -> Result<(), KernelError> {
    let fail = |message: String, path: &[usize]| KernelError::at(path, message);

    universe.validate_formula(&proof.goal).map_err(|message| {
        fail(format!("ill-typed proof goal: {}", message), path)
    })?;

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
            universe.validate_formula(fact).map_err(|message| {
                fail(format!("assumption '{}' is ill-typed: {}", name, message), path)
            })?;
            if !proof.sub_proofs.is_empty()
                || !proof.witnesses.is_empty()
                || !formulas_alpha_equivalent(fact, &proof.goal)
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
            let Formula::Exists { var, sort, body } = &proof.goal else {
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
            let witness = &proof.witnesses[0].1;
            let actual_sort = witness_sort(witness, universe).map_err(|message| {
                fail(format!("invalid existential witness: {}", message), path)
            })?;
            if actual_sort != *sort {
                return Err(fail(
                    format!(
                        "existential witness has sort {}, but the binder requires {}",
                        actual_sort, sort
                    ),
                    path,
                ));
            }
            let bindings = HashMap::from([(var.clone(), witness.clone())]);
            let instantiated = body.substitute(&bindings);
            if proof.sub_proofs[0].goal != instantiated {
                return Err(fail(
                    "existential sub-proof does not match the supplied witness".into(),
                    path,
                ));
            }
        }
        ProofRule::Axiom(axiom_name, instantiations) => {
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
            if instantiations.keys().any(|name| !axiom.vars.contains(name)) {
                return Err(fail(
                    format!("axiom '{}' has an instantiation for an undeclared variable", axiom.name),
                    path,
                ));
            }
            let instantiated_conclusion = axiom.conclusion.substitute(instantiations);
            if instantiated_conclusion != proof.goal {
                return Err(fail(
                    format!(
                        "axiom '{}' instantiated conclusion is {}, not {}",
                        axiom.name, instantiated_conclusion, proof.goal
                    ),
                    path,
                ));
            }
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
                let expected = premise.substitute(instantiations);
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

    fn declare_predicate(universe: &mut Universe, name: &str, argument_sorts: &[&str]) {
        universe.add_predicate(
            name.into(),
            argument_sorts.iter().map(|sort| (*sort).into()).collect(),
            "Prop".into(),
        );
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
        declare_predicate(&mut universe, "P", &[]);
        universe.add_given("P_fact".into(), pred("P"));
        let proof = leaf(pred("P"), ProofRule::Given("P_fact".into()));
        check_proof(&proof, &universe).unwrap();
    }

    #[test]
    fn checks_both_sides_of_conjunction() {
        let mut universe = Universe::new();
        declare_predicate(&mut universe, "P", &[]);
        declare_predicate(&mut universe, "Q", &[]);
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
        declare_predicate(&mut universe, "P", &[]);
        declare_predicate(&mut universe, "Q", &[]);
        universe.add_axiom(Axiom {
            name: "P_to_Q".into(),
            vars: vec![],
            premises: vec![pred("P")],
            conclusion: pred("Q"),
        });
        universe.add_given("p".into(), pred("P"));
        let proof = ProofStep {
            goal: pred("Q"),
            rule: ProofRule::Axiom("P_to_Q".into(), HashMap::new()),
            sub_proofs: vec![leaf(pred("P"), ProofRule::Given("p".into()))],
            witnesses: vec![],
        };
        check_proof(&proof, &universe).unwrap();

        let forged = ProofStep { sub_proofs: vec![], ..proof };
        assert!(check_proof(&forged, &universe).is_err());
    }


    #[test]
    fn checks_explicit_axiom_instantiations_against_conclusion_and_premises() {
        let mut universe = Universe::new();
        declare_predicate(&mut universe, "P", &["Object"]);
        declare_predicate(&mut universe, "Q", &["Object"]);
        let x = Term::Var("x".into(), crate::ast::Sort::object());
        let alice = Term::Const("alice".into());
        let p_x = Formula::Pred("P".into(), vec![x.clone()]);
        let q_x = Formula::Pred("Q".into(), vec![x]);
        universe.add_axiom(Axiom {
            name: "P_to_Q".into(),
            vars: vec!["x".into()],
            premises: vec![p_x],
            conclusion: q_x.clone(),
        });

        let instantiation = HashMap::from([("x".into(), alice.clone())]);
        let proof = ProofStep {
            goal: Formula::Pred("Q".into(), vec![alice.clone()]),
            rule: ProofRule::Axiom("P_to_Q".into(), instantiation.clone()),
            sub_proofs: vec![leaf(
                Formula::Pred("P".into(), vec![alice.clone()]),
                ProofRule::Given("p_alice".into()),
            )],
            witnesses: vec![],
        };
        universe.add_given(
            "p_alice".into(),
            Formula::Pred("P".into(), vec![alice.clone()]),
        );
        check_proof(&proof, &universe).unwrap();

        let undeclared = ProofStep {
            rule: ProofRule::Axiom(
                "P_to_Q".into(),
                HashMap::from([
                    ("x".into(), alice.clone()),
                    ("rogue".into(), alice.clone()),
                ]),
            ),
            ..proof.clone()
        };
        assert!(check_proof(&undeclared, &universe).is_err());

        let wrong_premise = ProofStep {
            sub_proofs: vec![leaf(
                Formula::Pred("P".into(), vec![Term::Const("bob".into())]),
                ProofRule::Given("p_alice".into()),
            )],
            ..proof
        };
        assert!(check_proof(&wrong_premise, &universe).is_err());
    }

    #[test]
    fn proof_search_records_the_axiom_instantiation_for_the_kernel() {
        let mut universe = Universe::new();
        declare_predicate(&mut universe, "P", &["Object"]);
        declare_predicate(&mut universe, "Q", &["Object"]);
        let x = Term::Var("x".into(), crate::ast::Sort::object());
        let alice = Term::Const("alice".into());
        universe.add_axiom(Axiom {
            name: "P_to_Q".into(),
            vars: vec!["x".into()],
            premises: vec![Formula::Pred("P".into(), vec![x.clone()])],
            conclusion: Formula::Pred("Q".into(), vec![x]),
        });
        universe.add_given(
            "p_alice".into(),
            Formula::Pred("P".into(), vec![alice.clone()]),
        );
        let goal = Formula::Pred("Q".into(), vec![alice.clone()]);
        let proof = crate::engine::prove(&goal, &universe, 8)
            .expect("the axiom should prove Q(alice)");

        match &proof.rule {
            ProofRule::Axiom(name, instantiations) => {
                assert_eq!(name, "P_to_Q");
                assert_eq!(instantiations.get("x"), Some(&alice));
            }
            other => panic!("expected an axiom proof, got {other:?}"),
        }
        check_proof_for_goal(&proof, &goal, &universe).unwrap();
    }

    #[test]
    fn rejects_unknown_axioms_and_false_reflexivity() {
        let mut universe = Universe::new();
        declare_predicate(&mut universe, "P", &[]);
        assert!(check_proof(
            &leaf(pred("P"), ProofRule::Axiom("TrustMe".into(), HashMap::new())),
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

    #[test]
    fn kernel_goal_checks_do_not_treat_unification_as_proof() {
        let mut universe = Universe::new();
        declare_predicate(&mut universe, "P", &["Object"]);
        universe.add_constant("a".into(), Sort::object());
        let a = Term::Const("a".into());
        let x = Term::Var(VarId::fresh("x"), Sort::object());
        let concrete = Formula::Pred("P".into(), vec![a.clone()]);
        let general = Formula::Pred("P".into(), vec![x]);

        universe.add_given("p_a".into(), concrete.clone());
        let concrete_proof = leaf(concrete, ProofRule::Given("p_a".into()));
        assert!(check_proof_for_goal(&concrete_proof, &general, &universe).is_err());

        let forged_general = leaf(general.clone(), ProofRule::Given("p_a".into()));
        assert!(check_proof_for_goal(&forged_general, &general, &universe).is_err());
    }

    #[test]
    fn kernel_goal_checks_accept_alpha_equivalent_quantifiers() {
        let mut universe = Universe::new();
        declare_predicate(&mut universe, "P", &["Object"]);
        let left_var = VarId::fresh("x");
        let right_var = VarId::fresh("y");
        let left = Formula::Exists {
            var: left_var.clone(),
            sort: Sort::object(),
            body: Box::new(Formula::Pred(
                "P".into(),
                vec![Term::Var(left_var, Sort::object())],
            )),
        };
        let right = Formula::Exists {
            var: right_var.clone(),
            sort: Sort::object(),
            body: Box::new(Formula::Pred(
                "P".into(),
                vec![Term::Var(right_var, Sort::object())],
            )),
        };
        universe.add_given("exists_p".into(), left.clone());
        let proof = leaf(left, ProofRule::Given("exists_p".into()));
        check_proof_for_goal(&proof, &right, &universe).unwrap();
    }

    #[test]
    fn rejects_existential_witness_with_wrong_sort() {
        let mut universe = Universe::new();
        declare_predicate(&mut universe, "P", &["Point"]);
        let point = Sort("Point".into());
        let line = Sort("Line".into());
        let binder = VarId::fresh("x");
        let witness = Term::Var(VarId::fresh("wrong"), line);
        let goal = Formula::Exists {
            var: binder.clone(),
            sort: point.clone(),
            body: Box::new(Formula::Pred(
                "P".into(),
                vec![Term::Var(binder.clone(), point)],
            )),
        };
        let child_goal = match &goal {
            Formula::Exists { body, var, .. } => body.substitute(&HashMap::from([
                (var.clone(), witness.clone()),
            ])),
            _ => unreachable!(),
        };
        let proof = ProofStep {
            goal,
            rule: ProofRule::ExistentialIntroduction,
            sub_proofs: vec![leaf(child_goal, ProofRule::Given("not_reached".into()))],
            witnesses: vec![(binder, witness)],
        };
        let error = check_proof(&proof, &universe).unwrap_err();
        assert!(error.message.contains("witness has sort Line"));
    }

    #[test]
    fn existential_witness_substitution_avoids_capturing_nested_binders() {
        let mut universe = Universe::new();
        declare_predicate(&mut universe, "R", &["Point", "Point"]);
        let point = Sort("Point".into());
        let outer = VarId::fresh("x");
        let nested = VarId::fresh("y");
        let witness = Term::Var(nested.clone(), point.clone());
        let nested_body = Formula::Pred(
            "R".into(),
            vec![
                Term::Var(outer.clone(), point.clone()),
                Term::Var(nested.clone(), point.clone()),
            ],
        );
        let body = Formula::Exists {
            var: nested.clone(),
            sort: point.clone(),
            body: Box::new(nested_body),
        };
        let goal = Formula::Exists {
            var: outer.clone(),
            sort: point,
            body: Box::new(body.clone()),
        };
        let instantiated = body.substitute(&HashMap::from([(outer.clone(), witness.clone())]));
        universe.add_given("witness_instance".into(), instantiated.clone());
        let proof = ProofStep {
            goal,
            rule: ProofRule::ExistentialIntroduction,
            sub_proofs: vec![leaf(instantiated, ProofRule::Given("witness_instance".into()))],
            witnesses: vec![(outer, witness)],
        };
        check_proof(&proof, &universe).unwrap();
    }

}
