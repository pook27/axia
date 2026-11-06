use axia::ast::{Formula, Sort, Term};
use axia::parser::{lex, Parser};

fn parse_formula(source: &str) -> Formula {
    let mut parser = Parser::with_universe(lex(source), None);
    parser
        .parse_formula()
        .unwrap_or_else(|| panic!("failed to parse formula: {source}"))
}

fn variable(name: &str) -> Term {
    Term::Var(name.to_string(), Sort::object())
}

fn predicate(name: &str, args: Vec<Term>) -> Formula {
    Formula::Pred(name.to_string(), args)
}

#[test]
fn parses_predicate_application() {
    assert_eq!(
        parse_formula("Parent(alice, bob)"),
        predicate("Parent", vec![
            Term::Var("alice".to_string(), Sort::object()),
            Term::Var("bob".to_string(), Sort::object()),
        ])
    );
}

#[test]
fn parses_equality() {
    assert_eq!(
        parse_formula("f(x) = y"),
        Formula::Eq(
            Term::Apply("f".to_string(), vec![variable("x")]),
            variable("y"),
        )
    );
}

#[test]
fn parses_conjunction() {
    assert_eq!(
        parse_formula("P(x) and Q(x)"),
        Formula::And(
            Box::new(predicate("P", vec![variable("x")])),
            Box::new(predicate("Q", vec![variable("x")])),
        )
    );
}

#[test]
fn parses_disjunction() {
    assert_eq!(
        parse_formula("P(x) or Q(x)"),
        Formula::Or(
            Box::new(predicate("P", vec![variable("x")])),
            Box::new(predicate("Q", vec![variable("x")])),
        )
    );
}

#[test]
fn parses_negation() {
    assert_eq!(
        parse_formula("not P(x)"),
        Formula::Not(Box::new(predicate("P", vec![variable("x")]))),
    );
}

#[test]
fn parses_implication() {
    assert_eq!(
        parse_formula("P(x) -> Q(x)"),
        Formula::Implies(
            Box::new(predicate("P", vec![variable("x")])),
            Box::new(predicate("Q", vec![variable("x")])),
        )
    );
}

#[test]
fn implication_is_right_associative() {
    assert_eq!(
        parse_formula("P -> Q -> R"),
        Formula::Implies(
            Box::new(predicate("P", vec![])),
            Box::new(Formula::Implies(
                Box::new(predicate("Q", vec![])),
                Box::new(predicate("R", vec![])),
            )),
        )
    );
}

#[test]
fn conjunction_binds_more_tightly_than_disjunction() {
    assert_eq!(
        parse_formula("P or Q and R"),
        Formula::Or(
            Box::new(predicate("P", vec![])),
            Box::new(Formula::And(
                Box::new(predicate("Q", vec![])),
                Box::new(predicate("R", vec![])),
            )),
        )
    );
}

#[test]
fn parentheses_override_operator_precedence() {
    assert_eq!(
        parse_formula("(P or Q) and R"),
        Formula::And(
            Box::new(Formula::Or(
                Box::new(predicate("P", vec![])),
                Box::new(predicate("Q", vec![])),
            )),
            Box::new(predicate("R", vec![])),
        )
    );
}

#[test]
fn parses_existential_quantification() {
    assert_eq!(
        parse_formula("exists x : Person, Parent(x, bob)"),
        Formula::Exists {
            var: "x".to_string(),
            sort: Sort("Person".to_string()),
            body: Box::new(predicate(
                    "Parent",
                    vec![
                    Term::Var("x".to_string(), Sort("Person".to_string())),
                    variable("bob"),
                    ],
            )),
        }
    );
}

#[test]
fn parses_nested_existentials() {
    assert_eq!(
        parse_formula("exists x, exists y, Related(x, y)"),
        Formula::Exists {
            var: "x".to_string(),
            sort: Sort::object(),
            body: Box::new(Formula::Exists {
                var: "y".to_string(),
                sort: Sort::object(),
                body: Box::new(predicate("Related", vec![variable("x"), variable("y")])),
            }),
        }
    );
}

