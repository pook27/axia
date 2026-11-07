use axia::ast::{Formula, Sort, Term, VarId};
use axia::parser::{lex, Parser};

fn parse_formula(source: &str) -> Formula {
    let mut parser = Parser::with_universe(lex(source), None);
    let formula = parser
        .parse_formula()
        .unwrap_or_else(|| panic!("failed to parse formula: {source}"));
    normalize_formula(formula)
}

fn normalize_term(term: Term) -> Term {
    match term {
        Term::Var(name, sort) => Term::Var(
            VarId::from(axia::ast::variable_display_name(&name)),
            sort,
        ),
        Term::Const(name) => Term::Const(name),
        Term::Apply(name, args) => {
            Term::Apply(name, args.into_iter().map(normalize_term).collect())
        }
    }
}

// These tests check source-level syntax and precedence. Internal variable
// identity is tested separately in parser unit tests.
fn normalize_formula(formula: Formula) -> Formula {
    match formula {
        Formula::Eq(left, right) => Formula::Eq(normalize_term(left), normalize_term(right)),
        Formula::Pred(name, args) => {
            Formula::Pred(name, args.into_iter().map(normalize_term).collect())
        }
        Formula::And(left, right) => Formula::And(
            Box::new(normalize_formula(*left)),
            Box::new(normalize_formula(*right)),
        ),
        Formula::Or(left, right) => Formula::Or(
            Box::new(normalize_formula(*left)),
            Box::new(normalize_formula(*right)),
        ),
        Formula::Not(inner) => Formula::Not(Box::new(normalize_formula(*inner))),
        Formula::Implies(left, right) => Formula::Implies(
            Box::new(normalize_formula(*left)),
            Box::new(normalize_formula(*right)),
        ),
        Formula::Exists { var, sort, body } => Formula::Exists {
            var: VarId::from(axia::ast::variable_display_name(&var)),
            sort,
            body: Box::new(normalize_formula(*body)),
        },
    }
}

fn variable(name: &str) -> Term {
    Term::Var(VarId::from(name), Sort::object())
}

fn predicate(name: &str, args: Vec<Term>) -> Formula {
    Formula::Pred(name.to_string(), args)
}

#[test]
fn parses_predicate_application() {
    assert_eq!(
        parse_formula("Parent(alice, bob)"),
        predicate("Parent", vec![
            Term::Var(VarId::from("alice"), Sort::object()),
            Term::Var(VarId::from("bob"), Sort::object()),
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
            var: VarId::from("x"),
            sort: Sort("Person".to_string()),
            body: Box::new(predicate(
                    "Parent",
                    vec![
                    Term::Var(VarId::from("x"), Sort("Person".to_string())),
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
            var: VarId::from("x"),
            sort: Sort::object(),
            body: Box::new(Formula::Exists {
                var: VarId::from("y"),
                sort: Sort::object(),
                body: Box::new(predicate("Related", vec![variable("x"), variable("y")])),
            }),
        }
    );
}

