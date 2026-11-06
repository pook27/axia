use axia::ast::Statement;
use axia::parser::{lex_checked, Parser};

fn formula_result(source: &str) -> Result<(), String> {
    let tokens = lex_checked(source)?;
    Parser::with_universe(tokens, None)
        .parse_formula_complete()
        .map(|_| ())
}

fn statement_result(source: &str) -> Result<Statement, String> {
    let tokens = lex_checked(source)?;
    Parser::with_universe(tokens, None).parse_statement_complete()
}

#[test]
fn accepts_well_formed_formulas() {
    for source in [
        "Parent(alice, bob)",
        "f(x) = y",
        "A and B or C",
        "not P(x)",
        "(2 + 2) = 4",
        "exists x : Nat, P(x) -> Q(x)",
        "P()",
    ] {
        assert!(formula_result(source).is_ok(), "should accept: {source}");
    }
}

#[test]
fn rejects_trailing_tokens_after_formula() {
    for source in ["P(x) )", "P(x) Q(y) =", "x = y z = w )", "A and B ,"] {
        let error = formula_result(source).expect_err(source);
        assert!(error.contains("trailing"), "{source}: {error}");
    }
}

#[test]
fn rejects_incomplete_formulas() {
    for source in ["", "P(x) and", "not", "x =", "exists x,", "exists x : Nat P(x)", "P(x) ->"] {
        assert!(formula_result(source).is_err(), "should reject: {source:?}");
    }
}

#[test]
fn rejects_unbalanced_parentheses() {
    for source in ["P(x", "P(x, y", "(x + y = z", "f((x) = y"] {
        assert!(formula_result(source).is_err(), "should reject: {source}");
    }
}

#[test]
fn rejects_malformed_argument_lists() {
    for source in ["P(x,)", "P(,x)", "P(x y)"] {
        assert!(formula_result(source).is_err(), "should reject: {source}");
    }
}

#[test]
fn rejects_unknown_characters_instead_of_dropping_them() {
    let error = lex_checked("P(x) @ Q(y)").expect_err("@ is not part of the language");
    assert!(error.contains('@'));
    assert!(formula_result("A & B").is_err());
}

#[test]
fn accepts_well_formed_statements() {
    assert!(matches!(statement_result("Pt : Type"), Ok(Statement::TypeDecl(_))));
    assert!(matches!(statement_result("A : Pt"), Ok(Statement::ConstDecl(..))));
    assert!(matches!(statement_result("On : Pt -> Line -> Prop"), Ok(Statement::PredDecl(..))));
    assert!(matches!(
        statement_result("Refl : forall x : Object, x = x"),
        Ok(Statement::AxiomDecl { .. })
    ));
    assert!(matches!(statement_result("import logic"), Ok(Statement::Import(_))));
    assert!(matches!(statement_result("Given H : P(x)"), Ok(Statement::GivenDecl(..))));
}

#[test]
fn rejects_malformed_statements() {
    for source in [
        "Pt : Type extra",
        "A : Pt Line",
        "On : Pt ->",
        "Name :",
        "Name : 42",
        "Name : )",
        "Bad : forall : Object, x = x",
        "Bad : forall x Object, x = x",
        "Bad : forall x : , x = x",
        "Bad : forall x : Object x = x",
        "import logic extra",
        "Given H : P(x) )",
        "Given : P(x)",
    ] {
        assert!(statement_result(source).is_err(), "should reject: {source}");
    }
}
