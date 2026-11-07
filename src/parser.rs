use crate::ast::{Term, Formula, Statement, Sort};
use crate::engine::Universe;
use std::iter::Peekable;
use std::vec::IntoIter;
use std::collections::HashMap;
use std::sync::atomic::{AtomicU64, Ordering};

static NEXT_VARIABLE_ID: AtomicU64 = AtomicU64::new(1);

fn fresh_variable_key(display_name: &str) -> String {
    let id = NEXT_VARIABLE_ID.fetch_add(1, Ordering::Relaxed);
    format!("__axia_var_{}__{}", id, display_name)
}

// ---------------------------------------------------------------------------
// Tokens
// ---------------------------------------------------------------------------

#[derive(Debug, Clone, PartialEq)]
pub enum Token {
    Ident(String),
    Symbol(String),
    Keyword(String),
}

/// Lenient lexer: characters that are not part of the language are skipped.
/// Prefer [`lex_checked`] for user-supplied input.
#[allow(dead_code)]
pub fn lex(input: &str) -> Vec<Token> {
    lex_inner(input, &mut Vec::new())
}

/// Strict lexer: fails on any character that is not part of the language,
/// instead of silently dropping it.
pub fn lex_checked(input: &str) -> Result<Vec<Token>, String> {
    let mut unknown = Vec::new();
    let tokens = lex_inner(input, &mut unknown);
    match unknown.first() {
        Some(c) => Err(format!("unexpected character '{}'", c)),
        None => Ok(tokens),
    }
}

fn lex_inner(input: &str, unknown: &mut Vec<char>) -> Vec<Token> {
    let mut tokens = Vec::new();
    let mut chars = input.chars().peekable();

    while let Some(&c) = chars.peek() {
        match c {
            ' ' | '\t' | '\n' | '\r' => { chars.next(); }

            // Single-character symbols — including ∃ which is now a first-class
            // quantifier in formulas (not just in axiom headers).
            '(' | ')' | ':' | ',' | '∀' | '∃' | '∧' | '→' | '=' | '∨' | '¬' | '!' | '|' | '+' | '*' | '/' => {
                tokens.push(Token::Symbol(c.to_string()));
                chars.next();
            }

            '-' => {
                chars.next();
                if let Some(&'>') = chars.peek() {
                    chars.next();
                    tokens.push(Token::Symbol("→".to_string()));
                } else if let Some(&'-') = chars.peek() {
                    // Line comment: skip to end of line
                    while let Some(&x) = chars.peek() { if x == '\n' { break; } chars.next(); }
                } else {
                    tokens.push(Token::Symbol("-".to_string()));
                }
            }

            _ if c.is_alphanumeric() || c == '_' => {
                let mut s = String::new();
                while let Some(&x) = chars.peek() {
                    if x.is_alphanumeric() || x == '_' { s.push(x); chars.next(); } else { break; }
                }
                match s.as_str() {
                    "class" | "where" | "Type" | "Prop" | "forall" | "exists" | "import"
                        | "Given"
                        => tokens.push(Token::Keyword(s)),
                    "and" => tokens.push(Token::Symbol("∧".to_string())),
                    "or"  => tokens.push(Token::Symbol("∨".to_string())),
                    "not" => tokens.push(Token::Symbol("¬".to_string())),
                    _     => tokens.push(Token::Ident(s)),
                }
            }

            _ => { unknown.push(c); chars.next(); }
        }
    }
    tokens
}

// ---------------------------------------------------------------------------
// Parser
// ---------------------------------------------------------------------------

pub struct Parser<'a> {
    tokens: Peekable<IntoIter<Token>>,
    universe: Option<&'a Universe>,
    variable_sorts: HashMap<String, (String, Sort)>,
    free_variables: HashMap<String, String>,
}

impl<'a> Parser<'a> {
    /// Create a parser with access to the active universe for constant lookup.
    pub fn with_universe(tokens: Vec<Token>, universe: Option<&'a Universe>) -> Self {
        Parser {
            tokens: tokens.into_iter().peekable(),
            universe,
            variable_sorts: HashMap::new(),
            free_variables: HashMap::new(),
        }
    }

    /// Resolve a bare identifier to either `Term::Const` (if it is registered
    /// in the universe's constant table) or `Term::Var` (otherwise).
    /// Resolve a bare identifier to either a Peano number, `Term::Const`, or `Term::Var`.
    fn ident_to_term(&self, name: String) -> Term {
        // 1. Syntactic sugar: parse digits as Peano numbers.
        if let Ok(n) = name.parse::<u32>() {
            let mut term = Term::Const("0".to_string());
            for _ in 0..n {
                term = Term::Apply("S".to_string(), vec![term]);
            }
            return term;
        }

        // 2. Check whether this identifier is a scoped variable.
        if let Some((identity, sort)) = self.variable_sorts.get(&name) {
            return Term::Var(identity.clone(), sort.clone());
        }

        // 3. Check registered constants.
        if let Some(u) = self.universe {
            if u.constants.contains_key(&name) {
                return Term::Const(name);
            }
        }

        // 4. Otherwise, it's a free variable. Give each lexical variable a
        // stable internal key; its source spelling is display metadata only.
        let identity = self.free_variables
            .entry(name.clone())
            .or_insert_with(|| fresh_variable_key(&name))
            .clone();
        Term::Var(identity, Sort::object())
    }

    // ------------------------------------------------------------------
    // Low-level helpers
    // ------------------------------------------------------------------

    fn peek_sym(&mut self, expected: &str) -> bool {
        matches!(self.tokens.peek(), Some(Token::Symbol(s)) if s == expected)
    }

    fn consume_sym(&mut self, expected: &str) -> bool {
        if self.peek_sym(expected) { self.tokens.next(); true } else { false }
    }

    fn peek_kw(&mut self, expected: &str) -> bool {
        matches!(self.tokens.peek(), Some(Token::Keyword(k)) if k == expected)
    }

    /// Peek at whether the next token begins an existential quantifier.
    /// Accepts both the Unicode symbol `∃` and the ASCII keyword `exists`.
    fn peek_exists(&mut self) -> bool {
        self.peek_sym("∃") || self.peek_kw("exists")
    }

    /// Consume a sort identifier.  Returns `None` if the next token is not a sort.
    fn parse_sort(&mut self) -> Option<Sort> {
        match self.tokens.peek() {
            Some(Token::Keyword(k)) if k == "Type" || k == "Prop" => {
                let k = k.clone();
                self.tokens.next();
                Some(Sort(k))
            }
            // Numeric literals lex as identifiers but are never valid sort names.
            Some(Token::Ident(n)) if !n.starts_with(|c: char| c.is_ascii_digit()) => {
                let n = n.clone();
                self.tokens.next();
                Some(Sort(n))
            }
            _ => None,
        }
    }

    /// True once every token has been consumed.
    pub fn at_end(&mut self) -> bool {
        self.tokens.peek().is_none()
    }

    fn describe_next(&mut self) -> String {
        match self.tokens.peek() {
            Some(Token::Ident(s)) | Some(Token::Symbol(s)) | Some(Token::Keyword(s)) => s.clone(),
            None => "end of input".to_string(),
        }
    }

    fn finish<T>(&mut self, parsed: Option<T>) -> Result<T, String> {
        match parsed {
            None => Err("incomplete or malformed input".to_string()),
            Some(value) if self.at_end() => Ok(value),
            Some(_) => Err(format!("unexpected trailing token '{}'", self.describe_next())),
        }
    }

    /// Parse a whole formula, rejecting malformed input and leftover tokens.
    pub fn parse_formula_complete(&mut self) -> Result<Formula, String> {
        let parsed = self.parse_formula();
        self.finish(parsed)
    }

    /// Parse a whole statement, rejecting malformed input and leftover tokens.
    pub fn parse_statement_complete(&mut self) -> Result<Statement, String> {
        let parsed = self.parse_statement();
        self.finish(parsed)
    }

    // ------------------------------------------------------------------
    // Formula parsing
    //
    // Precedence (low → high):
    //   →  (right-associative)
    //   ∨
    //   ∧
    //   ¬ / atoms / quantifiers
    //
    // Quantifiers (∀ / ∃) are parsed at the *atom* level so they can appear
    // anywhere a formula can: as the body of another quantifier, as the RHS
    // of an implication, inside conjunctions, etc.
    // ------------------------------------------------------------------

    pub fn parse_formula(&mut self) -> Option<Formula> {
        let left = self.parse_or()?;
        if self.peek_sym("→") {
            self.tokens.next();
            let right = self.parse_formula()?; // right-associative
            return Some(Formula::Implies(Box::new(left), Box::new(right)));
        }
        Some(left)
    }

    fn parse_or(&mut self) -> Option<Formula> {
        let mut left = self.parse_and()?;
        while self.peek_sym("∨") || self.peek_sym("|") {
            self.tokens.next();
            let right = self.parse_and()?;
            left = Formula::Or(Box::new(left), Box::new(right));
        }
        Some(left)
    }

    fn parse_and(&mut self) -> Option<Formula> {
        let mut left = self.parse_unary()?;
        while self.peek_sym("∧") || self.peek_sym("&") {
            self.tokens.next();
            let right = self.parse_unary()?;
            left = Formula::And(Box::new(left), Box::new(right));
        }
        Some(left)
    }

    fn parse_unary(&mut self) -> Option<Formula> {
        // Negation
        if self.peek_sym("¬") || self.peek_sym("!") {
            self.tokens.next();
            let inner = self.parse_unary()?;
            return Some(Formula::Not(Box::new(inner)));
        }
        if self.peek_kw("not") {
            self.tokens.next();
            let inner = self.parse_unary()?;
            return Some(Formula::Not(Box::new(inner)));
        }

        // Existential quantifier — ∃ x : Sort, body  or  ∃ x, body
        if self.peek_exists() {
            return self.parse_exists_formula();
        }

        self.parse_atom()
    }

    /// Parse `∃ var : Sort, body` or `∃ var, body`.
    ///
    /// The sort annotation is optional; it defaults to `Object`.
    fn parse_exists_formula(&mut self) -> Option<Formula> {
        self.tokens.next(); // consume `∃` / `exists`

        let var = match self.tokens.next() {
            Some(Token::Ident(v)) => v,
            _ => return None,
        };

        let sort = if self.peek_sym(":") {
            self.tokens.next();
            self.parse_sort()?
        } else {
            Sort::object()
        };

        if !self.consume_sym(",") {
            return None;
        }

        // Introduce the existential variable into scope.
        let identity = fresh_variable_key(&var);
        let previous_sort = self.variable_sorts.insert(var.clone(), (identity.clone(), sort.clone()));

        let body = self.parse_formula();

        // Restore the previous scope.
        match previous_sort {
            Some(previous) => {
                self.variable_sorts.insert(var.clone(), previous);
            }
            None => {
                self.variable_sorts.remove(&var);
            }
        }

        let body = body?;

        Some(Formula::Exists {
            var: identity,
            sort,
            body: Box::new(body),
        })
    }

    fn parse_atom(&mut self) -> Option<Formula> {
        // Parentheses ambiguity: Is it a formula `(A ∧ B)` or a term `(2 + 2) = 4`?
        if self.peek_sym("(") {
            let fallback = self.tokens.clone();
            self.tokens.next(); // consume '('
            if let Some(f) = self.parse_formula() {
                if self.consume_sym(")") {
                    // LOOKAHEAD: If the next token is a math operator, this was a Math Term, not a Logical Formula!
                    let is_math_cont = self.peek_sym("+") || self.peek_sym("-") || 
                        self.peek_sym("*") || self.peek_sym("/") || 
                        self.peek_sym("=");
                    if !is_math_cont {
                        return Some(f);
                    }
                }
            }
            // If it failed or it continues with math, restore state and parse as a Term!
            self.tokens = fallback;
        }

        // Parse the left-hand side as a full mathematical term
        let lhs = self.parse_term()?;

        // If it's followed by an equals sign, it's an equation
        if self.peek_sym("=") {
            self.tokens.next();
            let rhs = self.parse_term()?;
            return Some(Formula::Eq(lhs, rhs));
        }

        // If no equals sign, promote the Term back into a logical Predicate
        match lhs {
            Term::Apply(name, args) => Some(Formula::Pred(name, args)),
            Term::Var(name, _) | Term::Const(name) => {
                let mut args = Vec::new();
                // Support juxtaposition `On Point Line`
                while let Some(Token::Ident(_)) = self.tokens.peek() {
                    if let Some(t) = self.parse_term() { args.push(t); } else { break; }
                }
                Some(Formula::Pred(name, args))
            }
        }
    }

    // ------------------------------------------------------------------
    // Term parsing
    // ------------------------------------------------------------------

    // ------------------------------------------------------------------
    // Term parsing (Recursive Descent for Operator Precedence)
    // ------------------------------------------------------------------

    pub fn parse_term(&mut self) -> Option<Term> {
        self.parse_term_add()
    }

    fn parse_term_add(&mut self) -> Option<Term> {
        let mut left = self.parse_term_mul()?;
        while let Some(Token::Symbol(s)) = self.tokens.peek() {
            if s == "+" {
                self.tokens.next();
                let right = self.parse_term_mul()?;
                left = Term::Apply("Add".to_string(), vec![left, right]);
            } else if s == "-" {
                self.tokens.next();
                let right = self.parse_term_mul()?;
                left = Term::Apply("Sub".to_string(), vec![left, right]);
            } else {
                break;
            }
        }
        Some(left)
    }

    fn parse_term_mul(&mut self) -> Option<Term> {
        let mut left = self.parse_term_primary()?;
        while let Some(Token::Symbol(s)) = self.tokens.peek() {
            if s == "*" {
                self.tokens.next();
                let right = self.parse_term_primary()?;
                left = Term::Apply("Mul".to_string(), vec![left, right]);
            } else if s == "/" {
                self.tokens.next();
                let right = self.parse_term_primary()?;
                left = Term::Apply("Div".to_string(), vec![left, right]);
            } else {
                break;
            }
        }
        Some(left)
    }

    fn parse_term_primary(&mut self) -> Option<Term> {
        // Handle parentheses grouping for terms: (x + y)
        if self.peek_sym("(") {
            self.tokens.next();
            let t = self.parse_term()?;
            if !self.consume_sym(")") { return None; }
            return Some(t);
        }

        let name = match self.tokens.next() {
            Some(Token::Ident(s)) => s,
            _ => return None,
        };

        // Function call: f(x, y)
        if self.peek_sym("(") {
            self.tokens.next();
            let mut args = Vec::new();
            if !self.peek_sym(")") {
                loop {
                    args.push(self.parse_term()?);
                    if self.consume_sym(",") { continue; }
                    break;
                }
            }
            if !self.consume_sym(")") { return None; }
            return Some(Term::Apply(name, args));
        }

        Some(self.ident_to_term(name))
    }

    // ------------------------------------------------------------------
    // Statement parsing
    // ------------------------------------------------------------------

    pub fn parse_statement(&mut self) -> Option<Statement> {
        // `import <universe_name>`
        if self.peek_kw("import") {
            self.tokens.next();
            let universe_name = match self.tokens.next() {
                Some(Token::Ident(n)) => n,
                _ => return None,
            };
            return Some(Statement::Import(universe_name));
        }

        // `Given <Name> : <Formula>`
        //
        // Parsed as a keyword arm before the generic Ident path so that
        // "Given" is never mistaken for a type/constant/predicate name.
        if self.peek_kw("Given") {
            self.tokens.next(); // consume `Given`
            let hyp_name = match self.tokens.next() {
                Some(Token::Ident(n)) => n,
                _ => return None,
            };
            if !self.consume_sym(":") { return None; }
            let formula = self.parse_formula()?;
            return Some(Statement::GivenDecl(hyp_name, formula));
        }

        let name = match self.tokens.peek() {
            Some(Token::Ident(n)) => n.clone(),
            _ => return None,
        };
        self.tokens.next();

        if !self.consume_sym(":") { return None; }

        // `Name : Type`
        if self.peek_kw("Type") {
            self.tokens.next();
            return Some(Statement::TypeDecl(name));
        }

        // `Name : forall ...`  or  `Name : ∀ ...`
        if self.peek_kw("forall") || self.peek_sym("∀") {
            return self.parse_forall_axiom(name);
        }

        // `Name : Prop`
        if self.peek_kw("Prop") {
            self.tokens.next();
            return Some(Statement::PredDecl(name, vec![], Sort::prop()));
        }

        // `Name : SortA -> SortB -> Prop`  or  `Name : SomeConcreteSort`
        //
        // We collect one or more sorts separated by `→`.
        // • If there is more than one sort, the last is the return sort of a
        //   predicate/function declaration → `PredDecl`.
        // • If there is exactly one sort and it is `"Type"`, the name is itself
        //   being declared as a new type → `TypeDecl`.
        // • If there is exactly one sort and it is anything else (e.g. `Pt`,
        //   `Line`), the name is a ground constant of that sort → `ConstDecl`.
        if let Some(Token::Ident(_)) = self.tokens.peek() {
            let mut sorts: Vec<Sort> = Vec::new();
            loop {
                let s = self.parse_sort()?;
                sorts.push(s);
                if self.peek_sym("→") { self.tokens.next(); continue; }
                break;
            }
            if sorts.len() > 1 {
                let ret = sorts.pop().unwrap();
                return Some(Statement::PredDecl(name, sorts, ret));
            }
            // Exactly one sort.
            let sole = sorts.remove(0);
            if sole == Sort(String::from("Type")) {
                return Some(Statement::TypeDecl(name));
            }
            return Some(Statement::ConstDecl(name, sole));
        }

        // `Name :` followed by anything else is malformed.
        None
    }

    /// Parse `forall v1 v2 ... : Sort, <formula>`.
    fn parse_forall_axiom(&mut self, name: String) -> Option<Statement> {
        self.tokens.next(); // consume `forall` / `∀`

        let mut var_names = Vec::new();

        while let Some(Token::Ident(v)) = self.tokens.peek() {
            var_names.push(v.clone());
            self.tokens.next();
        }

        if var_names.is_empty() { return None; }
        if !self.consume_sym(":") { return None; }
        let sort = self.parse_sort()?;
        if !self.consume_sym(",") { return None; }

        // Each binder receives its own identity, even when it shadows an
        // outer variable with the same spelling.
        let mut identities = Vec::with_capacity(var_names.len());
        let mut previous_sorts = Vec::with_capacity(var_names.len());
        for display_name in &var_names {
            let identity = fresh_variable_key(display_name);
            let previous = self.variable_sorts.insert(
                display_name.clone(),
                (identity.clone(), sort.clone()),
            );
            identities.push((identity, sort.clone()));
            previous_sorts.push((display_name.clone(), previous));
        }

        let body = self.parse_formula();

        for (display_name, previous) in previous_sorts {
            match previous {
                Some(previous_binding) => { self.variable_sorts.insert(display_name, previous_binding); }
                None => { self.variable_sorts.remove(&display_name); }
            }
        }

        let body = body?;
        let vars = identities;

        Some(Statement::AxiomDecl { name, vars, body })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::{Formula, Sort, Statement, Term};
    use crate::engine::Universe;

    #[test]
    fn forall_preserves_variable_sort() {
        let universe = Universe::new();
        let tokens = lex("OnLine : forall p : Point, On(p)");
        let mut parser = Parser::with_universe(tokens, Some(&universe));

        let statement = parser.parse_statement().unwrap();

        match statement {
            Statement::AxiomDecl { vars, body, .. } => {
                assert_eq!(vars.len(), 1);
                assert_eq!(crate::ast::variable_display_name(&vars[0].0), "p");

                match body {
                    Formula::Pred(_, args) => {
                        assert_eq!(
                            args[0],
                            Term::Var(vars[0].0.clone(), Sort("Point".to_string()))
                        );
                    }
                    _ => panic!("Expected predicate"),
                }
            }
            _ => panic!("Expected axiom declaration"),
        }
    }

    #[test]
    fn exists_preserves_variable_sort() {
        let universe = Universe::new();
        let tokens = lex("exists x : Point, On(x)");
        let mut parser = Parser::with_universe(tokens, Some(&universe));

        let formula = parser.parse_formula().unwrap();

        match formula {
            Formula::Exists { var, sort, body } => {
                assert_eq!(crate::ast::variable_display_name(&var), "x");
                assert_eq!(sort, Sort("Point".to_string()));

                match *body {
                    Formula::Pred(_, args) => {
                        assert_eq!(
                            args[0],
                            Term::Var(var.clone(), Sort("Point".to_string()))
                        );
                    }
                    _ => panic!("Expected predicate"),
                }
            }
            _ => panic!("Expected existential"),
        }
    }

    #[test]
    fn quantified_variable_shadows_constant() {
        let mut universe = Universe::new();
        universe.add_constant("p".to_string(), Sort("Line".to_string()));

        let tokens = lex("Rule : forall p : Point, On(p)");
        let mut parser = Parser::with_universe(tokens, Some(&universe));

        let statement = parser.parse_statement().unwrap();

        match statement {
            Statement::AxiomDecl { body, .. } => {
                match body {
                    Formula::Pred(_, args) => {
                        let Term::Var(identity, sort) = &args[0] else { panic!("Expected scoped variable"); };
                        assert_eq!(crate::ast::variable_display_name(identity), "p");
                        assert_eq!(sort, &Sort("Point".to_string()));
                    }
                    _ => panic!("Expected predicate"),
                }
            }
            _ => panic!("Expected axiom declaration"),
        }
    }

    #[test]
    fn nested_same_name_binders_have_distinct_identities() {
        let mut parser = Parser::with_universe(
            lex("exists x : Point, (P(x) & exists x : Line, Q(x))"),
            None,
        );
        let formula = parser.parse_formula_complete().unwrap();
        let Formula::Exists { var: outer, body, .. } = formula else { panic!("outer exists"); };
        let Formula::And(left, right) = *body else { panic!("conjunction"); };
        let Formula::Exists { var: inner, body: inner_body, .. } = *right else { panic!("inner exists"); };
        let Formula::Pred(_, outer_args) = *left else { panic!("outer predicate"); };
        let Formula::Pred(_, inner_args) = *inner_body else { panic!("inner predicate"); };
        let Term::Var(outer_use, _) = &outer_args[0] else { panic!("outer variable"); };
        let Term::Var(inner_use, _) = &inner_args[0] else { panic!("inner variable"); };
        assert_eq!(&outer, outer_use);
        assert_eq!(&inner, inner_use);
        assert_ne!(outer, inner);
    }

    #[test]
    fn repeated_free_variable_occurrences_share_identity() {
        let mut parser = Parser::with_universe(lex("P(x) & Q(x)"), None);
        let formula = parser.parse_formula_complete().unwrap();
        let Formula::And(left, right) = formula else { panic!("conjunction"); };
        let Formula::Pred(_, left_args) = *left else { panic!("left predicate"); };
        let Formula::Pred(_, right_args) = *right else { panic!("right predicate"); };
        assert_eq!(left_args[0], right_args[0]);
    }

    #[test]
    fn same_spelling_in_separate_parse_scopes_is_not_same_variable() {
        let mut first = Parser::with_universe(lex("P(x)"), None);
        let mut second = Parser::with_universe(lex("P(x)"), None);
        let first = first.parse_formula_complete().unwrap();
        let second = second.parse_formula_complete().unwrap();
        assert_ne!(first, second);
        assert!(first.unify(&second).is_none());
    }

    #[test]
    fn parsed_quantifiers_are_alpha_equivalent_despite_distinct_ids() {
        let mut first = Parser::with_universe(lex("exists x : Point, P(x)"), None);
        let mut second = Parser::with_universe(lex("exists y : Point, P(y)"), None);
        let first = first.parse_formula_complete().unwrap();
        let second = second.parse_formula_complete().unwrap();
        assert_ne!(first, second);
        assert!(first.unify(&second).is_some());
    }

}
