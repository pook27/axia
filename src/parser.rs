use crate::ast::{Term, Formula, Statement, Sort};
use crate::engine::Universe;
use std::iter::Peekable;
use std::vec::IntoIter;

// ---------------------------------------------------------------------------
// Tokens
// ---------------------------------------------------------------------------

#[derive(Debug, Clone, PartialEq)]
pub enum Token {
    Ident(String),
    Symbol(String),
    Keyword(String),
}

pub fn lex(input: &str) -> Vec<Token> {
    let mut tokens = Vec::new();
    let mut chars = input.chars().peekable();

    while let Some(&c) = chars.peek() {
        match c {
            ' ' | '\t' | '\n' | '\r' => { chars.next(); }

            // Single-character symbols — including ∃ which is now a first-class
            // quantifier in formulas (not just in axiom headers).
            '(' | ')' | ':' | ',' | '∀' | '∃' | '∧' | '→' | '=' | '∨' | '¬' | '!' | '|' => {
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
                }
            }

            _ if c.is_alphanumeric() || c == '_' => {
                let mut s = String::new();
                while let Some(&x) = chars.peek() {
                    if x.is_alphanumeric() || x == '_' { s.push(x); chars.next(); } else { break; }
                }
                match s.as_str() {
                    "class" | "where" | "Type" | "Prop" | "forall" | "exists" | "import"
                        => tokens.push(Token::Keyword(s)),
                    "and" => tokens.push(Token::Symbol("∧".to_string())),
                    "or"  => tokens.push(Token::Symbol("∨".to_string())),
                    "not" => tokens.push(Token::Symbol("¬".to_string())),
                    _     => tokens.push(Token::Ident(s)),
                }
            }

            _ => { chars.next(); }
        }
    }
    tokens
}

// ---------------------------------------------------------------------------
// Parser
// ---------------------------------------------------------------------------

pub struct Parser<'a> {
    tokens:   Peekable<IntoIter<Token>>,
    /// Optional reference to the active Universe.  When present the parser
    /// uses it to resolve identifiers: names found in `universe.constants`
    /// become `Term::Const`, everything else remains `Term::Var`.
    universe: Option<&'a Universe>,
}

impl<'a> Parser<'a> {
    /// Create a parser with access to the active universe for constant lookup.
    pub fn with_universe(tokens: Vec<Token>, universe: Option<&'a Universe>) -> Self {
        Parser { tokens: tokens.into_iter().peekable(), universe }
    }

    /// Resolve a bare identifier to either `Term::Const` (if it is registered
    /// in the universe's constant table) or `Term::Var` (otherwise).
    fn ident_to_term(&self, name: String) -> Term {
        if let Some(u) = self.universe {
            if u.constants.contains_key(&name) {
                return Term::Const(name);
            }
        }
        Term::Var(name, Sort::object())
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

    /// Consume a sort identifier.  Returns `Sort::object()` on failure.
    fn parse_sort(&mut self) -> Sort {
        match self.tokens.peek() {
            Some(Token::Keyword(k)) if k == "Type" || k == "Prop" => {
                let k = k.clone();
                self.tokens.next();
                Sort(k)
            }
            Some(Token::Ident(n)) => {
                let n = n.clone();
                self.tokens.next();
                Sort(n)
            }
            _ => Sort::object(),
        }
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

        // Variable name
        let var = match self.tokens.next() {
            Some(Token::Ident(v)) => v,
            _ => return None,
        };

        // Optional `: Sort`
        let sort = if self.peek_sym(":") {
            self.tokens.next();
            self.parse_sort()
        } else {
            Sort::object()
        };

        // Mandatory `,`
        if !self.consume_sym(",") { return None; }

        // Body — parsed as a full formula so quantifiers can nest
        let body = self.parse_formula()?;

        Some(Formula::Exists { var, sort, body: Box::new(body) })
    }

    fn parse_atom(&mut self) -> Option<Formula> {
        // Parenthesised formula
        if self.peek_sym("(") {
            self.tokens.next();
            let f = self.parse_formula()?;
            self.consume_sym(")");
            return Some(f);
        }

        // Must start with an identifier
        let name = match self.tokens.next() {
            Some(Token::Ident(s)) => s,
            _ => return None,
        };

        let mut args: Vec<Term> = Vec::new();
        let mut is_call = false;

        if self.peek_sym("(") {
            is_call = true;
            self.tokens.next();
            while let Some(t) = self.parse_term() {
                args.push(t);
                if self.peek_sym(",") { self.tokens.next(); continue; }
                break;
            }
            self.consume_sym(")");
        }

        // Equality: `name = rhs` or `f(...) = rhs`
        if self.peek_sym("=") {
            self.tokens.next();
            let lhs = if is_call {
                Term::Apply(name, args)
            } else {
                self.ident_to_term(name)
            };
            let rhs = self.parse_term()?;
            return Some(Formula::Eq(lhs, rhs));
        }

        if is_call {
            return Some(Formula::Pred(name, args));
        }

        // Juxtaposition-style predicate: `Pred x y`
        while let Some(Token::Ident(_)) = self.tokens.peek() {
            if let Some(t) = self.parse_term() { args.push(t); }
        }
        Some(Formula::Pred(name, args))
    }

    // ------------------------------------------------------------------
    // Term parsing
    // ------------------------------------------------------------------

    pub fn parse_term(&mut self) -> Option<Term> {
        let name = match self.tokens.next() {
            Some(Token::Ident(s)) => s,
            _ => return None,
        };

        if self.peek_sym("(") {
            self.tokens.next();
            let mut args = Vec::new();
            while let Some(arg) = self.parse_term() {
                args.push(arg);
                if self.peek_sym(",") { self.tokens.next(); continue; }
                break;
            }
            self.consume_sym(")");
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
                let s = self.parse_sort();
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

        while self.tokens.next().is_some() {}
        Some(Statement::PredDecl(name, vec![], Sort::object()))
    }

    /// Parse `forall v1 v2 ... : Sort, <formula>`.
    fn parse_forall_axiom(&mut self, name: String) -> Option<Statement> {
        self.tokens.next(); // consume `forall` / `∀`

        let mut var_names: Vec<String> = Vec::new();
        while let Some(Token::Ident(v)) = self.tokens.peek() {
            var_names.push(v.clone());
            self.tokens.next();
        }

        self.consume_sym(":");
        let sort = self.parse_sort();
        self.consume_sym(",");
        let body = self.parse_formula()?;

        let vars: Vec<(String, Sort)> = var_names
            .into_iter()
            .map(|v| (v, sort.clone()))
            .collect();

        Some(Statement::AxiomDecl { name, vars, body })
    }
}
