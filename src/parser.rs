use crate::ast::{Term, Formula, Statement};
use std::iter::Peekable;
use std::vec::IntoIter;

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
            '(' | ')' | ':' | ',' | '∀' | '∃' | '∧' | '→' | '=' => {
                tokens.push(Token::Symbol(c.to_string()));
                chars.next();
            },
            '-' => {
                chars.next();
                if let Some(&'>') = chars.peek() {
                    chars.next();
                    tokens.push(Token::Symbol("→".to_string()));
                } else if let Some(&'-') = chars.peek() {
                    while let Some(&x) = chars.peek() {
                        if x == '\n' { break; }
                        chars.next();
                    }
                }
            },
            _ if c.is_alphanumeric() || c == '_' => {
                let mut s = String::new();
                while let Some(&x) = chars.peek() {
                    if x.is_alphanumeric() || x == '_' { s.push(x); chars.next(); } else { break; }
                }
                match s.as_str() {
                    "class" | "where" | "Type" | "Prop" | "forall" | "exists" => tokens.push(Token::Keyword(s)),
                    "and" => tokens.push(Token::Symbol("∧".to_string())),
                    _ => tokens.push(Token::Ident(s)),
                }
            },
            _ => { chars.next(); }
        }
    }
    tokens
}

pub struct Parser {
    tokens: Peekable<IntoIter<Token>>,
}

impl Parser {
    pub fn new(tokens: Vec<Token>) -> Self {
        Parser { tokens: tokens.into_iter().peekable() }
    }

    fn consume(&mut self, expected: &str) -> bool {
        if let Some(Token::Symbol(s)) = self.tokens.peek() {
            if s == expected { self.tokens.next(); return true; }
        }
        false
    }

    pub fn parse_statement(&mut self) -> Option<Statement> {
        let name = match self.tokens.peek() {
            Some(Token::Ident(n)) => n.clone(),
            Some(Token::Keyword(k)) if k == "class" => return Some(Statement::TypeDecl("Context".to_string())),
            _ => return None,
        };
        self.tokens.next(); // Eat name

        if !self.consume(":") { return None; }

        match self.tokens.peek() {
            Some(Token::Keyword(k)) if k == "Type" => {
                self.tokens.next();
                return Some(Statement::TypeDecl(name));
            },
            Some(Token::Keyword(k)) if k == "forall" => return self.parse_axiom(name),
            Some(Token::Symbol(s)) if s == "∀" || s == "forall" => return self.parse_axiom(name),
            _ => {}
        }

        while self.tokens.next().is_some() {} 
        Some(Statement::PredDecl(name, vec![]))
    }

    fn parse_axiom(&mut self, name: String) -> Option<Statement> {
        self.tokens.next();
        let mut vars = Vec::new();
        while let Some(Token::Ident(v)) = self.tokens.peek() {
            let v_name = v.clone();
            self.tokens.next();
            vars.push((v_name, "Object".to_string()));
        }
        self.consume(":");
        self.tokens.next();
        self.consume(",");

        let body = self.parse_formula()?;

        Some(Statement::AxiomDecl { name, vars, body })
    }

    pub fn parse_term(&mut self) -> Option<Term> {
        let name = match self.tokens.next() {
            Some(Token::Ident(s)) => s,
            _ => return None,
        };

        if let Some(Token::Symbol(s)) = self.tokens.peek() {
            if s == "(" {
                self.tokens.next(); // Eat '('
                let mut args = Vec::new();
                while let Some(arg) = self.parse_term() {
                    args.push(arg);
                    if let Some(Token::Symbol(c)) = self.tokens.peek() {
                        if c == "," { self.tokens.next(); continue; }
                    }
                    break;
                }
                self.consume(")");
                return Some(Term::Apply(name, args));
            }
        }
        Some(Term::Var(name))
    }

    pub fn parse_formula(&mut self) -> Option<Formula> {
        if let Some(Token::Symbol(s)) = self.tokens.peek() {
            if s == "(" {
                self.tokens.next(); // Eat '('
                let left = self.parse_formula()?;
                self.consume(")");

                if let Some(Token::Symbol(op)) = self.tokens.peek() {
                    if op == "∧" {
                        self.tokens.next();
                        self.consume("("); 
                        let right = self.parse_formula()?;
                        self.consume(")");
                        return Some(Formula::And(Box::new(left), Box::new(right)));
                    }
                }
                return Some(left);
            }
        }

        let start_token = self.tokens.next()?; 
        let name = match start_token {
            Token::Ident(s) => s,
            _ => return None,
        };

        if let Some(Token::Symbol(s)) = self.tokens.peek() {
            if s == "=" {
                self.tokens.next(); // Eat '='
                let lhs = Term::Var(name); // The first token was the LHS
                let rhs = self.parse_term()?; // Parse the RHS
                return Some(Formula::Eq(lhs, rhs));
            }
        }

        let mut args = Vec::new();
        if let Some(Token::Symbol(s)) = self.tokens.peek() {
            if s == "(" {
                self.tokens.next(); // Eat '('
                while let Some(t) = self.parse_term() {
                    args.push(t);
                    if let Some(Token::Symbol(c)) = self.tokens.peek() {
                        if c == "," { self.tokens.next(); continue; }
                    }
                    break;
                }
                self.consume(")");
                return Some(Formula::Pred(name, args));
            }
        }
        while let Some(Token::Ident(_)) = self.tokens.peek() {
            if let Some(t) = self.parse_term() {
                args.push(t);
            }
        }
        Some(Formula::Pred(name, args))
    }
}
