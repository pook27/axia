mod ast;
mod parser;
mod engine;

use std::fs::File;
use std::io::{BufRead, BufReader};
use std::collections::HashMap;
use rustyline::error::ReadlineError;
use rustyline::DefaultEditor;
use parser::{lex, Parser};
use ast::{Statement, Formula, Sort};
use engine::{Axiom, Universe, ProofStep, prove};

// ---------------------------------------------------------------------------
// Session — named universes + active cursor
// ---------------------------------------------------------------------------

struct Session {
    universes: HashMap<String, Universe>,
    active:    String,
}

impl Session {
    fn new() -> Self {
        let mut universes = HashMap::new();
        universes.insert("default".to_string(), Universe::new());
        Session { universes, active: "default".to_string() }
    }

    fn current(&self) -> &Universe {
        self.universes.get(&self.active).expect("active universe missing")
    }

    fn current_mut(&mut self) -> &mut Universe {
        self.universes.get_mut(&self.active).expect("active universe missing")
    }

    fn create_universe(&mut self, name: &str) -> bool {
        if self.universes.contains_key(name) { return false; }
        self.universes.insert(name.to_string(), Universe::new());
        true
    }

    fn use_universe(&mut self, name: &str) -> bool {
        if self.universes.contains_key(name) { self.active = name.to_string(); true } else { false }
    }

    fn import_universe(&mut self, src_name: &str) -> Result<usize, String> {
        if src_name == self.active {
            return Err("Cannot import a universe into itself.".to_string());
        }
        let src = self.universes.get(src_name)
            .ok_or_else(|| format!("Universe '{}' not found.", src_name))?
            .clone();
        let before = self.current().axioms.len();
        self.current_mut().import_from(&src);
        let after = self.current().axioms.len();
        Ok(after - before)
    }
}

// ---------------------------------------------------------------------------
// Axiom helpers
// ---------------------------------------------------------------------------

/// Decompose a formula into axiom(s) and add them to the universe.
///
/// * Conjunctions are split into two sibling axioms (suffixed `_L` / `_R`).
/// * Implications are flattened: premises are collected into the `premises`
///   list and the final consequent becomes the `conclusion`.
/// * Existentials and atomic formulas are stored as zero-premise axioms
///   whose conclusion is the formula itself; the engine handles the
///   existential reduction at search time.
fn add_axiom(name: String, vars: Vec<String>, formula: Formula, universe: &mut Universe) {
    match formula {
        Formula::And(left, right) => {
            add_axiom(format!("{}_L", name), vars.clone(), *left,  universe);
            add_axiom(format!("{}_R", name), vars,         *right, universe);
        }
        Formula::Implies(premise, conclusion) => {
            let mut premises = vec![*premise];
            let mut current  = *conclusion;
            while let Formula::Implies(p, c) = current {
                premises.push(*p);
                current = *c;
            }
            universe.add_axiom(Axiom { name, vars, premises, conclusion: current });
        }
        // Existentials and ground facts are stored with no premises so
        // the engine can handle them directly during proof search.
        other => {
            universe.add_axiom(Axiom { name, vars, premises: vec![], conclusion: other });
        }
    }
}

// ---------------------------------------------------------------------------
// Generic Proof Formatter
// ---------------------------------------------------------------------------

const ALIAS_THRESHOLD: usize = 12;

struct ProofFormatter {
    /// Maps raw `Display` string of a long Apply term → short alias.
    aliases:     HashMap<String, String>,
    /// Preamble "Let A = …" lines to print before the proof narrative.
    definitions: Vec<String>,
    counter:     usize,
}

impl ProofFormatter {
    fn new() -> Self {
        ProofFormatter { aliases: HashMap::new(), definitions: Vec::new(), counter: 0 }
    }

    // ------------------------------------------------------------------
    // Pass 1: scan the proof tree and register term aliases
    // ------------------------------------------------------------------

    fn scan(&mut self, step: &ProofStep) {
        self.scan_formula(&step.goal);
        // Also scan witness terms so constructions get aliased if long.
        for (_, term) in &step.witnesses {
            self.scan_term(term);
        }
        for sub in &step.sub_proofs { self.scan(sub); }
    }

    fn scan_formula(&mut self, f: &Formula) {
        match f {
            Formula::Eq(l, r)      => { self.scan_term(l); self.scan_term(r); }
            Formula::Pred(_, args) => args.iter().for_each(|a| self.scan_term(a)),
            Formula::And(l, r) | Formula::Or(l, r) | Formula::Implies(l, r) => {
                self.scan_formula(l); self.scan_formula(r);
            }
            Formula::Not(i)        => self.scan_formula(i),
            Formula::Exists { body, .. } => self.scan_formula(body),
        }
    }

    fn scan_term(&mut self, t: &ast::Term) {
        if let ast::Term::Apply(_, args) = t {
            for a in args { self.scan_term(a); }
            let raw = format!("{}", t);
            if raw.len() > ALIAS_THRESHOLD && !self.aliases.contains_key(&raw) {
                self.counter += 1;
                let alias = format!("X{}", self.counter); // Start at X1, X2...
                self.definitions.push(format!("Let {} = {}.", alias, self.fmt_term_raw(t)));
                self.aliases.insert(raw, alias);
            }
        }
    }

    // ------------------------------------------------------------------
    // Pass 2: format terms and formulas
    // ------------------------------------------------------------------

    fn fmt_term(&self, t: &ast::Term) -> String {
        let raw = format!("{}", t);
        if let Some(alias) = self.aliases.get(&raw) { return alias.clone(); }
        self.fmt_term_raw(t)
    }

    fn fmt_term_raw(&self, t: &ast::Term) -> String {
        match t {
            ast::Term::Var(name, sort) if sort != &Sort::object() => format!("{}:{}", name, sort),
            ast::Term::Var(name, _)  => name.clone(),
            ast::Term::Const(name)   => name.clone(),
            ast::Term::Apply(name, args) => {
                let fa: Vec<String> = args.iter().map(|a| self.fmt_term(a)).collect();
                format!("{}({})", name, fa.join(", "))
            }
        }
    }

    fn fmt_formula(&self, f: &Formula) -> String {
        match f {
            Formula::Eq(l, r) =>
                format!("{} = {}", self.fmt_term(l), self.fmt_term(r)),
            Formula::Pred(name, args) => {
                if args.is_empty() { name.clone() }
                else {
                    let fa: Vec<String> = args.iter().map(|a| self.fmt_term(a)).collect();
                    format!("{}({})", name, fa.join(", "))
                }
            }
            Formula::And(l, r) =>
                format!("{} AND {}", self.fmt_formula(l), self.fmt_formula(r)),
            Formula::Or(l, r) =>
                format!("{} OR {}",  self.fmt_formula(l), self.fmt_formula(r)),
            Formula::Not(i) =>
                format!("NOT {}", self.fmt_formula(i)),
            Formula::Implies(l, r) =>
                format!("IF {} THEN {}", self.fmt_formula(l), self.fmt_formula(r)),
            Formula::Exists { var, sort, body } => {
                let body_str = self.fmt_formula(body);
                if sort == &Sort::object() {
                    format!("∃ {}, {}", var, body_str)
                } else {
                    format!("∃ {} : {}, {}", var, sort, body_str)
                }
            }
        }
    }

    /// Strip `_L` / `_R` suffixes and replace underscores with spaces.
    fn clean_rule_name(raw: &str) -> String {
        let stripped = raw.strip_suffix("_L")
            .or_else(|| raw.strip_suffix("_R"))
            .unwrap_or(raw);
        stripped.replace('_', " ")
    }
}

// ---------------------------------------------------------------------------
// Proof explanation driver
// ---------------------------------------------------------------------------

fn explain_proof(step: &ProofStep) {
    let mut fmt = ProofFormatter::new();
    fmt.scan(step);

    println!("\n--- Q.E.D. ---");
    for def in &fmt.definitions { println!("{}", def); }
    if !fmt.definitions.is_empty() { println!(); }

    explain_recursive(step, 0, &fmt);
}

fn explain_recursive(step: &ProofStep, depth: usize, fmt: &ProofFormatter) {
    let indent = "  ".repeat(depth);
    let goal_text  = fmt.fmt_formula(&step.goal);
    let rule_label = ProofFormatter::clean_rule_name(&step.rule_name);

    if !step.witnesses.is_empty() {
        // Existential Instantiation step.
        //
        // Print a "Construct …" line for each witness, then narrate the
        // sub-proof that established the witness property.
        println!("{}To prove: {}", indent, goal_text);
        for (var, term) in &step.witnesses {
            let term_str = fmt.fmt_term(term);
            // Distinguish between a resolved construction and a bare Skolem
            // that remained unbound (i.e. proved abstractly).
            let is_abstract = matches!(term, ast::Term::Var(n, _) if n.starts_with("?w"));
            if is_abstract {
                println!("{}Witness: introduce {} as an abstract object.", indent, var);
            } else {
                println!("{}Construct {} as {}.", indent, var, term_str);
            }
        }
        for sub in &step.sub_proofs { explain_recursive(sub, depth + 1, fmt); }

    } else if step.sub_proofs.is_empty() {
        // Leaf node
        if step.rule_name.starts_with("Fact") || step.rule_name == "Given" {
            println!("{}Given: {}.", indent, goal_text);
        } else {
            println!("{}By {}, {}.", indent, rule_label, goal_text);
        }
    } else if step.rule_name == "Conjunction" {
        println!("{}To prove {}, we show both parts:", indent, goal_text);
        for sub in &step.sub_proofs { explain_recursive(sub, depth + 1, fmt); }
    } else {
        println!("{}Goal: {}.", indent, goal_text);
        println!("{}Strategy: Apply {}.", indent, rule_label);
        for sub in &step.sub_proofs { explain_recursive(sub, depth + 1, fmt); }
    }

    if depth == 0 { println!("\nTherefore, the proof is complete."); }
}

// ---------------------------------------------------------------------------
// Help text
// ---------------------------------------------------------------------------

fn print_help() {
    println!("Commands:");
    println!("  create_universe <name>              Create a new empty universe");
    println!("  use <name>                          Switch active universe");
    println!("  list_universes                      List all universes");
    println!("  universe_info                       Show contents of active universe");
    println!("  import <name>                       Pull axioms from another universe into active");
    println!("  load <file>                         Load a .axia file into active universe");
    println!("  load <file> into <universe>         Load a file into a specific universe");
    println!("  assert <formula>                    Add a ground fact to active universe");
    println!("  prove <formula>                     Prove a formula in active universe");
    println!("  exit                                Quit");
    println!();
    println!("Formula syntax:");
    println!("  P(x, y)          predicate application");
    println!("  f(x) = g(y)      equality");
    println!("  A ∧ B  / A and B conjunctions");
    println!("  A ∨ B  / A or B  disjunctions");
    println!("  A → B  / A -> B  implication");
    println!("  ¬ A    / not A   negation");
    println!("  ∃ x, P(x)        existential (engine introduces Skolem witness)");
    println!("  ∃ x : Sort, P(x) existential with sort annotation");
}

// ---------------------------------------------------------------------------
// CLI command processing
// ---------------------------------------------------------------------------

fn process_line(input: &str, session: &mut Session) {
    let trimmed = input.trim();
    if trimmed.is_empty() || trimmed.starts_with("--") { return; }

    if trimmed == "help" || trimmed == "?" { print_help(); return; }

    // -----------------------------------------------------------------------
    // Universe management
    // -----------------------------------------------------------------------

    if let Some(rest) = trimmed.strip_prefix("create_universe ") {
        let name = rest.trim();
        if name.is_empty() { println!("Usage: create_universe <name>"); return; }
        if session.create_universe(name) {
            println!("Universe '{}' created.", name);
        } else {
            println!("Universe '{}' already exists.", name);
        }
        return;
    }

    if let Some(rest) = trimmed.strip_prefix("use ") {
        let name = rest.trim();
        if session.use_universe(name) {
            println!("Switched to universe '{}'.", name);
        } else {
            println!("Error: Universe '{}' does not exist. Use `create_universe {}` first.", name, name);
        }
        return;
    }

    if trimmed == "list_universes" {
        let mut names: Vec<&String> = session.universes.keys().collect();
        names.sort();
        for name in names {
            let marker = if name == &session.active { " [active]" } else { "" };
            println!("  {}{} — {}", name, marker, session.universes[name].summary());
        }
        return;
    }

    if trimmed == "universe_info" {
        let u = session.current();
        println!("Active universe: '{}'", session.active);
        let types_str = if u.types.is_empty() { "(none)".to_string() } else { u.types.join(", ") };
        let preds_str = if u.predicates.is_empty() {
            "(none)".to_string()
        } else {
            u.predicates.keys().cloned().collect::<Vec<_>>().join(", ")
        };
        let consts_str = if u.constants.is_empty() {
            "(none)".to_string()
        } else {
            let mut pairs: Vec<String> = u.constants
                .iter()
                .map(|(n, s)| format!("{} : {}", n, s))
                .collect();
            pairs.sort();
            pairs.join(", ")
        };
        println!("  Types      : {}", types_str);
        println!("  Constants  : {}", consts_str);
        println!("  Predicates : {}", preds_str);
        println!("  Axioms ({}):", u.axioms.len());
        for ax in &u.axioms {
            if ax.premises.is_empty() {
                println!("    [{}] ⊢ {}", ax.name, ax.conclusion);
            } else {
                let prems: Vec<String> = ax.premises.iter().map(|p| format!("{}", p)).collect();
                println!("    [{}] {} ⊢ {}", ax.name, prems.join(", "), ax.conclusion);
            }
        }
        return;
    }

    if let Some(rest) = trimmed.strip_prefix("import ") {
        let src = rest.trim();
        match session.import_universe(src) {
            Ok(n)    => println!("Imported {} new axiom(s) from '{}' into '{}'.", n, src, session.active),
            Err(msg) => println!("Error: {}", msg),
        }
        return;
    }

    // -----------------------------------------------------------------------
    // load <file> [into <universe>]
    // -----------------------------------------------------------------------

    if let Some(rest) = trimmed.strip_prefix("load ") {
        let (filename, target) = if let Some(pos) = rest.rfind(" into ") {
            (rest[..pos].trim(), Some(rest[pos + 6..].trim().to_string()))
        } else {
            (rest.trim(), None)
        };

        let target_name = match &target {
            Some(name) => {
                if !session.universes.contains_key(name.as_str()) {
                    println!("Error: Universe '{}' does not exist. Create it first.", name);
                    return;
                }
                name.clone()
            }
            None => session.active.clone(),
        };

        println!("Loading '{}' into universe '{}'…", filename, target_name);
        match File::open(filename) {
            Ok(file) => {
                let reader = BufReader::new(file);
                let previous_active = session.active.clone();
                session.active = target_name.clone();
                for line in reader.lines().flatten() { process_line(&line, session); }
                session.active = previous_active;
                println!("Done. '{}' now has {}.", target_name, session.universes[&target_name].summary());
            }
            Err(_) => println!("Error: Could not open file '{}'.", filename),
        }
        return;
    }

    // -----------------------------------------------------------------------
    // prove <formula>
    // -----------------------------------------------------------------------

    if let Some(goal_str) = trimmed.strip_prefix("prove ") {
        let tokens = lex(goal_str.trim());
        let mut parser = Parser::with_universe(tokens, Some(session.current()));
        match parser.parse_formula() {
            Some(goal) => {
                println!("Goal: {}  [universe: '{}']", goal, session.active);
                match prove(&goal, session.current(), 10) {
                    Some(proof) => explain_proof(&proof),
                    None        => println!("No proof found."),
                }
            }
            None => println!("Could not parse goal."),
        }
        return;
    }

    // -----------------------------------------------------------------------
    // assert <formula>
    // -----------------------------------------------------------------------

    if let Some(fact_str) = trimmed.strip_prefix("assert ") {
        let tokens = lex(fact_str.trim());
        let mut parser = Parser::with_universe(tokens, Some(session.current()));
        match parser.parse_formula() {
            Some(f) => {
                session.current_mut().add_axiom(Axiom {
                    name:       "Fact".to_string(),
                    vars:       vec![],
                    premises:   vec![],
                    conclusion: f,
                });
                println!("Fact added to universe '{}'.", session.active);
            }
            None => println!("Could not parse fact."),
        }
        return;
    }

    // -----------------------------------------------------------------------
    // Bare declaration (TypeDecl / ConstDecl / PredDecl / AxiomDecl / Import)
    // -----------------------------------------------------------------------

    let tokens = lex(trimmed);
    let mut parser = Parser::with_universe(tokens, Some(session.current()));
    match parser.parse_statement() {
        Some(Statement::TypeDecl(n)) => {
            session.current_mut().add_type(n.clone());
            println!("Defined Type: {}", n);
        }
        Some(Statement::ConstDecl(n, sort)) => {
            session.current_mut().add_constant(n.clone(), sort.clone());
            println!("Defined Constant: {} : {}", n, sort);
        }
        Some(Statement::PredDecl(n, arg_sorts, ret_sort)) => {
            let arg_strs: Vec<String> = arg_sorts.iter().map(|s| s.to_string()).collect();
            session.current_mut().add_predicate(n.clone(), arg_strs, ret_sort.to_string());
            if arg_sorts.is_empty() {
                println!("Defined Predicate/Relation: {}", n);
            } else {
                let sig: Vec<String> = arg_sorts.iter().map(|s| s.to_string()).collect();
                println!("Defined Function/Predicate: {} : {} → {}", n, sig.join(" → "), ret_sort);
            }
        }
        Some(Statement::AxiomDecl { name, vars, body }) => {
            let var_strs: Vec<String> = vars
                .iter()
                .map(|(v, s)| if s == &Sort::object() { v.clone() } else { format!("{}:{}", v, s) })
                .collect();
            let vars_pure: Vec<String> = vars.into_iter().map(|(n, _)| n).collect();
            add_axiom(name.clone(), vars_pure, body, session.current_mut());
            if var_strs.is_empty() {
                println!("Added Axiom: {}", name);
            } else {
                println!("Added Axiom: {} [∀ {}]", name, var_strs.join(", "));
            }
        }
        Some(Statement::Import(src)) => {
            match session.import_universe(&src) {
                Ok(n)    => println!("Imported {} new axiom(s) from '{}'.", n, src),
                Err(msg) => println!("Error: {}", msg),
            }
        }
        Some(Statement::Goal(_)) => println!("Goal declared."),
        None => println!("Parse error: {}", trimmed),
    }
}

// ---------------------------------------------------------------------------
// Entry point
// ---------------------------------------------------------------------------

fn main() {
    let mut session = Session::new();
    let mut rl = DefaultEditor::new().expect("Failed to init readline");

    println!("--- Axia Kernel v0.8 ---");
    println!("Active universe: 'default'  |  type `help` for commands");

    loop {
        let prompt = format!("[{}]> ", session.active);
        match rl.readline(&prompt) {
            Ok(line) => {
                let _ = rl.add_history_entry(line.as_str());
                let t = line.trim();
                if t == "exit" { break; }
                process_line(&line, &mut session);
            }
            Err(ReadlineError::Interrupted) | Err(ReadlineError::Eof) => break,
            Err(e) => { eprintln!("Error: {:?}", e); break; }
        }
    }
}
