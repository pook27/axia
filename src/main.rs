mod ast;
mod parser;
mod engine;

use std::path::Path;
use std::fs::{self, File};

use std::io::{BufRead, BufReader};
use std::collections::HashMap;
use rustyline::error::ReadlineError;
use rustyline::DefaultEditor;
use parser::{lex, Parser};
use ast::{Statement, Formula, Sort};
use engine::{Axiom, Universe, ProofStep, prove, forward_deduce};
use colored::Colorize;
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

const ALIAS_THRESHOLD: usize = 50;

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
        if let Some(alias) = self.aliases.get(&raw) { 
            return alias.cyan().bold().to_string(); 
        }
        self.fmt_term_raw(t)
    }

    fn fmt_term_raw(&self, t: &ast::Term) -> String {
        let lp = "(".bright_black().bold();
        let rp = ")".bright_black().bold();

        // If the term is a chain of S(...) ending in 0, format it as a digit.
        let mut curr = t;
        let mut peano_val = 0;
        let mut is_peano = false;
        
        while let ast::Term::Apply(n, args) = curr {
            if n == "S" && args.len() == 1 {
                peano_val += 1;
                curr = &args[0];
            } else {
                break;
            }
        }
        if let ast::Term::Const(c) = curr {
            if c == "0" || c == "Z" {
                is_peano = true;
            }
        }
        
        if is_peano {
            return peano_val.to_string().cyan().bold().to_string();
        }
        // ----------------------------------
        
        match t {
            ast::Term::Var(name, sort) if sort != &Sort::object() => {
                format!("{}:{}", name.cyan().bold(), sort.to_string().cyan().bold())
            }
            ast::Term::Var(name, _)  => name.cyan().bold().to_string(),
            ast::Term::Const(name)   => name.cyan().bold().to_string(),
            ast::Term::Apply(name, args) => {
                let fa: Vec<String> = args.iter().map(|a| self.fmt_term(a)).collect();
                
                // Binary operators get bright blue syntax highlighting
                if args.len() == 2 {
                    let op = match name.as_str() {
                        "Add" => Some("+".bright_blue().bold()),
                        "Sub" => Some("-".bright_blue().bold()),
                        "Mul" => Some("*".bright_blue().bold()),
                        "Div" => Some("/".bright_blue().bold()),
                        _ => None,
                    };
                    if let Some(op_str) = op {
                        return format!("{} {} {}", fa[0], op_str, fa[1]);
                    }
                }
                
                format!("{}{}{}{}", name.cyan().bold(), lp, fa.join(", "), rp)
            }
        }
    }

    fn fmt_formula(&self, f: &Formula) -> String {
        let lp = "(".bright_black().bold();
        let rp = ")".bright_black().bold();
        let eq = "=".bright_blue().bold();
        
        match f {
            Formula::Eq(l, r) =>
                format!("{} {} {}", self.fmt_term(l), eq, self.fmt_term(r)),
            Formula::Pred(name, args) => {
                if args.is_empty() { name.cyan().bold().to_string() }
                else {
                    let fa: Vec<String> = args.iter().map(|a| self.fmt_term(a)).collect();
                    format!("{}{}{}{}", name.cyan().bold(), lp, fa.join(", "), rp)
                }
            }
            Formula::And(l, r) =>
                format!("{} {} {}", self.fmt_formula(l), "AND".magenta().bold(), self.fmt_formula(r)),
            Formula::Or(l, r) =>
                format!("{} {} {}", self.fmt_formula(l), "OR".magenta().bold(), self.fmt_formula(r)),
            Formula::Not(i) =>
                format!("{} {}", "NOT".magenta().bold(), self.fmt_formula(i)),
            Formula::Implies(l, r) =>
                format!("{} {} {} {}", "IF".magenta().bold(), self.fmt_formula(l), "THEN".magenta().bold(), self.fmt_formula(r)),
            Formula::Exists { var, sort, body } => {
                let body_str = self.fmt_formula(body);
                let e = "∃".magenta().bold();
                if sort == &Sort::object() {
                    format!("{} {}, {}", e, var.cyan().bold(), body_str)
                } else {
                    format!("{} {} : {}, {}", e, var.cyan().bold(), sort.to_string().cyan().bold(), body_str)
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

    println!("\n{}", "--- Q.E.D. ---".green().bold());
    for def in &fmt.definitions { println!("{}", def); }
    if !fmt.definitions.is_empty() { println!(); }

    explain_recursive(step, 0, &fmt);
}

fn explain_recursive(step: &ProofStep, depth: usize, fmt: &ProofFormatter) {
    // Dim the tree branches so they fade into the background
    let branch = if depth == 0 {
        String::new()
    } else {
        format!("{}└─ ", "   ".repeat(depth - 1)).bright_black().to_string()
    };
    
    // Colorize the components
    let turnstile = "⊢".magenta().bold();
    let goal_text = fmt.fmt_formula(&step.goal);
    let rule_label = ProofFormatter::clean_rule_name(&step.rule_name).yellow();

    if !step.witnesses.is_empty() {
        // Existential Instantiation step
        println!("{}Prove: {}", branch, goal_text);
        for (var, term) in &step.witnesses {
            let term_str = fmt.fmt_term(term).green().bold();
            let is_abstract = matches!(term, ast::Term::Var(n, _) if n.starts_with("?w"));
            let prefix = format!("{}   ", "   ".repeat(depth)).bright_black();
            
            if is_abstract {
                println!("{}↳ Let {} be an abstract variable.", prefix, var.bold());
            } else {
                println!("{}↳ Construct {} := {}", prefix, var.bold(), term_str);
            }
        }
        for sub in &step.sub_proofs { explain_recursive(sub, depth + 1, fmt); }

    } else if step.sub_proofs.is_empty() {
        // Base case — no sub-proofs: axiom/given/deduction leaf.
        if step.rule_name.starts_with("Given ") {
            // Named hypothesis or deduction used as a direct fact.
            let hyp = step.rule_name.strip_prefix("Given ").unwrap_or(&step.rule_name);
            println!("{}{} {} {}",
                branch,
                goal_text,
                "(by hypothesis".bright_black(),
                format!("{})", hyp).bright_black());
        } else if step.rule_name.starts_with("Fact") {
            println!("{}{} {}", branch, goal_text, "(asserted fact)".bright_black());
        } else {
            println!("{}{} (via {})", branch, goal_text, rule_label);
        }
    } else if step.rule_name == "Conjunction" {
        // Conjunctions
        println!("{}{} {}  {}", branch, turnstile, goal_text, "[Requires both:]".bright_black());
        for sub in &step.sub_proofs { explain_recursive(sub, depth + 1, fmt); }
    } else {
        // Standard implication step
        println!("{}{} {}  (apply {})", branch, turnstile, goal_text, rule_label);
        for sub in &step.sub_proofs { explain_recursive(sub, depth + 1, fmt); }
    }

    if depth == 0 { println!("\n{}", "Q.E.D.".green().bold()); }
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
    println!("  Given <Name> : <formula>            Declare a named hypothesis");
    println!("  deduce <n>                          Forward-chain for <n> saturation steps");
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

fn resolve_and_load(target: &str, session: &mut Session) -> Result<(), String> {
    // The "Search Paths" for the module resolver
    let possible_paths = vec![
        target.to_string(),
        format!("{}.axia", target),
        format!("lib/{}", target),
        format!("lib/{}.axia", target),
        format!("lib/core/{}", target),
        format!("lib/core/{}.axia", target),
        format!("lib/geometry/{}", target),
        format!("lib/geometry/{}.axia", target),
    ];

    let mut found_path = None;
    for p in &possible_paths {
        if Path::new(p).exists() {
            found_path = Some(p.clone());
            break;
        }
    }

    let path_str = found_path.ok_or_else(|| format!("Could not find library or module '{}'", target))?;
    let path = Path::new(&path_str);

    if path.is_dir() {
        // Module/Directory Loading: Load all .axia files in alphabetical order
        println!("Loading module package '{}'...", path_str);
        let mut entries: Vec<_> = fs::read_dir(path).unwrap().filter_map(Result::ok).collect();
        entries.sort_by_key(|e| e.path()); 
        
        for entry in entries {
            let p = entry.path();
            if p.is_file() && p.extension().unwrap_or_default() == "axia" {
                load_file(p.to_str().unwrap(), &session.active.clone(), session)?;
            }
        }
        Ok(())
    } else {
        // Single File Loading
        load_file(&path_str, &session.active.clone(), session)
    }
}

fn load_file(filename: &str, target_name: &str, session: &mut Session) -> Result<(), String> {
    let file = File::open(filename).map_err(|_| format!("Could not open file '{}'.", filename))?;
    let reader = BufReader::new(file);
    let previous_active = session.active.clone();
    session.active = target_name.to_string();
    
    for line_result in reader.lines() { 
        if let Ok(line) = line_result {
            process_line(&line, session); 
        }
    }
    
    session.active = previous_active;
    Ok(())
}

fn process_line(input: &str, session: &mut Session) {
    let trimmed = input.trim();
    if trimmed.is_empty() || trimmed.starts_with("--") { return; }

    if trimmed == "help" || trimmed == "?" { print_help(); return; }

    // -----------------------------------------------------------------------
    // Universe management
    // -----------------------------------------------------------------------

    if let Some(rest) = trimmed.strip_prefix("create_universe ") {
        let name = rest.trim();
        if name.is_empty() { println!("{}", "Usage: create_universe <name>".red()); return; }
        if session.create_universe(name) {
            println!("Universe '{}' created.", name.green().bold());
        } else {
            println!("{}", format!("Universe '{}' already exists.", name).yellow());
        }
        return;
    }

    if let Some(rest) = trimmed.strip_prefix("use ") {
        let name = rest.trim();
        if session.use_universe(name) {
            println!("Switched to universe '{}'.", name.green().bold());
        } else {
            println!("{}", format!("Error: Universe '{}' does not exist.", name).red());
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
        if !u.givens.is_empty() {
            println!("  Givens / Deductions ({}):", u.givens.len());
            let mut pairs: Vec<(&String, &Formula)> = u.givens.iter().collect();
            pairs.sort_by_key(|(n, _)| n.as_str());
            for (gname, gf) in pairs {
                println!("    [{}] {}", gname, gf);
            }
        }
        return;
    }

    if let Some(rest) = trimmed.strip_prefix("import ") {
        let src = rest.trim();
        let core_path = format!("lib/core/{}.axia", src);
        let geom_path = format!("lib/geometry/{}.axia", src);
        
        if load_file(&core_path, &session.active.clone(), session).is_ok() {
            // Success
        } else if load_file(&geom_path, &session.active.clone(), session).is_ok() {
            // Success
        } else {
            println!("Error: Could not find library '{}' in lib/core/ or lib/geometry/", src);
        }
        return;
    }

    // -----------------------------------------------------------------------
    // load <file> [into <universe>]
    // -----------------------------------------------------------------------

    if let Some(rest) = trimmed.strip_prefix("load ") {
        let target = rest.trim();
        match resolve_and_load(target, session) {
            Ok(_) => println!("Done. Module '{}' loaded.", target.green()),
            Err(e) => println!("{}", format!("Error: {}", e).red()),
        }
        return;
    }

    
    // prove <formula>
    // -----------------------------------------------------------------------

    if let Some(goal_str) = trimmed.strip_prefix("prove ") {
        let tokens = lex(goal_str.trim());
        let mut parser = Parser::with_universe(tokens, Some(session.current()));
        match parser.parse_formula() {
            Some(goal) => {
                println!("{} {}  [universe: '{}']", "Goal:".blue().bold(), goal.to_string().cyan(), session.active.yellow());
                match prove(&goal, session.current(), 20) {
                    Some(proof) => explain_proof(&proof),
                    None        => println!("{}", "No proof found.".red().bold()),
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
    // deduce <steps>
    //
    // Run the forward-chaining saturation loop for up to <steps> rounds,
    // applying every axiom whose premises are satisfied by existing givens
    // and recording the conclusions as new named deductions.
    // -----------------------------------------------------------------------

    if let Some(rest) = trimmed.strip_prefix("deduce") {
        // Accept both `deduce` (default 1 step) and `deduce <n>`.
        let steps: u32 = rest.trim().parse().unwrap_or(1).max(1);

        println!("{} {} {}",
            "Running forward deduction".blue().bold(),
            format!("({} step{})...", steps, if steps == 1 { "" } else { "s" }).bright_black(),
            format!("[universe: '{}']", session.active).yellow(),
        );

        let discoveries = forward_deduce(session.current_mut(), steps);

        if discoveries.is_empty() {
            println!("{}", "  No new facts discovered (fixpoint reached).".bright_black());
        } else {
            println!("{} {}",
                format!("  {} new fact{} discovered:", discoveries.len(),
                    if discoveries.len() == 1 { "" } else { "s" }).green().bold(),
                "".normal(),
            );
            for (name, formula) in &discoveries {
                println!("  {} {} : {}",
                    "◆".green(),
                    name.yellow().bold(),
                    formula.to_string().cyan(),
                );
            }
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
            println!("{} {}", "Defined Type:".yellow(), n.cyan().bold());
        }
        Some(Statement::ConstDecl(n, sort)) => {
            session.current_mut().add_constant(n.clone(), sort.clone());
            println!("{} {} : {}", "Defined Constant:".yellow(), n.cyan().bold(), sort.to_string().cyan());
        }
        Some(Statement::PredDecl(n, arg_sorts, ret_sort)) => {
            let arg_strs: Vec<String> = arg_sorts.iter().map(|s| s.to_string()).collect();
            session.current_mut().add_predicate(n.clone(), arg_strs, ret_sort.0.clone());
            
            let sig: Vec<String> = arg_sorts.iter().map(|s| s.to_string()).collect();
            let sig_str = if sig.is_empty() { "".to_string() } else { format!(" : {} → ", sig.join(" → ")) };
            println!("{} {}{}{}", "Defined Function/Predicate:".yellow(), n.cyan().bold(), sig_str, ret_sort.to_string().cyan());
        }
        Some(Statement::AxiomDecl { name, vars, body }) => {
            let vars_pure: Vec<String> = vars.iter().map(|(n, _)| n.clone()).collect();
            add_axiom(name.clone(), vars_pure, body, session.current_mut());
            
            let var_strs: Vec<String> = vars.iter().map(|(v, s)| format!("{}:{}", v.cyan(), s.to_string().cyan())).collect();
            let vars_display = if var_strs.is_empty() { "".to_string() } else { format!(" [∀ {}]", var_strs.join(", ")) };
            println!("{} {}{}", "Added Axiom:".yellow(), name.yellow().bold(), vars_display.bright_black());
        }
        Some(Statement::Import(src)) => {
            if let Err(e) = resolve_and_load(&src, session) {
                println!("{}", format!("Error importing '{}': {}", src, e).red());
            }
        }
        Some(Statement::GivenDecl(name, formula)) => {
            session.current_mut().add_given(name.clone(), formula.clone());
            println!("{} {}",
                "Added Given:".green().bold(),
                name.cyan().bold());
        }
        None => println!("{}", format!("Parse error: {}", trimmed).red()),
    }
}

// ---------------------------------------------------------------------------
// Entry point
// ---------------------------------------------------------------------------

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let mut session = Session::new();

    // -------------------------------------------------------------------
    // COMPILER MODE (File input)
    // -------------------------------------------------------------------
    if args.len() > 1 {
        let filename = &args[1];
        if let Err(e) = resolve_and_load(filename, &mut session) {
            eprintln!("{}", format!("Error: {}", e).red());
        }
        return;
    }

    // -------------------------------------------------------------------
    // REPL MODE
    // -------------------------------------------------------------------
    let mut rl = DefaultEditor::new().expect("Failed to init readline");
    let _ = rl.load_history(".axia_history");

    println!("{}", "\n--- Axia Kernel v0.9 ---".yellow().bold());
    println!("Active universe: 'default'  |  type `help` for commands");

    loop {
        let prompt = format!("[{}]> ", session.active);
        match rl.readline(&prompt) {
            Ok(line) => {
                let _ = rl.add_history_entry(line.as_str());
                let t = line.trim();
                if t == "exit" { 
                    let _ = rl.save_history(".axia_history");
                    break; 
                }
                process_line(&line, &mut session);
            }
            Err(ReadlineError::Interrupted) | Err(ReadlineError::Eof) => {
                let _ = rl.save_history(".axia_history");
                break;
            }
            Err(e) => { 
                eprintln!("{}", format!("Error: {:?}", e).red()); 
                let _ = rl.save_history(".axia_history");
                break; 
            }
        }
    }
}
