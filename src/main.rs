mod ast;
mod parser;
mod engine;

use std::fs::File;
use std::io::{BufRead, BufReader};
use std::collections::HashMap;
use rustyline::error::ReadlineError;
use rustyline::DefaultEditor;
use parser::{lex, Parser};
use ast::{Statement, Formula, Term};
use engine::{Axiom, ProofStep, prove};

// --- LOGIC HELPERS ---

fn add_axiom(name: String, vars: Vec<String>, formula: Formula, axioms: &mut Vec<Axiom>) {
    match formula {
        Formula::And(left, right) => {
            add_axiom(format!("{}_L", name), vars.clone(), *left, axioms);
            add_axiom(format!("{}_R", name), vars, *right, axioms);
        },
        Formula::Implies(premise, conclusion) => {
            axioms.push(Axiom {
                name,
                vars,
                premises: vec![*premise],
                conclusion: *conclusion,
            });
        },
        _ => {
            axioms.push(Axiom { name, vars, premises: vec![], conclusion: formula });
        }
    }
}

// --- SMART FORMATTER (The "Writer") ---

struct ProofFormatter {
    aliases: HashMap<String, String>, // Maps raw term string -> "C"
    definitions: Vec<String>,         // "Let C be..."
}

impl ProofFormatter {
    fn new() -> Self {
        ProofFormatter {
            aliases: HashMap::new(),
            definitions: Vec::new(),
        }
    }

    // 1. Analyze the tree to find "Construction" terms
    fn scan(&mut self, step: &ProofStep) {
        // Check the goal for interesting terms
        self.scan_formula(&step.goal);
        // Recurse
        for sub in &step.sub_proofs {
            self.scan(sub);
        }
    }

    fn scan_formula(&mut self, f: &Formula) {
        match f {
            Formula::Eq(l, r) => { self.scan_term(l); self.scan_term(r); }
            Formula::Pred(_, args) => { for a in args { self.scan_term(a); } }
            Formula::And(l, r) | Formula::Or(l, r) | Formula::Implies(l, r) => { 
                self.scan_formula(l); self.scan_formula(r); 
            }
            Formula::Not(i) => self.scan_formula(i),
        }
    }

    fn scan_term(&mut self, t: &Term) {
        if let Term::Apply(name, args) = t {
            // Recurse first
            for a in args { self.scan_term(a); }

            // Heuristic: If it's an Intersection, name it C!
            if name == "IntersectAt" && !self.aliases.contains_key(&format!("{}", t)) {
                let name = "C"; // For a generic solver, we'd use C1, C2...
                let desc = format!("Let {} be the intersection of {} and {}.", 
                    name, self.fmt_term(&args[0]), self.fmt_term(&args[1]));
                
                self.aliases.insert(format!("{}", t), name.to_string());
                self.definitions.push(desc);
            }
        }
    }

    // 2. Format Terms (Apply Aliases)
    fn fmt_term(&self, t: &Term) -> String {
        let raw = format!("{}", t);
        if let Some(alias) = self.aliases.get(&raw) {
            return alias.clone();
        }
        match t {
            Term::Apply(n, args) => {
                if n == "Circ" && args.len() == 2 {
                    // Pretty print Circles
                    format!("Circle({}, {})", self.fmt_term(&args[0]), self.fmt_term(&args[1]))
                } else {
                    raw // Default
                }
            },
            _ => raw
        }
    }

    // 3. Format Formulas (Readable English)
    fn fmt_formula(&self, f: &Formula) -> String {
        match f {
            Formula::Eq(l, r) => format!("{} = {}", self.fmt_term(l), self.fmt_term(r)),
            Formula::Pred(name, args) => {
                if name == "DistEq" && args.len() == 4 {
                    format!("|{}{}| = |{}{}|", 
                        self.fmt_term(&args[0]), self.fmt_term(&args[1]), 
                        self.fmt_term(&args[2]), self.fmt_term(&args[3]))
                } else if name == "OnCirc" && args.len() == 2 {
                    format!("{} is on {}", self.fmt_term(&args[0]), self.fmt_term(&args[1]))
                } else if name == "Center" && args.len() == 2 {
                    format!("{} is center of {}", self.fmt_term(&args[0]), self.fmt_term(&args[1]))
                } else {
                    // Fallback to standard
                    let nice_args: Vec<String> = args.iter().map(|a| self.fmt_term(a)).collect();
                    format!("{}({})", name, nice_args.join(", "))
                }
            },
            Formula::And(l, r) => format!("{} AND {}", self.fmt_formula(l), self.fmt_formula(r)),
            Formula::Or(l, r) => format!("{} OR {}", self.fmt_formula(l), self.fmt_formula(r)),
            Formula::Not(i) => format!("NOT {}", self.fmt_formula(i)),
            Formula::Implies(l, r) => format!("IF {} THEN {}", self.fmt_formula(l), self.fmt_formula(r)),
        }
    }
}

fn explain_proof(step: &ProofStep) {
    // 1. Pre-Scan for constructions
    let mut fmt = ProofFormatter::new();
    fmt.scan(step);

    println!("\n--- Q.E.D. ---");
    // Print Definitions ("Let C be...")
    for def in &fmt.definitions {
        println!("{}", def);
    }
    println!(""); // Spacer

    explain_recursive(step, 0, &fmt);
}

fn explain_recursive(step: &ProofStep, depth: usize, fmt: &ProofFormatter) {
    let indent = "  ".repeat(depth);
    let goal_text = fmt.fmt_formula(&step.goal);

    // Clean up rule names (e.g., "Ax_Int_L" -> "Intersection Axiom")
    let rule_display = match step.rule_name.as_str() {
        "Ax_Transitivity" => "Transitivity",
        "Ax_Radii_Eq" => "Equality of Radii",
        "Ax_Int_L" | "Ax_Int_R" => "Intersection Definition",
        "Ax_Radius" => "Radius Definition",
        name => name.strip_suffix("_L").or_else(|| name.strip_suffix("_R")).unwrap_or(name),
    };

    if step.sub_proofs.is_empty() {
        // Base Facts
        if step.rule_name.starts_with("Fact") || step.rule_name == "Given" {
            println!("{}Given: {}.", indent, goal_text);
        } else {
            // e.g. "By Definition, C is on Circle(A, B)."
            println!("{}By {}, {}.", indent, rule_display, goal_text);
        }
    } else {
        // Complex Steps
        if step.rule_name == "Conjunction" {
            println!("{}To prove {}, we show both parts:", indent, goal_text);
        } else {
            println!("{}Goal: {}.", indent, goal_text);
            println!("{}Strategy: Apply {}.", indent, rule_display);
        }

        for sub in &step.sub_proofs {
            explain_recursive(sub, depth + 1, fmt);
        }
        
        if depth == 0 {
            println!("\nTherefore, the proof is complete.");
        }
    }
}

// --- CLI HANDLERS ---

fn process_line(input: &str, axioms: &mut Vec<Axiom>) {
    let trimmed = input.trim();
    if trimmed.is_empty() || trimmed.starts_with("--") { return; }

    if trimmed.starts_with("load ") {
        let filename = trimmed.trim_start_matches("load ").trim();
        println!("Loading file: {}", filename);
        if let Ok(file) = File::open(filename) {
            let reader = BufReader::new(file);
            for line in reader.lines() { if let Ok(l) = line { process_line(&l, axioms); } }
            println!("File loaded.");
        } else { println!("Error: Could not open file '{}'", filename); }
        return;
    }

    if trimmed.starts_with("prove ") {
         let goal_str = trimmed.trim_start_matches("prove ").trim();
         let tokens = lex(goal_str);
         let mut parser = Parser::new(tokens);
         if let Some(goal) = parser.parse_formula() {
             println!("Goal: {}", goal); // Raw goal first
             if let Some(proof) = prove(&goal, axioms, 8) {
                 explain_proof(&proof); // <--- CALL NEW EXPLAINER
             } else { println!("No proof found."); }
         } else { println!("Could not parse goal."); }
         return;
    }

    if trimmed.starts_with("assert ") {
         let fact_str = trimmed.trim_start_matches("assert ").trim();
         let tokens = lex(fact_str);
         let mut parser = Parser::new(tokens);
         if let Some(f) = parser.parse_formula() {
             axioms.push(Axiom { name: "Fact".to_string(), vars: vec![], premises: vec![], conclusion: f });
             println!("Fact added.");
         } else { println!("Could not parse fact."); }
         return;
    }

    let tokens = lex(trimmed);
    let mut parser = Parser::new(tokens);
    match parser.parse_statement() {
        Some(Statement::TypeDecl(n)) => println!("Defined Type: {}", n),
        Some(Statement::PredDecl(n, _)) => println!("Defined Predicate: {}", n),
        Some(Statement::AxiomDecl { name, vars, body }) => {
            let vars_pure: Vec<String> = vars.into_iter().map(|(n, _)| n).collect();
            add_axiom(name.clone(), vars_pure, body, axioms);
            println!("Added Axiom(s): {}", name);
        },
        Some(Statement::Goal(_)) => println!("Goal declared."),
        None => println!("Parse error: {}", trimmed),
    }
}

fn main() {
    let mut axioms = Vec::new();
    let mut rl = DefaultEditor::new().expect("Failed to init readline");
    println!("--- Axia Euclidean Kernel v0.5 ---");
    println!("Commands: 'load <file>', 'assert <fact>', 'prove <goal>'");

    loop {
        match rl.readline("> ") {
            Ok(line) => {
                let _ = rl.add_history_entry(line.as_str());
                if line.trim() == "exit" { break; }
                process_line(&line, &mut axioms);
            },
            Err(_) => break,
        }
    }
}
