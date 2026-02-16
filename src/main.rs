mod ast;
mod parser;
mod engine;

use std::fs::File;
use std::io::{self, BufRead, BufReader, Write};
use rustyline::error::ReadlineError;
use rustyline::DefaultEditor;
use parser::{lex, Parser};
use ast::{Statement, Formula, Term};
use engine::{Axiom, prove};

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
                premises: vec![*premise], // The LHS is the premise
                conclusion: *conclusion,  // The RHS is the conclusion
            });
        },
        _ => {
            axioms.push(Axiom { name, vars, premises: vec![], conclusion: formula });
        }
    }
}

fn print_proof(step: &engine::ProofStep, depth: usize) {
    let indent = "  ".repeat(depth);
    if step.sub_proofs.is_empty() {
        println!("{}• Fact: {} (By {})", indent, step.goal, step.rule_name);
    } else {
        println!("{}• Prove: {}", indent, step.goal);
        println!("{}  Strategy: Apply {}", indent, step.rule_name);
        for sub in &step.sub_proofs { print_proof(sub, depth + 1); }
    }
}

fn process_line(input: &str, axioms: &mut Vec<Axiom>) {
    let trimmed = input.trim();
    if trimmed.is_empty() || trimmed.starts_with("--") { return; } // Skip empty or comments

    if trimmed.starts_with("load ") {
        let filename = trimmed.trim_start_matches("load ").trim();
        println!("Loading file: {}", filename);
        if let Ok(file) = File::open(filename) {
            let reader = BufReader::new(file);
            for line in reader.lines() {
                if let Ok(l) = line {
                    process_line(&l, axioms); // Recursively process file lines
                }
            }
            println!("File loaded.");
        } else {
            println!("Error: Could not open file '{}'", filename);
        }
        return;
    }

    if trimmed.starts_with("prove ") {
         let goal_str = trimmed.trim_start_matches("prove ").trim();
         let g_tokens = lex(goal_str);
         let mut g_parser = Parser::new(g_tokens);
         
         if let Some(goal) = g_parser.parse_formula() {
             println!("Goal: {}", goal);
             if let Some(proof) = prove(&goal, axioms, 0) {
                 println!("\n--- Q.E.D. ---");
                 print_proof(&proof, 0);
             } else {
                 println!("No proof found.");
             }
         } else {
             println!("Could not parse goal.");
         }
         return;
    }

    if trimmed.starts_with("assert ") {
         let fact_str = trimmed.trim_start_matches("assert ").trim();
         let tokens = lex(fact_str);
         let mut parser = Parser::new(tokens);
         if let Some(f) = parser.parse_formula() {
             axioms.push(Axiom { name: "Fact".to_string(), vars: vec![], premises: vec![], conclusion: f });
             println!("Fact added.");
         } else {
             println!("Could not parse fact.");
         }
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
    
    println!("--- Axia Euclidean Kernel v0.3 ---");
    println!("Commands: 'load <file>', 'prove <goal>', or type definitions.");
    println!("(Press Ctrl+C to exit)");

    loop {
        let readline = rl.readline("> ");
        match readline {
            Ok(line) => {
                let _ = rl.add_history_entry(line.as_str()); // Add to Up-Arrow history
                if line.trim() == "exit" { break; }
                process_line(&line, &mut axioms);
            },
            Err(ReadlineError::Interrupted) => {
                println!("CTRL-C");
                break;
            },
            Err(ReadlineError::Eof) => {
                println!("CTRL-D");
                break;
            },
            Err(err) => {
                println!("Error: {:?}", err);
                break;
            }
        }
    }
}
