use std::collections::HashMap;
use std::fmt;

pub type Bindings = HashMap<String, Term>;

#[derive(Debug, Clone)]
pub struct ProofStep {
    pub goal: Formula,
    pub rule_name: String,
    pub sub_proofs: Vec<ProofStep>,
}

impl ProofStep {
    pub fn new(goal: Formula, rule_name: &str, sub_proofs: Vec<ProofStep>) -> Self {
        ProofStep {
            goal,
            rule_name: rule_name.to_string(),
            sub_proofs,
        }
    }
}

pub struct Axiom {
    pub name: String,
    pub premises: Vec<Formula>,
    pub conclusion: Formula,
}

impl Axiom {
    pub fn new(name: &str, premises: Vec<Formula>, conclusion: Formula) -> Self {
        Axiom {name: name.to_string(), premises, conclusion}
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Term {
    Var(String),
    Const(String),
    Apply(String, Vec<Term>),
}

impl Term {
    pub fn var(name: &str) -> Self {Term::Var(name.to_string())}
    pub fn con(name: &str) -> Self {Term::Const(name.to_string())}
    pub fn apply(name: &str, args: Vec<Term>) -> Self {Term::Apply(name.to_string(), args)}
    pub fn substitute(&self, bindings: &Bindings) -> Term {
        match self {
            Term::Var(name) => {
                if let Some(replacement) = bindings.get(name) {
                    replacement.clone()
                } else {
                    Term::Var(name.clone())
                }
            },
            Term::Const(_) => self.clone(),
            Term::Apply(name, args) => {
                let new_args = args.iter().map(|arg| arg.substitute(bindings)).collect();
                Term::Apply(name.clone(), new_args)
            }
        }
    }
}

impl fmt::Display for Term {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Term::Var(name) => write!(f, "{}", name),
            Term::Const(name) => write!(f, "{}", name),
            Term::Apply(name, args) => {
                write!(f, "{}()", name)?;
                for (i, arg) in args.iter().enumerate() {
                    if i>0 {write!(f, ", ")?;}
                    write!(f, "{}", arg)?;
                }
                write!(f, ")")
            }
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Formula {
    Eq(Term, Term),
    Pred(String, Vec<Term>),
}

impl Formula {
    pub fn eq(lhs: Term, rhs: Term) -> Self {Formula::Eq(lhs, rhs)}

    pub fn pred(name: &str, args: Vec<Term>) -> Self {Formula::Pred(name.to_string(), args)}

    pub fn substitute(&self, bindings: &Bindings) -> Formula {
        match self {
            Formula::Eq(lhs, rhs) => {
                Formula::Eq(lhs.substitute(bindings), rhs.substitute(bindings))
            }
            Formula::Pred(name, args) => {
                let new_args = args.iter().map(|a| a.substitute(bindings)).collect();
                Formula::Pred(name.clone(), new_args)
            }
        }
    }

    pub fn unify(&self, goal: &Formula) -> Option<Bindings> {
        let mut bindings = HashMap::new();
        match (self, goal) {
            (Formula::Eq(l1, r1), Formula::Eq(l2, r2)) => {
                if !Self::unify_term(l1, l2, &mut bindings) {return None;}
                if !Self::unify_term(r1, r2, &mut bindings) {return None;}
            }
            (Formula::Pred(n1, args1), Formula::Pred(n2, args2)) => {
                if n1 != n2 || args1.len() != args2.len() { return None;}
                for (a1, a2) in args1.iter().zip(args2.iter()) {
                    if !Self::unify_term(a1, a2, &mut bindings) { return None; }
                }
            }
            _ => return None,
        }
        Some(bindings)
    }

    fn unify_term(pattern: &Term, target: &Term, bindings: &mut Bindings) -> bool {
        match (pattern, target) {
            (Term::Var(name), val) => {
                if let Some(existing) = bindings.get(name) {
                    return existing == val;
                }
                bindings.insert(name.clone(), val.clone());
                true
            },
            (val, Term::Var(name)) => {
                if let Some(existing) = bindings.get(name) {
                    return existing == val;
                }
                bindings.insert(name.clone(), val.clone());
                true
            },
            (Term::Const(c1), Term::Const(c2)) => c1 == c2,
            (Term::Apply(n1, args1), Term::Apply(n2, args2)) => {
                if n1 != n2 || args1.len() != args2.len() {return false;}
                for (a1, a2) in args1.iter().zip(args2.iter()) {
                    if !Self::unify_term(a1, a2, bindings) {return false;}
                }
                true
            },
            _ => false,
        }
    }

}

impl fmt::Display for Formula {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Formula::Eq(lhs, rhs) => write!(f, "{}={}", lhs, rhs),
            Formula::Pred(name, args) => {
                write!(f, "{}(", name)?;
                for (i, arg) in args.iter().enumerate() {
                    if i>0 { write!(f, ", ")?; }
                    write!(f, "{}", arg)?;
                }
                write!(f, ")")
            }
        }
    }
}

fn prove(goal: &Formula, axioms: &[Axiom], depth: u32) -> Option<ProofStep> {
    if depth > 10 { return None; } 

    for axiom in axioms {
        if let Some(bindings) = axiom.conclusion.unify(goal) {

            let required_premises: Vec<Formula> = axiom.premises.iter()
                .map(|p| p.substitute(&bindings))
                .collect();

            let mut sub_proofs = Vec::new();
            let mut all_premises_proven = true;

            for premise in required_premises {
                if let Some(proof) = prove(&premise, axioms, depth + 1) {
                    sub_proofs.push(proof);
                } else {
                    all_premises_proven = false;
                    break;
                }
            }

            if all_premises_proven {
                return Some(ProofStep::new(
                        goal.clone(), 
                        &axiom.name, 
                        sub_proofs
                ));
            }
        }
    }

    None
}

fn print_proof(step: &ProofStep, depth: usize) {
    let indent = " ".repeat(depth);
    if step.sub_proofs.is_empty() {
        println!("{}• Fact: {} (By {})", indent, step.goal, step.rule_name);
    } else {
        println!("{}• Prove: {}", indent, step.goal);
        println!("{}  Strategy: Apply {}", indent, step.rule_name);

        for sub in &step.sub_proofs {
            print_proof(sub, depth + 1);
        }
    }
}

fn main() {
    let ab = Term::con("AB");
    let cd = Term::con("CD");
    let ef = Term::con("EF");

    // 2. Define The "Givens" (Facts specific to this problem)
    let given_1 = Axiom::new("Given", vec![], Formula::pred("Congruent", vec![ab.clone(), cd.clone()]));
    let given_2 = Axiom::new("Given", vec![], Formula::pred("Congruent", vec![cd.clone(), ef.clone()]));

    // 3. Define the "Rules of Geometry" (General Math Truths)
    let x = Term::var("x");
    let y = Term::var("y");
    let z = Term::var("z");

    // Transitive Property: If x ~= y AND y ~= z, THEN x ~= z
    let transitivity = Axiom::new(
        "TransitiveProperty",
        vec![
        Formula::pred("Congruent", vec![x.clone(), y.clone()]),
        Formula::pred("Congruent", vec![y.clone(), z.clone()]),
        ],
        Formula::pred("Congruent", vec![x.clone(), z.clone()])
    );

    // Symmetric Property: If x ~= y THEN y ~= x (Optional, but good for robust proofs)
    let symmetry = Axiom::new(
        "SymmetricProperty",
        vec![Formula::pred("Congruent", vec![x.clone(), y.clone()])],
        Formula::pred("Congruent", vec![y.clone(), x.clone()])
    );

    let axioms = vec![given_1, given_2, transitivity, symmetry];

    // 4. The Goal: Prove AB ~= EF
    let goal = Formula::pred("Congruent", vec![ab.clone(), ef.clone()]);

    println!("--- Geometry Proof Assistant ---");
    println!("Goal: {}", goal);

    match prove(&goal, &axioms, 0) {
        Some(proof) => {
            println!("\nProof Found:\n");
            print_proof(&proof, 0);
        },
        None => println!("Unable to find a proof."),
    }
}
