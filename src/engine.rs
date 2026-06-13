use std::collections::HashMap;
use crate::ast::{Term, Formula, Sort};

pub type Bindings = HashMap<String, Term>;

// ---------------------------------------------------------------------------
// Proof tree
// ---------------------------------------------------------------------------

/// One node in a successful proof tree.
///
/// The `witnesses` field is populated when this node was proved via
/// Existential Instantiation.  Each entry is `(original_var_name, resolved_term)`
/// — for example `("C", Apply("IntersectAt", [Var("l1"), Var("l2")]))`.
/// The formatter uses this to emit "Construct C as IntersectAt(l1, l2)."
#[derive(Debug, Clone)]
pub struct ProofStep {
    /// The formula that was proved at this node, with all bindings applied.
    pub goal:       Formula,
    /// Human-readable name of the rule / axiom used.
    pub rule_name:  String,
    /// Sub-goals that had to be proved to discharge this goal.
    pub sub_proofs: Vec<ProofStep>,
    /// Existential witnesses introduced at this step (may be empty).
    pub witnesses:  Vec<(String, Term)>,
}

impl ProofStep {
    /// Convenience constructor for steps with no witnesses.
    fn simple(goal: Formula, rule_name: impl Into<String>, sub_proofs: Vec<ProofStep>) -> Self {
        ProofStep { goal, rule_name: rule_name.into(), sub_proofs, witnesses: vec![] }
    }

    /// Recursively apply `bindings` to every goal formula and every witness
    /// term in this node and all of its descendants.
    ///
    /// Called once on the root after `prove_dfs` returns so that Skolem
    /// variables (`?wN`) and alpha-renamed axiom variables (`x_9`) that were
    /// still unresolved at the time each snapshot was taken are replaced with
    /// their final ground values before the formatter sees the tree.
    pub fn apply_bindings(&mut self, bindings: &Bindings) {
        self.goal = self.goal.substitute(bindings);
        for witness in &mut self.witnesses {
            witness.1 = witness.1.substitute(bindings);
        }
        for sub in &mut self.sub_proofs {
            sub.apply_bindings(bindings);
        }
    }
}

// ---------------------------------------------------------------------------
// Axiom representation
// ---------------------------------------------------------------------------

#[derive(Debug, Clone)]
pub struct Axiom {
    pub name:       String,
    pub vars:       Vec<String>,
    pub premises:   Vec<Formula>,
    pub conclusion: Formula,
}

// ---------------------------------------------------------------------------
// Universe (logical namespace)
// ---------------------------------------------------------------------------

#[derive(Debug, Clone, Default)]
pub struct Universe {
    pub axioms:     Vec<Axiom>,
    pub types:      Vec<String>,
    pub predicates: HashMap<String, (Vec<String>, String)>,
    /// Ground constants declared in this universe, e.g. `A : Pt`.
    /// Maps constant name → its sort.  These are treated as rigid
    /// (`Term::Const`) during parsing so the engine cannot unify them
    /// with each other or with free variables.
    pub constants:  HashMap<String, Sort>,
}

impl Universe {
    pub fn new() -> Self { Universe::default() }

    pub fn add_axiom(&mut self, axiom: Axiom) { self.axioms.push(axiom); }

    pub fn add_type(&mut self, name: String) {
        if !self.types.contains(&name) { self.types.push(name); }
    }

    pub fn add_predicate(&mut self, name: String, arg_sorts: Vec<String>, ret_sort: String) {
        self.predicates.insert(name, (arg_sorts, ret_sort));
    }

    pub fn add_constant(&mut self, name: String, sort: Sort) {
        self.constants.insert(name, sort);
    }

    pub fn import_from(&mut self, other: &Universe) {
        for axiom in &other.axioms {
            if !self.axioms.iter().any(|a| a.name == axiom.name) {
                self.axioms.push(axiom.clone());
            }
        }
        for type_name in &other.types { self.add_type(type_name.clone()); }
        for (name, (args, ret)) in &other.predicates {
            self.predicates.entry(name.clone()).or_insert_with(|| (args.clone(), ret.clone()));
        }
        for (name, sort) in &other.constants {
            self.constants.entry(name.clone()).or_insert_with(|| sort.clone());
        }
    }

    pub fn summary(&self) -> String {
        format!("{} axiom(s), {} type(s), {} predicate(s), {} constant(s)",
                self.axioms.len(), self.types.len(), self.predicates.len(), self.constants.len())
    }
}

// ---------------------------------------------------------------------------
// Substitution — must cover the Exists arm
// ---------------------------------------------------------------------------

impl Term {
    pub fn substitute(&self, bindings: &Bindings) -> Term {
        // Follow the variable-pointer chain to its ultimate target before
        // dispatching.  Without this, a chain  x → y → Apply(f, …)  would
        // return  Var("y", …)  instead of  Apply(f, …)  when starting from x,
        // because the original single-step lookup only followed one hop.
        let mut current = self;
        while let Term::Var(n, _) = current {
            match bindings.get(n) {
                Some(next) if next != current => { current = next; }
                _ => break,
            }
        }

        match current {
            Term::Var(n, s)      => Term::Var(n.clone(), s.clone()),
            Term::Const(_)       => current.clone(),
            Term::Apply(n, args) => Term::Apply(
                n.clone(),
                args.iter().map(|a| a.substitute(bindings)).collect(),
            ),
        }
    }

    pub fn sort(&self) -> Sort {
        match self {
            Term::Var(_, s) => s.clone(),
            _               => Sort::object(),
        }
    }

    /// Walk the binding chain until we reach a non-Var or an unbound Var.
    pub fn resolve<'a>(&'a self, bindings: &'a Bindings) -> &'a Term {
        let mut current = self;
        loop {
            match current {
                Term::Var(n, _) => match bindings.get(n) {
                    Some(next) if next != current => { current = next; }
                    _ => break,
                },
                _ => break,
            }
        }
        current
    }
}

impl Formula {
    pub fn substitute(&self, bindings: &Bindings) -> Formula {
        match self {
            Formula::Eq(l, r)        => Formula::Eq(l.substitute(bindings), r.substitute(bindings)),
            Formula::Pred(n, args)   => Formula::Pred(
                n.clone(),
                args.iter().map(|a| a.substitute(bindings)).collect(),
            ),
            Formula::And(l, r)       => Formula::And(
                Box::new(l.substitute(bindings)), Box::new(r.substitute(bindings))),
            Formula::Or(l, r)        => Formula::Or(
                Box::new(l.substitute(bindings)), Box::new(r.substitute(bindings))),
            Formula::Not(i)          => Formula::Not(Box::new(i.substitute(bindings))),
            Formula::Implies(l, r)   => Formula::Implies(
                Box::new(l.substitute(bindings)), Box::new(r.substitute(bindings))),

            // Substitution respects the binder: if the bound variable is
            // shadowed by a binding we skip it inside the body, just as in
            // capture-avoiding substitution.  In practice our Skolem names
            // (`?wN`) are globally unique so shadowing cannot occur, but we
            // implement it correctly anyway.
            Formula::Exists { var, sort, body } => {
                let mut inner_bindings = bindings.clone();
                inner_bindings.remove(var); // the bound var is local
                Formula::Exists {
                    var:  var.clone(),
                    sort: sort.clone(),
                    body: Box::new(body.substitute(&inner_bindings)),
                }
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Unification — must cover the Exists arm
// ---------------------------------------------------------------------------

impl Formula {
    pub fn unify(&self, goal: &Formula) -> Option<Bindings> {
        let mut bindings = HashMap::new();
        if self.unify_inner(goal, &mut bindings) { Some(bindings) } else { None }
    }

    fn unify_inner(&self, goal: &Formula, bindings: &mut Bindings) -> bool {
        match (self, goal) {
            (Formula::Pred(n1, a1), Formula::Pred(n2, a2)) =>
                n1 == n2
                    && a1.len() == a2.len()
                    && a1.iter().zip(a2).all(|(x, y)| Self::unify_term(x, y, bindings)),

            (Formula::Eq(l1, r1), Formula::Eq(l2, r2)) =>
                Self::unify_term(l1, l2, bindings) && Self::unify_term(r1, r2, bindings),

            (Formula::Not(i1),         Formula::Not(i2))         => i1.unify_inner(i2, bindings),
            (Formula::Or(l1, r1),      Formula::Or(l2, r2))      =>
                l1.unify_inner(l2, bindings) && r1.unify_inner(r2, bindings),
            (Formula::And(l1, r1),     Formula::And(l2, r2))     =>
                l1.unify_inner(l2, bindings) && r1.unify_inner(r2, bindings),
            (Formula::Implies(l1, r1), Formula::Implies(l2, r2)) =>
                l1.unify_inner(l2, bindings) && r1.unify_inner(r2, bindings),

            // Two existentials unify if their bound variables and bodies
            // unify (alpha-equivalence is not needed here because we
            // normalise variable names at axiom-load time).
            (Formula::Exists { var: v1, sort: s1, body: b1 },
             Formula::Exists { var: v2, sort: s2, body: b2 }) =>
                v1 == v2 && s1 == s2 && b1.unify_inner(b2, bindings),

            _ => false,
        }
    }

    pub fn unify_term(t1: &Term, t2: &Term, bindings: &mut Bindings) -> bool {
        let t1_res = t1.resolve(bindings).clone();
        let t2_res = t2.resolve(bindings).clone();

        match (t1_res, t2_res) {
            (Term::Var(n1, s1), Term::Var(n2, s2)) => {
                if n1 == n2 { return true; }
                if !sorts_compatible(&s1, &s2) { return false; }
                bindings.insert(n1, Term::Var(n2, s2));
                true
            }
            (Term::Var(n, s), val) | (val, Term::Var(n, s)) => {
                if occurs_check(&n, &val, bindings) { return false; }
                if !sorts_compatible(&s, &val.sort()) { return false; }
                bindings.insert(n, val);
                true
            }
            (Term::Const(a), Term::Const(b)) => a == b,
            (Term::Apply(n1, a1), Term::Apply(n2, a2)) =>
                n1 == n2
                    && a1.len() == a2.len()
                    && a1.iter().zip(a2.iter()).all(|(x, y)| Self::unify_term(x, y, bindings)),
            _ => false,
        }
    }
}

fn occurs_check(n: &str, t: &Term, bindings: &Bindings) -> bool {
    let t_res = t.resolve(bindings);
    match t_res {
        Term::Var(v, _)      => v == n,
        Term::Apply(_, args) => args.iter().any(|a| occurs_check(n, a, bindings)),
        Term::Const(_)       => false,
    }
}

fn sorts_compatible(s1: &Sort, s2: &Sort) -> bool {
    s1 == s2 || s1 == &Sort::object() || s2 == &Sort::object()
}

// ---------------------------------------------------------------------------
// Skolem name generation
// ---------------------------------------------------------------------------

/// Generate a fresh Skolem witness name.
///
/// Names are `?w1`, `?w2`, … — the leading `?` makes them visually distinct
/// from user-introduced variables and prevents them from accidentally
/// shadowing axiom variable names.
///
/// The counter is passed by mutable reference so it survives across IDDFS
/// depth iterations within a single `prove()` call.  This guarantees that
/// Skolem names are unique within one top-level proof attempt.
fn fresh_skolem(counter: &mut u32) -> String {
    *counter += 1;
    format!("?w{}", *counter)
}

// ---------------------------------------------------------------------------
// Alpha-renaming helper
// ---------------------------------------------------------------------------

/// Clone an axiom and suffix every universally-quantified variable name with
/// `_<counter>` so that two uses of the same axiom within one proof branch
/// cannot collide in the shared `bindings` map.
///
/// Only the names that appear in `axiom.vars` are renamed; predicate /
/// function names and sort names are left untouched.
fn instantiate_axiom(axiom: &Axiom, counter: usize) -> Axiom {
    // Build a renaming map: old_name → new_name
    let rename: HashMap<String, String> = axiom.vars
        .iter()
        .map(|v| (v.clone(), format!("{}_{}", v, counter)))
        .collect();

    /// Rename variables inside a Term.
    fn rename_term(t: &Term, rename: &HashMap<String, String>) -> Term {
        match t {
            Term::Var(n, s) =>
                Term::Var(rename.get(n).cloned().unwrap_or_else(|| n.clone()), s.clone()),
            Term::Const(_) => t.clone(),
            Term::Apply(n, args) =>
                Term::Apply(n.clone(), args.iter().map(|a| rename_term(a, rename)).collect()),
        }
    }

    /// Rename variables inside a Formula.
    fn rename_formula(f: &Formula, rename: &HashMap<String, String>) -> Formula {
        match f {
            Formula::Eq(l, r) =>
                Formula::Eq(rename_term(l, rename), rename_term(r, rename)),
            Formula::Pred(n, args) =>
                Formula::Pred(n.clone(), args.iter().map(|a| rename_term(a, rename)).collect()),
            Formula::And(l, r) =>
                Formula::And(Box::new(rename_formula(l, rename)), Box::new(rename_formula(r, rename))),
            Formula::Or(l, r) =>
                Formula::Or(Box::new(rename_formula(l, rename)), Box::new(rename_formula(r, rename))),
            Formula::Not(i) =>
                Formula::Not(Box::new(rename_formula(i, rename))),
            Formula::Implies(l, r) =>
                Formula::Implies(Box::new(rename_formula(l, rename)), Box::new(rename_formula(r, rename))),
            Formula::Exists { var, sort, body } => {
                // If the existential variable shadows a universally-quantified
                // one, propagate the rename into the body but not the binder.
                Formula::Exists {
                    var:  rename.get(var).cloned().unwrap_or_else(|| var.clone()),
                    sort: sort.clone(),
                    body: Box::new(rename_formula(body, rename)),
                }
            }
        }
    }

    Axiom {
        name:       axiom.name.clone(),
        vars:       axiom.vars.iter().map(|v| format!("{}_{}", v, counter)).collect(),
        premises:   axiom.premises.iter().map(|p| rename_formula(p, &rename)).collect(),
        conclusion: rename_formula(&axiom.conclusion, &rename),
    }
}

// ---------------------------------------------------------------------------
// Proof search (IDDFS)
// ---------------------------------------------------------------------------

/// Attempt to prove `goal` using axioms from the given `universe`.
pub fn prove(goal: &Formula, universe: &Universe, max_depth: u32) -> Option<ProofStep> {
    let mut skolem_counter = 0u32;
    let mut axiom_counter  = 0usize;
    for depth in 1..=max_depth {
        let proofs = prove_dfs(goal, &universe.axioms, depth, &HashMap::new(), &[], &mut skolem_counter, &mut axiom_counter);
        if let Some((mut proof, final_bindings)) = proofs.into_iter().next() {
            // Wash the entire proof tree with the final resolved bindings so
            // that Skolem variables (?wN) and alpha-renamed axiom variables
            // (x_9) that were snapshotted with incomplete bindings during the
            // DFS are all replaced with their ultimate ground terms before the
            // formatter sees the tree.
            proof.apply_bindings(&final_bindings);
            return Some(proof);
        }
    }
    None
}

/// Core backward-chaining DFS.
///
/// Returns `(ProofStep, Bindings)` on success, `None` on failure.
///
/// # Arguments
/// * `goal`          — Formula to prove (may still contain free variables).
/// * `axioms`        — Available axioms (from the active Universe).
/// * `depth`         — Remaining depth budget for this IDDFS iteration.
/// * `bindings`      — Variable substitutions accumulated so far.
/// * `path`          — Stack of goals on the current branch (cycle detection).
/// * `skolem_ctr`    — Mutable counter for fresh Skolem name generation.
/// * `axiom_ctr`     — Mutable counter for alpha-renaming axiom variables.
fn prove_dfs(
    goal:       &Formula,
    axioms:     &[Axiom],
    depth:      u32,
    bindings:   &Bindings,
    path:       &[Formula],
    skolem_ctr: &mut u32,
    axiom_ctr:  &mut usize,
) -> Vec<(ProofStep, Bindings)> {
    if depth == 0 { return vec![]; }

    let current_goal = goal.substitute(bindings);

    // ------------------------------------------------------------------
    // Cycle detection
    //
    // We compare structurally.  Skolem constants (`?wN`) appear as Var
    // nodes with globally unique names, so an existential sub-goal
    // `P(?w1)` will never accidentally match a prior `P(?w2)` — no
    // spurious cycle pruning occurs.
    //
    // We deliberately do NOT add the Exists wrapper to the path; instead
    // we add the instantiated body (below).  This prevents the wrapper from
    // being mistaken for a cycle if the same existential is encountered on
    // a different branch.
    // ------------------------------------------------------------------
    if path.contains(&current_goal) { return vec![]; }
    
    let mut results = Vec::new();

    // ------------------------------------------------------------------
    // Structural rule: Conjunction  (A ∧ B)
    // ------------------------------------------------------------------
    if let Formula::And(left, right) = &current_goal {
        let mut path2 = path.to_vec(); path2.push(current_goal.clone());
        for (p1, b1) in prove_dfs(left, axioms, depth, bindings, &path2, skolem_ctr, axiom_ctr) {
            let right_sub = right.substitute(&b1);
            for (p2, b2) in prove_dfs(&right_sub, axioms, depth, &b1, &path2, skolem_ctr, axiom_ctr) {
                results.push((
                    ProofStep::simple(current_goal.clone(), "Conjunction", vec![p1.clone(), p2]),
                    b2,
                ));
            }
        }
        return results;
    }

    // ------------------------------------------------------------------
    // Structural rule: Disjunction  (A ∨ B)
    // ------------------------------------------------------------------
    if let Formula::Or(left, right) = &current_goal {
        let mut path2 = path.to_vec(); path2.push(current_goal.clone());
        for (p, b) in prove_dfs(left, axioms, depth, bindings, &path2, skolem_ctr, axiom_ctr) {
            results.push((ProofStep::simple(current_goal.clone(), "Disjunction_Left", vec![p]), b));
        }
        for (p, b) in prove_dfs(right, axioms, depth, bindings, &path2, skolem_ctr, axiom_ctr) {
            results.push((ProofStep::simple(current_goal.clone(), "Disjunction_Right", vec![p]), b));
        }
        return results;
    }

    // ------------------------------------------------------------------
    // Structural rule: Existential Instantiation  (∃ x : S, P(x))
    //
    // Algorithm:
    //  1. Mint a fresh Skolem constant `?wN` with the declared sort.
    //  2. Substitute `x := ?wN` in the body, producing the witness goal.
    //  3. Add ONLY the witness goal to the path (not the ∃ wrapper) so
    //     cycle detection operates on what we are actually trying to prove.
    //  4. Recursively prove the witness goal.
    //  5. After success, resolve `?wN` in the returned bindings to obtain
    //     the concrete witness term (if any).
    //  6. Apply ALL final bindings to the witness goal so the stored
    //     `ProofStep.goal` shows the fully-concrete formula.
    //  7. Return the witness pair in `ProofStep.witnesses` for the formatter.
    // ------------------------------------------------------------------
    if let Formula::Exists { var, sort, body } = &current_goal {
        let skolem_name = fresh_skolem(skolem_ctr);
        let skolem_term = Term::Var(skolem_name.clone(), sort.clone());

        // Build  body[var := ?wN]
        let mut witness_bindings = bindings.clone();
        witness_bindings.insert(var.clone(), skolem_term.clone());
        let witness_goal = body.substitute(&witness_bindings);

        let mut path2 = path.to_vec();
        path2.push(current_goal.clone()); // Push the Exists wrapper to prevent immediate cycle death

        for (sub_proof, final_bindings) in prove_dfs(&witness_goal, axioms, depth - 1, &witness_bindings, &path2, skolem_ctr, axiom_ctr) {
            let resolved_witness = skolem_term.substitute(&final_bindings);
            let concrete_goal = witness_goal.substitute(&final_bindings);

            let mut step = ProofStep {
                goal:       current_goal.clone(),
                rule_name:  "Existential_Instantiation".to_string(),
                sub_proofs: vec![sub_proof],
                witnesses:  vec![(var.clone(), resolved_witness)],
            };

            let mut merged = bindings.clone();
            merged.extend(final_bindings);

            step.sub_proofs[0].goal = concrete_goal;
            results.push((step, merged));
        }
        return results;
    }

    // ------------------------------------------------------------------
    // Axiom matching (backward chaining)
    // ------------------------------------------------------------------
    let mut path2 = path.to_vec(); path2.push(current_goal.clone());

    for axiom in axioms {
        // Alpha-rename the axiom's universally-quantified variables so that
        // two applications of the same axiom on the same branch cannot
        // collide in the shared `bindings` map.
        *axiom_ctr += 1;
        let fresh_axiom = instantiate_axiom(axiom, *axiom_ctr);

        if let Some(new_bindings) = fresh_axiom.conclusion.unify(&current_goal) {
            // Track all valid branching states: (list of subproofs, accumulated bindings)
            let mut branch_states = vec![(Vec::new(), {
                let mut b = bindings.clone();
                b.extend(new_bindings);
                b
            })];

            // Fold over each premise
            for premise in &fresh_axiom.premises {
                let mut next_states = Vec::new();
                for (sub_proofs_so_far, current_bindings) in branch_states {
                    let p_sub = premise.substitute(&current_bindings);
                    let premise_proofs = prove_dfs(&p_sub, axioms, depth - 1, &current_bindings, &path2, skolem_ctr, axiom_ctr);
                    
                    for (proof, b_out) in premise_proofs {
                        let mut next_proofs = sub_proofs_so_far.clone();
                        next_proofs.push(proof);
                        
                        let mut next_bindings = current_bindings.clone();
                        next_bindings.extend(b_out);
                        
                        next_states.push((next_proofs, next_bindings));
                    }
                }
                branch_states = next_states;
            }

            // Any state that survived all premises is a valid proof
            for (sub_proofs, final_bindings) in branch_states {
                results.push((
                    ProofStep::simple(current_goal.clone(), axiom.name.clone(), sub_proofs),
                    final_bindings,
                ));
            }
        }
    }

    results
}
