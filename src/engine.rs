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
    /// Named hypotheses / deduced facts in this universe.
    ///
    /// Populated by:
    ///   • `Given <Name> : <Formula>` declarations (user-supplied)
    ///   • `forward_deduce` (engine-discovered consequences)
    ///
    /// The engine performs a direct O(|givens|) forward lookup against
    /// these before initiating any backward-chaining DFS, and the forward
    /// deduction loop iterates over them to derive new facts.
    pub givens:     HashMap<String, Formula>,
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

    pub fn add_given(&mut self, name: String, formula: Formula) {
        self.givens.insert(name, formula);
    }

    pub fn summary(&self) -> String {
        format!(
            "{} axiom(s), {} type(s), {} predicate(s), {} constant(s), {} given(s)",
            self.axioms.len(), self.types.len(),
            self.predicates.len(), self.constants.len(),
            self.givens.len(),
        )
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
// One-way pattern matching (for the term rewriter / simplifier)
// ---------------------------------------------------------------------------

/// Match `pattern` against `target`, treating `target` as ground.
///
/// This is intentionally weaker than full unification:
/// * Variables in `pattern` may bind to any sub-term of `target`.
/// * Variables in `target` are NOT bound to anything — `target` is rigid.
///   A pattern variable can still match a target `Var` (it just binds to
///   that variable like any other sub-term), but a `target` variable can
///   never cause `pattern` to be instantiated.
/// * Constants and function symbols must match exactly.
/// * A pattern variable that's already bound (from matching an earlier
///   part of the pattern) must match the *same* target sub-term again
///   (consistency check), so `Add(x, x)` only matches `Add(2, 2)`, not
///   `Add(2, 3)`.
///
/// Returns `true` and populates `bindings` on success; on failure
/// `bindings` may have been partially populated, so callers should use a
/// fresh `Bindings` map (or be prepared to discard it) per attempt.
pub fn pattern_match(pattern: &Term, target: &Term, bindings: &mut Bindings) -> bool {
    match pattern {
        // A pattern variable: if we've already bound it, the target must
        // match the existing binding exactly (consistency). Otherwise bind
        // it to `target` now, provided the sorts are compatible.
        Term::Var(name, sort) => {
            if let Some(existing) = bindings.get(name) {
                existing == target
            } else {
                if !sorts_compatible(sort, &target.sort()) { return false; }
                bindings.insert(name.clone(), target.clone());
                true
            }
        }
        // Constants must match the target exactly — `target` is rigid, so
        // there's nothing to bind here.
        Term::Const(_) => pattern == target,
        // Function applications: target must be the same function symbol
        // with the same arity, and every argument must match recursively.
        Term::Apply(p_name, p_args) => match target {
            Term::Apply(t_name, t_args) => {
                p_name == t_name
                    && p_args.len() == t_args.len()
                    && p_args.iter().zip(t_args).all(|(p, t)| pattern_match(p, t, bindings))
            }
            _ => false,
        },
    }
}

// ---------------------------------------------------------------------------
// Term rewriting / simplification ("simp" tactic)
// ---------------------------------------------------------------------------

/// Deterministically simplify `term` by repeatedly applying unconditional
/// equational axioms (`premises.is_empty()` and `conclusion: Eq(lhs, rhs)`)
/// as left-to-right rewrite rules, bottom-up.
///
/// This lets the engine pre-compute things like `Mul(2, 3) → 6` in one pass
/// instead of forcing IDDFS to "guess" a chain of `Eq_Trans` steps to get
/// there. The result is always a single, fully-reduced term — never a
/// search space.
///
/// # Algorithm
/// 1. If `term` is `Apply(f, args)`, recursively simplify every argument
///    first (bottom-up), producing `Apply(f, simplified_args)`.
/// 2. Try each unconditional equational axiom's LHS as a rewrite pattern
///    against the (possibly-rewritten) term via `pattern_match`.
/// 3. On the first match, substitute the resulting bindings into the
///    axiom's RHS and recursively `simplify_term` that — this lets one
///    rewrite trigger further rewrites (e.g. `Add(Mul(2,3), 0) → Add(6, 0)
///    → 6`).
/// 4. If no axiom matches, the (bottom-up-simplified) term is the final
///    result.
pub fn simplify_term(term: &Term, axioms: &[Axiom]) -> Term {
    // Step 1: simplify bottom-up — reduce all arguments first.
    let current_term = match term {
        Term::Apply(name, args) => {
            let simplified_args: Vec<Term> = args.iter()
                .map(|a| simplify_term(a, axioms))
                .collect();
            Term::Apply(name.clone(), simplified_args)
        }
        // Vars and Consts have no sub-terms to reduce.
        Term::Var(_, _) | Term::Const(_) => term.clone(),
    };

    // Step 2/3: try every unconditional equational axiom as a rewrite rule.
    for axiom in axioms {
        if !axiom.premises.is_empty() { continue; }
        if let Formula::Eq(lhs, rhs) = &axiom.conclusion {
            let mut bindings = Bindings::new();
            if pattern_match(lhs, &current_term, &mut bindings) {
                let rewritten = rhs.substitute(&bindings);
                
                // ---> THE FIX: PREVENT INFINITE REWRITE LOOPS <---
                // If the rewrite rule doesn't actually change the term 
                // (like Eq_Refl mapping `x` to `x`), ignore it!
                if rewritten == current_term {
                    continue;
                }

                // Keep reducing — the rewrite may expose new redexes.
                return simplify_term(&rewritten, axioms);
            }
        }
    }

    // Step 4: nothing more to do.
    current_term
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
// Forward chaining (deduction)
// ---------------------------------------------------------------------------

/// Find all binding maps that simultaneously satisfy every formula in
/// `premises` against the current `givens`.
///
/// This is the forward-chaining analogue of the backward-chaining DFS
/// premise loop.  It works by recursive backtracking:
///
/// 1. Base case — no premises left: the accumulated `bindings` is a valid
///    solution; return it as a singleton.
/// 2. Inductive step — take `premises[0]`, substitute any variables that
///    are already bound, then try to unify the result with every formula
///    currently in `givens`.  For each successful unification, merge the
///    new bindings and recurse on `premises[1..]`.
///
/// Because givens are ground (no free variables after substitution), the
/// unification step here is effectively one-way pattern matching: the
/// premise's variables get bound to concrete terms from the given, while
/// the given itself is never modified.
fn match_premises_forward(
    premises: &[Formula],
    givens:   &HashMap<String, Formula>,
    bindings: &Bindings,
) -> Vec<Bindings> {
    // Base case: all premises satisfied — the current binding set is valid.
    if premises.is_empty() {
        return vec![bindings.clone()];
    }

    let premise = &premises[0];
    let rest    = &premises[1..];

    // Substitute variables that are already known into this premise so
    // that the unification attempt sees the most-specific form.
    let premise_sub = premise.substitute(bindings);

    let mut results = Vec::new();

    for given_formula in givens.values() {
        // Try to unify the (partially-substituted) premise with this given.
        // `unify` treats *both* sides as potentially containing variables,
        // which is correct here: the premise may still have free axiom
        // variables that need to be bound to ground terms from the given.
        if let Some(new_bindings) = premise_sub.unify(given_formula) {
            // Merge the newly discovered bindings with the ones we already
            // have, then recurse on the remaining premises.
            let mut merged = bindings.clone();
            merged.extend(new_bindings);
            results.extend(match_premises_forward(rest, givens, &merged));
        }
    }

    results
}

/// Simplify a formula exactly as `prove` does before handing off to DFS:
/// reduce both sides of an equality, or the arguments of a predicate.
/// Other formula shapes are returned as-is.
fn simp_formula(f: Formula, axioms: &[Axiom]) -> Formula {
    match f {
        Formula::Eq(l, r) => {
            Formula::Eq(simplify_term(&l, axioms), simplify_term(&r, axioms))
        }
        Formula::Pred(name, args) => {
            Formula::Pred(name, args.iter().map(|a| simplify_term(a, axioms)).collect())
        }
        other => other,
    }
}

/// Apply all axioms forward against the universe's `givens` for up to
/// `max_steps` saturation rounds.
///
/// Each step:
/// 1. Iterates over every axiom (alpha-renamed to avoid variable clashes).
/// 2. Calls `match_premises_forward` to find all ground binding maps that
///    satisfy the axiom's premises using existing givens.
/// 3. For every valid binding, instantiates the conclusion and simplifies
///    it through the `simp` rewrite pass.
/// 4. Checks whether the simplified conclusion is already present in the
///    givens (by structural equality of formula values).
/// 5. If it is genuinely new, inserts it as `Deduction_N` and records it.
///
/// The loop terminates early if a full step produces no new facts
/// (fixpoint reached).  Returns the list of all newly discovered facts
/// as `(name, formula)` pairs in discovery order.
pub fn forward_deduce(
    universe: &mut Universe,
    max_steps: u32,
) -> Vec<(String, Formula)> {
    // Global deduction counter — survives across saturation steps so names
    // like `Deduction_3` are unique for the lifetime of the call.
    let mut deduction_counter: usize = 0;
    // Accumulate all discoveries to return to the caller.
    let mut all_new: Vec<(String, Formula)> = Vec::new();

    // A counter for alpha-renaming axioms.  Reused across steps and axioms
    // so every instantiation gets a globally unique variable suffix.
    let mut axiom_ctr: usize = 0;

    for _step in 0..max_steps {
        // Snapshot the set of known formula values at the start of this
        // step so we can detect fixpoint and check novelty without
        // re-hashing the live map mid-iteration.
        let known_formulas: Vec<Formula> = universe.givens.values().cloned().collect();

        let mut new_this_step: Vec<(String, Formula)> = Vec::new();

        // Clone the axiom list so we hold no borrow on `universe` while we
        // also need `&mut universe.givens` below.
        let axioms_snap = universe.axioms.clone();

        for axiom in &axioms_snap {
            // Skip zero-premise axioms that are unconditional equational
            // rewrite rules — they are already handled by `simp` and
            // re-deriving them as deductions would just flood the given set
            // with trivial noise (e.g. `Add(0, x) = x` for every x).
            // We do keep zero-premise *predicate* facts (statements like
            // `On(A, L)` stored as axioms) because they might be novel.
            if axiom.premises.is_empty() {
                if let Formula::Eq(_, _) = &axiom.conclusion {
                    // Unconditional equational rewrite — skip.
                    continue;
                }
            }

            // Alpha-rename so axiom variables are fresh for this use.
            axiom_ctr += 1;
            let fresh = instantiate_axiom(axiom, axiom_ctr);

            // Find all ways the premises can be satisfied by current givens.
            let binding_sets = match_premises_forward(
                &fresh.premises,
                &universe.givens,
                &HashMap::new(),
            );

            for bindings in binding_sets {
                // Instantiate the conclusion under these bindings.
                let conclusion = fresh.conclusion.substitute(&bindings);

                // Check: does the conclusion still contain unresolved axiom
                // variables (i.e. variables that weren't pinned by any
                // premise)?  If so, it is not ground — skip it.
                if formula_has_free_vars(&conclusion, &bindings) {
                    continue;
                }

                // Run the simp pass on the instantiated conclusion.
                let simplified = simp_formula(conclusion, &axioms_snap);

                // Is this conclusion already known?
                let already_known = known_formulas.contains(&simplified)
                    || new_this_step.iter().any(|(_, f)| f == &simplified)
                    || universe.givens.values().any(|f| f == &simplified);

                if !already_known {
                    deduction_counter += 1;
                    let name = format!("Deduction_{}", deduction_counter);
                    new_this_step.push((name, simplified));
                }
            }
        }

        // If nothing new was found this step we have reached a fixpoint.
        if new_this_step.is_empty() {
            break;
        }

        // Commit the new facts to the universe and record them globally.
        for (name, formula) in new_this_step {
            universe.givens.insert(name.clone(), formula.clone());
            all_new.push((name, formula));
        }
    }

    all_new
}

/// Return `true` if `formula` contains any `Term::Var` whose name is NOT
/// already fully resolved to a ground term in `bindings`.
///
/// Used after instantiating an axiom conclusion to ensure we only store
/// ground (variable-free) deductions in the given set.
fn formula_has_free_vars(formula: &Formula, bindings: &Bindings) -> bool {
    match formula {
        Formula::Eq(l, r)      => term_has_free_vars(l, bindings) || term_has_free_vars(r, bindings),
        Formula::Pred(_, args) => args.iter().any(|a| term_has_free_vars(a, bindings)),
        Formula::And(l, r) | Formula::Or(l, r) | Formula::Implies(l, r) =>
            formula_has_free_vars(l, bindings) || formula_has_free_vars(r, bindings),
        Formula::Not(i)        => formula_has_free_vars(i, bindings),
        Formula::Exists { body, .. } => formula_has_free_vars(body, bindings),
    }
}

fn term_has_free_vars(term: &Term, bindings: &Bindings) -> bool {
    let resolved = term.resolve(bindings);
    match resolved {
        Term::Var(_, _)      => true,   // unbound variable — not ground
        Term::Const(_)       => false,
        Term::Apply(_, args) => args.iter().any(|a| term_has_free_vars(a, bindings)),
    }
}

// ---------------------------------------------------------------------------
// Proof search (IDDFS)
// ---------------------------------------------------------------------------

/// Attempt to prove `goal` using axioms from the given `universe`.
pub fn prove(goal: &Formula, universe: &Universe, max_depth: u32) -> Option<ProofStep> {
    // ------------------------------------------------------------------
    // Term rewriting fast-path ("simp")
    //
    // Before falling back to IDDFS, deterministically simplify both sides
    // of an equality goal using the universe's unconditional equational
    // axioms (e.g. arithmetic facts like `Mul(2,3) = 6`). This collapses
    // long Eq_Trans chains that DFS would otherwise have to *search for*
    // into a single linear-time rewrite pass.
    // ------------------------------------------------------------------
    let goal = match goal {
        Formula::Eq(left, right) => {
            let simped_left  = simplify_term(left,  &universe.axioms);
            let simped_right = simplify_term(right, &universe.axioms);

            if simped_left == simped_right {
                // Fully reduced both sides to the same term — trivially true
                let refl_goal = Formula::Eq(simped_left.clone(), simped_right.clone());
                return Some(ProofStep::simple(refl_goal, "Eq_Refl", vec![]));
            }
            Formula::Eq(simped_left, simped_right)
        }
        Formula::Pred(name, args) => {
            // ---> NEW: Simplify arguments inside Logical Predicates! <---
            let simped_args: Vec<Term> = args.iter()
                .map(|a| simplify_term(a, &universe.axioms))
                .collect();
            Formula::Pred(name.clone(), simped_args)
        }
        _ => goal.clone(),
    };
    let goal = &goal;

    // ------------------------------------------------------------------
    // Forward lookup — Givens
    //
    // Before starting any IDDFS iteration, check whether the (simplified)
    // goal unifies directly with a named Given or Deduction.  This is
    // O(|givens|) and fires before any depth-1 search node is expanded.
    // ------------------------------------------------------------------
    for (given_name, given_formula) in &universe.givens {
        if let Some(_bindings) = given_formula.unify(goal) {
            return Some(ProofStep::simple(
                goal.clone(),
                format!("Given {}", given_name),
                vec![],
            ));
        }
    }

    let mut skolem_counter = 0u32;
    let mut axiom_counter  = 0usize;
    // Global node budget. Shared across the whole IDDFS run (all depths),
    // so a single call to `prove` can never expand more than this many
    // `prove_dfs` nodes in total, regardless of how many depth iterations
    // are attempted or how branchy the search tree becomes.
    let mut operations_budget: usize = 500_000;
    for depth in 1..=max_depth {
        println!("  {}", format!("[Searching depth {}...]", depth));
        let proofs = prove_dfs(goal, &universe.axioms, &universe.givens, depth, &HashMap::new(), &[], &mut skolem_counter, &mut axiom_counter, &mut operations_budget);
        if operations_budget == 0 {
            println!("  {}", "[Search budget exhausted — aborting.]".to_string());
        }
        if let Some((mut proof, final_bindings)) = proofs.into_iter().next() {
            // Wash the entire proof tree with the final resolved bindings so
            // that Skolem variables (?wN) and alpha-renamed axiom variables
            // (x_9) that were snapshotted with incomplete bindings during the
            // DFS are all replaced with their ultimate ground terms before the
            // formatter sees the tree.
            proof.apply_bindings(&final_bindings);
            return Some(proof);
        }
        if operations_budget == 0 {
            // No point iterating to greater depths — we've already spent
            // the entire search budget without finding a proof.
            break;
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
/// * `operations_budget` — Global node budget shared across the entire IDDFS
///   run. Decremented once per `prove_dfs` call; when it hits zero the
///   search is aborted everywhere by returning empty result sets, which
///   unwinds the whole recursion without finding (or claiming) a proof.
fn prove_dfs(
    goal:       &Formula,
    axioms:     &[Axiom],
    givens:     &HashMap<String, Formula>,
    depth:      u32,
    bindings:   &Bindings,
    path:       &[Formula],
    skolem_ctr: &mut u32,
    axiom_ctr:  &mut usize,
    operations_budget: &mut usize,
) -> Vec<(ProofStep, Bindings)> {
    if depth == 0 { return vec![]; }

    // ------------------------------------------------------------------
    // Global search budget (node cutoff)
    //
    // Each call to `prove_dfs` counts as one "node" expansion. Once the
    // shared budget is exhausted we abort immediately and unwind: every
    // caller up the stack will also see an empty result and stop too,
    // so this single check is enough to bound the *entire* search tree
    // (across all depths/branches) to `operations_budget` node visits.
    // ------------------------------------------------------------------
    if *operations_budget == 0 { return vec![]; }
    *operations_budget -= 1;

    let current_goal = goal.substitute(bindings);

    // ------------------------------------------------------------------
    // Syntactic equality fast-path  (Eq_Refl)
    //
    // If the goal is `a = b` and `a` and `b` are structurally identical
    // after substitution (e.g. `4 = 4`), it's trivially true by
    // reflexivity. Short-circuit here so the engine never wastes a
    // search node — let alone an entire branch of Eq_Trans/Eq_Sym/
    // Cong_* applications — trying to *derive* `4 = ?y AND ?y = 4`.
    // ------------------------------------------------------------------
    if let Formula::Eq(l, r) = &current_goal {
        if l == r {
            return vec![(ProofStep::simple(current_goal.clone(), "Eq_Refl", vec![]), bindings.clone())];
        }
    }

    // ------------------------------------------------------------------
    // Forward lookup — Givens (inside DFS)
    //
    // At every DFS node we check whether the current (substituted) goal
    // is directly entailed by a named Given or Deduction.  This handles
    // sub-goals that arise mid-search, e.g. an axiom's premise that
    // happens to match an established hypothesis.  The check is O(|givens|)
    // and short-circuits immediately on the first match, just like Eq_Refl.
    // ------------------------------------------------------------------
    for (given_name, given_formula) in givens {
        if let Some(new_bindings) = given_formula.unify(&current_goal) {
            let mut merged = bindings.clone();
            merged.extend(new_bindings);
            return vec![(
                ProofStep::simple(current_goal.clone(), format!("Given {}", given_name), vec![]),
                merged,
            )];
        }
    }

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
        for (p1, b1) in prove_dfs(left, axioms, givens, depth, bindings, &path2, skolem_ctr, axiom_ctr, operations_budget) {
            let right_sub = right.substitute(&b1);
            for (p2, b2) in prove_dfs(&right_sub, axioms, givens, depth, &b1, &path2, skolem_ctr, axiom_ctr, operations_budget) {
                results.push((
                    ProofStep::simple(current_goal.clone(), "Conjunction", vec![p1.clone(), p2]),
                    b2,
                ));
                if results.len() >= 3 { return results; } // <-- CAP
            }
        }
        return results;
    }

    // ------------------------------------------------------------------
    // Structural rule: Disjunction  (A ∨ B)
    // ------------------------------------------------------------------
    if let Formula::Or(left, right) = &current_goal {
        let mut path2 = path.to_vec(); path2.push(current_goal.clone());
        for (p, b) in prove_dfs(left, axioms, givens, depth, bindings, &path2, skolem_ctr, axiom_ctr, operations_budget) {
            results.push((ProofStep::simple(current_goal.clone(), "Disjunction_Left", vec![p]), b));
            if results.len() >= 3 { return results; } // <-- CAP
        }
        for (p, b) in prove_dfs(right, axioms, givens, depth, bindings, &path2, skolem_ctr, axiom_ctr, operations_budget) {
            results.push((ProofStep::simple(current_goal.clone(), "Disjunction_Right", vec![p]), b));
            if results.len() >= 3 { return results; } // <-- CAP
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

        for (sub_proof, final_bindings) in prove_dfs(&witness_goal, axioms, givens, depth - 1, &witness_bindings, &path2, skolem_ctr, axiom_ctr, operations_budget) {
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
            if results.len() >= 3 { return results; } // <-- CAP
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
                    let premise_proofs = prove_dfs(&p_sub, axioms, givens, depth - 1, &current_bindings, &path2, skolem_ctr, axiom_ctr, operations_budget);
                    
                    for (proof, b_out) in premise_proofs {
                        let mut next_proofs = sub_proofs_so_far.clone();
                        next_proofs.push(proof);
                        
                        let mut next_bindings = current_bindings.clone();
                        next_bindings.extend(b_out);
                        
                        next_states.push((next_proofs, next_bindings));
                        if next_states.len() >= 5 { break; } // <-- CAP
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
                if results.len() >= 3 { return results; } // <-- CAP
            }
        }
        if results.len() >= 3 { return results; } // <-- STOP CHECKING AXIOMS IF WE HAVE ENOUGH
        if *operations_budget == 0 { return results; } // <-- BUDGET EXHAUSTED, STOP EXPLORING
    }

    results
}
