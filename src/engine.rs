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
    pub fn infer_term_sort(&self, term: &Term) -> Result<Option<Sort>, String> {
        match term {
            Term::Var(_, sort) => {
                if sort == &Sort::object() {
                    Ok(None)
                } else {
                    Ok(Some(sort.clone()))
                }
            }

            Term::Const(name) => {
                Ok(self.constants.get(name).cloned())
            }

            Term::Apply(name, args) => {
                let Some((expected_sorts, return_sort)) = self.predicates.get(name) else {
                    return Ok(None);
                };

                if return_sort == "Prop" {
                    return Err(format!(
                            "{} is a predicate and cannot be used as a term",
                            name
                    ));
                }

                if args.len() != expected_sorts.len() {
                    return Err(format!(
                            "{} expects {} argument(s), but received {}",
                            name,
                            expected_sorts.len(),
                            args.len()
                    ));
                }

                for (index, (arg, expected)) in
                    args.iter().zip(expected_sorts).enumerate()
                {
                    if let Some(actual) = self.infer_term_sort(arg)? {
                        if actual.0 != *expected {
                            return Err(format!(
                                    "argument {} of {} expects {}, but received {}",
                                    index + 1,
                                    name,
                                    expected,
                                    actual
                            ));
                        }
                    }
                }

                Ok(Some(Sort(return_sort.clone())))
            }
        }
    }

    pub fn validate_formula(&self, formula: &Formula) -> Result<(), String> {
        match formula {
            Formula::Eq(left, right) => {
                let left_sort = self.infer_term_sort(left)?;
                let right_sort = self.infer_term_sort(right)?;

                if let (Some(left), Some(right)) = (left_sort, right_sort) {
                    if left != right {
                        return Err(format!(
                                "equality compares incompatible sorts: {} and {}",
                                left, right
                        ));
                    }
                }

                Ok(())
            }

            Formula::Pred(name, args) => {
                let Some((expected_sorts, return_sort)) = self.predicates.get(name) else {
                    return Err(format!("undeclared predicate: {}", name));
                };

                if return_sort != "Prop" {
                    return Err(format!(
                            "{} is not a predicate (its return sort is {})",
                            name, return_sort
                    ));
                }

                if args.len() != expected_sorts.len() {
                    return Err(format!(
                            "{} expects {} argument(s), but received {}",
                            name,
                            expected_sorts.len(),
                            args.len()
                    ));
                }

                for (index, (arg, expected)) in
                    args.iter().zip(expected_sorts).enumerate()
                {
                    if let Some(actual) = self.infer_term_sort(arg)? {
                        if actual.0 != *expected {
                            return Err(format!(
                                    "argument {} of {} expects {}, but received {}",
                                    index + 1,
                                    name,
                                    expected,
                                    actual
                            ));
                        }
                    }
                }

                Ok(())
            }

            Formula::And(left, right)
                | Formula::Or(left, right)
                | Formula::Implies(left, right) => {
                    self.validate_formula(left)?;
                    self.validate_formula(right)
                }

            Formula::Not(inner) => self.validate_formula(inner),

            Formula::Exists { body, .. } => {
                self.validate_formula(body)
            }
        }
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
/// Maximum number of rewrite steps performed during one simplification.
const MAX_SIMPLIFY_REWRITES: usize = 256;

/// Simplify a term using unconditional equational axioms.
///
/// Rewriting is bottom-up and deterministic. A rewrite chain stops when it
/// reaches a normal form, revisits a term on the current recursive path, or
/// consumes the rewrite budget. In the latter two cases the last
/// non-repeating term is returned; simplification is best-effort rather than
/// an unbounded process.
pub fn simplify_term(term: &Term, axioms: &[Axiom]) -> Term {
    let mut remaining = MAX_SIMPLIFY_REWRITES;
    simplify_term_inner(term, axioms, &mut remaining, &mut Vec::new())
}

fn simplify_term_inner(
    term: &Term,
    axioms: &[Axiom],
    remaining: &mut usize,
    active: &mut Vec<Term>,
) -> Term {
    // Simplify children first. The active path is shared so a rewrite such as
    // x -> f(x) cannot recursively normalize the same term forever.
    let current_term = match term {
        Term::Apply(name, args) => {
            let simplified_args: Vec<Term> = args
                .iter()
                .map(|arg| simplify_term_inner(arg, axioms, remaining, active))
                .collect();
            Term::Apply(name.clone(), simplified_args)
        }
        Term::Var(_, _) | Term::Const(_) => term.clone(),
    };

    if *remaining == 0 || active.contains(&current_term) {
        return current_term;
    }

    active.push(current_term.clone());

    for axiom in axioms {
        if !axiom.premises.is_empty() {
            continue;
        }

        if let Formula::Eq(lhs, rhs) = &axiom.conclusion {
            let mut bindings = Bindings::new();
            if pattern_match(lhs, &current_term, &mut bindings) {
                let rewritten = rhs.substitute(&bindings);

                if rewritten == current_term || active.contains(&rewritten) {
                    continue;
                }

                if *remaining == 0 {
                    break;
                }

                *remaining -= 1;
                let result = simplify_term_inner(&rewritten, axioms, remaining, active);
                active.pop();
                return result;
            }
        }
    }

    active.pop();
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
/// Match every premise, forcing one selected premise to use a fact from the
/// current delta. All other premises may use any known fact. This is the
/// semi-naive step: every produced binding is therefore anchored to at least
/// one fact that was not present in the previous iteration.
fn match_premises_forward_delta(
    premises: &[Formula],
    givens: &HashMap<String, Formula>,
    fact_index: &FactIndex,
    pivot_index: usize,
    delta_fact: &Formula,
    bindings: &Bindings,
) -> Vec<Bindings> {
    fn recurse(
        premises: &[Formula],
        givens: &HashMap<String, Formula>,
        fact_index: &FactIndex,
        pivot_index: usize,
        delta_fact: &Formula,
        position: usize,
        bindings: &Bindings,
    ) -> Vec<Bindings> {
        if position == premises.len() {
            return vec![bindings.clone()];
        }

        let premise = premises[position].substitute(bindings);
        let mut results = Vec::new();

        if position == pivot_index {
            if let Some(new_bindings) = premise.unify(delta_fact) {
                let mut merged = bindings.clone();
                merged.extend(new_bindings);
                results.extend(recurse(
                    premises, givens, fact_index, pivot_index, delta_fact,
                    position + 1, &merged,
                ));
            }
        } else {
            for given_name in fact_index.candidates(&premise) {
                let Some(given_formula) = givens.get(given_name) else { continue; };
                if let Some(new_bindings) = premise.unify(given_formula) {
                    let mut merged = bindings.clone();
                    merged.extend(new_bindings);
                    results.extend(recurse(
                        premises, givens, fact_index, pivot_index, delta_fact,
                        position + 1, &merged,
                    ));
                }
            }
        }

        results
    }

    if pivot_index >= premises.len() {
        return Vec::new();
    }

    recurse(
        premises, givens, fact_index, pivot_index, delta_fact, 0, bindings,
    )
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

/// Derive facts using semi-naive forward chaining.
///
/// The initial delta is the current fact database. Each subsequent iteration
/// contains only facts discovered in the preceding iteration. A rule is
/// reconsidered only when at least one of its premises can match a delta fact;
/// the remaining premises are matched against the complete known database.
pub fn forward_deduce(
    universe: &mut Universe,
    max_steps: u32,
) -> Vec<(String, Formula)> {
    use std::collections::HashSet;

    let axioms = universe.axioms.clone();
    let rule_index = ForwardAxiomIndex::new(&axioms);
    let mut known: HashSet<Formula> = universe.givens.values().cloned().collect();
    let mut delta = universe.givens.clone();
    let mut all_new = Vec::new();
    let mut deduction_counter = 0usize;
    let mut axiom_counter = 0usize;

    for step in 0..max_steps {
        if step > 0 && delta.is_empty() {
            break;
        }

        let delta_index = FactIndex::new(&delta);
        let known_index = FactIndex::new(&universe.givens);
        let mut new_this_step: Vec<(String, Formula)> = Vec::new();

        // Premise-free predicate axioms are facts in their own right. Process
        // them once, rather than once per saturation iteration.
        if step == 0 {
            for axiom in &axioms {
                if !axiom.premises.is_empty() {
                    continue;
                }
                if matches!(&axiom.conclusion, Formula::Eq(_, _)) {
                    continue;
                }

                axiom_counter += 1;
                let fresh = instantiate_axiom(axiom, axiom_counter);
                let conclusion = fresh.conclusion.substitute(&HashMap::new());
                if formula_has_free_vars(&conclusion, &HashMap::new()) {
                    continue;
                }
                let simplified = simp_formula(conclusion, &axioms);
                if known.insert(simplified.clone()) {
                    deduction_counter += 1;
                    new_this_step.push((
                        format!("Deduction_{}", deduction_counter),
                        simplified,
                    ));
                }
            }
        }

        for axiom_index in rule_index.candidates(&delta_index) {
            let axiom = &axioms[axiom_index];
            axiom_counter += 1;
            let fresh = instantiate_axiom(axiom, axiom_counter);

            // Each premise may act as the delta pivot. This also handles rules
            // where two or more premises are all satisfied by new facts.
            for (pivot_index, pivot_premise) in fresh.premises.iter().enumerate() {
                for delta_name in delta_index.candidates(pivot_premise) {
                    let Some(delta_fact) = delta.get(delta_name) else { continue; };
                    let binding_sets = match_premises_forward_delta(
                        &fresh.premises,
                        &universe.givens,
                        &known_index,
                        pivot_index,
                        delta_fact,
                        &HashMap::new(),
                    );

                    for bindings in binding_sets {
                        let conclusion = fresh.conclusion.substitute(&bindings);
                        if formula_has_free_vars(&conclusion, &bindings) {
                            continue;
                        }

                        let simplified = simp_formula(conclusion, &axioms);
                        if known.insert(simplified.clone()) {
                            deduction_counter += 1;
                            new_this_step.push((
                                format!("Deduction_{}", deduction_counter),
                                simplified,
                            ));
                        }
                    }
                }
            }
        }

        if new_this_step.is_empty() {
            break;
        }

        let mut next_delta = HashMap::new();
        for (name, formula) in new_this_step {
            universe.givens.insert(name.clone(), formula.clone());
            next_delta.insert(name.clone(), formula.clone());
            all_new.push((name, formula));
        }
        delta = next_delta;
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


#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum FormulaHead {
    Predicate(String, usize),
    Equality,
    And,
    Or,
    Not,
    Implies,
    Exists,
}

fn formula_head(formula: &Formula) -> FormulaHead {
    match formula {
        Formula::Pred(name, args) => FormulaHead::Predicate(name.clone(), args.len()),
        Formula::Eq(_, _) => FormulaHead::Equality,
        Formula::And(_, _) => FormulaHead::And,
        Formula::Or(_, _) => FormulaHead::Or,
        Formula::Not(_) => FormulaHead::Not,
        Formula::Implies(_, _) => FormulaHead::Implies,
        Formula::Exists { .. } => FormulaHead::Exists,
    }
}

/// Index forward rules by every premise head, allowing any premise to
/// trigger a rule when a matching delta fact arrives.
#[derive(Debug, Default)]
struct ForwardAxiomIndex {
    by_premise_head: HashMap<FormulaHead, Vec<usize>>,
}

impl ForwardAxiomIndex {
    fn new(axioms: &[Axiom]) -> Self {
        let mut index = Self::default();
        for (position, axiom) in axioms.iter().enumerate() {
            for premise in &axiom.premises {
                index.by_premise_head
                    .entry(formula_head(premise))
                    .or_default()
                    .push(position);
            }
        }
        for positions in index.by_premise_head.values_mut() {
            positions.sort_unstable();
            positions.dedup();
        }
        index
    }

    fn candidates(&self, delta: &FactIndex) -> Vec<usize> {
        let mut candidates = Vec::new();
        for (head, positions) in &self.by_premise_head {
            if delta.contains_head(head) {
                candidates.extend_from_slice(positions);
            }
        }
        candidates.sort_unstable();
        candidates.dedup();
        candidates
    }
}

/// Index named facts by formula head for forward-premise matching.
#[derive(Debug, Default)]
struct FactIndex {
    by_head: HashMap<FormulaHead, Vec<String>>,
}

impl FactIndex {
    fn new(givens: &HashMap<String, Formula>) -> Self {
        let mut index = Self::default();
        for (name, formula) in givens {
            index.by_head.entry(formula_head(formula))
                .or_default().push(name.clone());
        }
        for names in index.by_head.values_mut() {
            names.sort();
        }
        index
    }

    fn contains_head(&self, head: &FormulaHead) -> bool {
        self.by_head.contains_key(head)
    }

    fn candidates(&self, formula: &Formula) -> &[String] {
        self.by_head.get(&formula_head(formula))
            .map(Vec::as_slice).unwrap_or(&[])
    }
}

/// Per-proof indexes. They store positions/names, not cloned formulas.
#[derive(Debug, Default)]
struct ProofSearchIndex {
    axioms_by_head: HashMap<FormulaHead, Vec<usize>>,
    givens_by_head: HashMap<FormulaHead, Vec<String>>,
}

impl ProofSearchIndex {
    fn new(axioms: &[Axiom], givens: &HashMap<String, Formula>) -> Self {
        let mut index = Self::default();
        for (position, axiom) in axioms.iter().enumerate() {
            index.axioms_by_head
                .entry(formula_head(&axiom.conclusion))
                .or_default()
                .push(position);
        }
        for (name, formula) in givens {
            index.givens_by_head
                .entry(formula_head(formula))
                .or_default()
                .push(name.clone());
        }
        index
    }

    fn axiom_candidates(&self, goal: &Formula) -> &[usize] {
        self.axioms_by_head.get(&formula_head(goal))
            .map(Vec::as_slice).unwrap_or(&[])
    }

    fn given_candidates(&self, goal: &Formula) -> &[String] {
        self.givens_by_head.get(&formula_head(goal))
            .map(Vec::as_slice).unwrap_or(&[])
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
    let search_index = ProofSearchIndex::new(&universe.axioms, &universe.givens);

    for given_name in search_index.given_candidates(goal) {
        if let Some(given_formula) = universe.givens.get(given_name) {
            if let Some(_bindings) = given_formula.unify(goal) {
                return Some(ProofStep::simple(
                        goal.clone(),
                        format!("Given {}", given_name),
                        vec![],
                ));
            }
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
        let proofs = prove_dfs(goal, &universe.axioms, &universe.givens, &search_index, depth, &HashMap::new(), &[], &mut skolem_counter, &mut axiom_counter, &mut operations_budget);
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

pub fn prove_checked(
    goal: &Formula,
    universe: &Universe,
    max_depth: u32,
) -> Result<Option<ProofStep>, String> {
    universe.validate_formula(goal)?;

    Ok(prove(goal, universe, max_depth))
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
    search_index: &ProofSearchIndex,
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
    for given_name in search_index.given_candidates(&current_goal) {
        if let Some(given_formula) = givens.get(given_name) {
            if let Some(new_bindings) = given_formula.unify(&current_goal) {
                let mut merged = bindings.clone();
                merged.extend(new_bindings);
                return vec![(
                    ProofStep::simple(current_goal.clone(), format!("Given {}", given_name), vec![]),
                    merged,
                )];
            }
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
        for (p1, b1) in prove_dfs(left, axioms, givens, search_index, depth, bindings, &path2, skolem_ctr, axiom_ctr, operations_budget) {
            let right_sub = right.substitute(&b1);
            for (p2, b2) in prove_dfs(&right_sub, axioms, givens, search_index, depth, &b1, &path2, skolem_ctr, axiom_ctr, operations_budget) {
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
        for (p, b) in prove_dfs(left, axioms, givens, search_index, depth, bindings, &path2, skolem_ctr, axiom_ctr, operations_budget) {
            results.push((ProofStep::simple(current_goal.clone(), "Disjunction_Left", vec![p]), b));
            if results.len() >= 3 { return results; } // <-- CAP
        }
        for (p, b) in prove_dfs(right, axioms, givens, search_index, depth, bindings, &path2, skolem_ctr, axiom_ctr, operations_budget) {
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

        for (sub_proof, final_bindings) in prove_dfs(&witness_goal, axioms, givens, search_index, depth - 1, &witness_bindings, &path2, skolem_ctr, axiom_ctr, operations_budget) {
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

    for &axiom_index in search_index.axiom_candidates(&current_goal) {
        let axiom = &axioms[axiom_index];
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
                    let premise_proofs = prove_dfs(&p_sub, axioms, givens, search_index, depth - 1, &current_bindings, &path2, skolem_ctr, axiom_ctr, operations_budget);

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

#[cfg(test)]
mod sort_inference_tests {
    use super::*;
    use crate::ast::Sort;

    #[test]
    fn infers_constant_sort() {
        let mut universe = Universe::new();
        universe.add_constant("alice".into(), Sort("Person".into()));

        assert_eq!(
            universe.infer_term_sort(&Term::Const("alice".into())),
            Ok(Some(Sort("Person".into())))
        );
    }

    #[test]
    fn infers_function_return_sort() {
        let mut universe = Universe::new();
        universe.add_predicate(
            "FatherOf".into(),
            vec!["Person".into()],
            "Person".into(),
        );
        universe.add_constant("alice".into(), Sort("Person".into()));

        let term = Term::Apply(
            "FatherOf".into(),
            vec![Term::Const("alice".into())],
        );

        assert_eq!(
            universe.infer_term_sort(&term),
            Ok(Some(Sort("Person".into())))
        );
    }

    #[test]
    fn rejects_function_argument_sort_mismatch() {
        let mut universe = Universe::new();
        universe.add_predicate(
            "FatherOf".into(),
            vec!["Person".into()],
            "Person".into(),
        );
        universe.add_constant("red".into(), Sort("Color".into()));

        let term = Term::Apply(
            "FatherOf".into(),
            vec![Term::Const("red".into())],
        );

        assert!(universe.infer_term_sort(&term).is_err());
    }

    #[test]
    fn rejects_function_arity_mismatch() {
        let mut universe = Universe::new();
        universe.add_predicate(
            "FatherOf".into(),
            vec!["Person".into()],
            "Person".into(),
        );

        let term = Term::Apply("FatherOf".into(), vec![]);

        assert!(universe.infer_term_sort(&term).is_err());
    }

    #[test]
    fn leaves_unannotated_variable_sort_unknown() {
        let universe = Universe::new();

        assert_eq!(
            universe.infer_term_sort(&Term::Var("x".into(), Sort::object())),
            Ok(None)
        );
    }

    #[test]
    fn accepts_valid_predicate() {
        let mut universe = Universe::new();
        universe.add_constant("alice".into(), Sort("Person".into()));
        universe.add_predicate(
            "Human".into(),
            vec!["Person".into()],
            "Prop".into(),
        );

        let formula = Formula::Pred(
            "Human".into(),
            vec![Term::Const("alice".into())],
        );

        assert!(universe.validate_formula(&formula).is_ok());
    }

#[test]
    fn rejects_predicate_argument_sort_mismatch() {
        let mut universe = Universe::new();
        universe.add_constant("red".into(), Sort("Color".into()));
        universe.add_predicate(
            "Human".into(),
            vec!["Person".into()],
            "Prop".into(),
        );

        let formula = Formula::Pred(
            "Human".into(),
            vec![Term::Const("red".into())],
        );

        assert!(universe.validate_formula(&formula).is_err());
    }

#[test]
    fn rejects_equality_between_different_sorts() {
        let mut universe = Universe::new();
        universe.add_constant("alice".into(), Sort("Person".into()));
        universe.add_constant("red".into(), Sort("Color".into()));

        let formula = Formula::Eq(
            Term::Const("alice".into()),
            Term::Const("red".into()),
        );

        assert!(universe.validate_formula(&formula).is_err());
    }
}

#[test]
fn rejects_predicate_used_as_term() {
    let mut universe = Universe::new();

    universe.add_constant("alice".into(), Sort("Person".into()));
    universe.add_predicate(
        "Human".into(),
        vec!["Person".into()],
        "Prop".into(),
    );

    let term = Term::Apply(
        "Human".into(),
        vec![Term::Const("alice".into())],
    );

    assert!(universe.infer_term_sort(&term).is_err());
}

#[cfg(test)]
mod simplifier_termination_tests {
    use super::*;

    fn rewrite(lhs: Term, rhs: Term) -> Axiom {
        Axiom {
            name: "rewrite".into(),
            vars: vec![],
            premises: vec![],
            conclusion: Formula::Eq(lhs, rhs),
        }
    }

    #[test]
    fn simplifier_stops_on_two_rule_cycles() {
        let axioms = vec![
            rewrite(Term::Const("A".into()), Term::Const("B".into())),
            rewrite(Term::Const("B".into()), Term::Const("A".into())),
        ];

        // The second rewrite would revisit A, so the engine returns B.
        assert_eq!(
            simplify_term(&Term::Const("A".into()), &axioms),
            Term::Const("B".into())
        );
    }

    #[test]
    fn simplifier_stops_when_rewrite_budget_is_exhausted() {
        let variable = Term::Var("x".into(), Sort::object());
        let expanding_rule = rewrite(
            variable.clone(),
            Term::Apply("f".into(), vec![variable]),
        );

        let result = simplify_term(&Term::Const("a".into()), &[expanding_rule]);

        fn unary_depth(term: &Term) -> usize {
            match term {
                Term::Apply(name, args) if name == "f" && args.len() == 1 => {
                    1 + unary_depth(&args[0])
                }
                _ => 0,
            }
        }

        assert_eq!(unary_depth(&result), MAX_SIMPLIFY_REWRITES);
    }
}
#[cfg(test)]
mod proof_search_index_tests {
    use super::*;

    fn axiom(name: &str, conclusion: Formula) -> Axiom {
        Axiom { name: name.into(), vars: vec![], premises: vec![], conclusion }
    }

    #[test]
    fn index_filters_predicates_by_name_and_arity() {
        let axioms = vec![
            axiom("P1", Formula::Pred("P".into(), vec![Term::Const("a".into())])),
            axiom("P2", Formula::Pred("P".into(), vec![
                Term::Const("a".into()), Term::Const("b".into()),
            ])),
            axiom("Q1", Formula::Pred("Q".into(), vec![Term::Const("a".into())])),
        ];
        let givens = HashMap::from([
            ("p".into(), Formula::Pred("P".into(), vec![Term::Const("a".into())])),
            ("q".into(), Formula::Pred("Q".into(), vec![Term::Const("a".into())])),
        ]);
        let index = ProofSearchIndex::new(&axioms, &givens);
        let goal = Formula::Pred("P".into(), vec![Term::Var("x".into(), Sort::object())]);

        assert_eq!(index.axiom_candidates(&goal), &[0]);
        assert_eq!(index.given_candidates(&goal), &["p".to_string()]);
        assert!(index.axiom_candidates(&Formula::Pred("Missing".into(), vec![])).is_empty());
    }

    #[test]
    fn index_separates_formula_constructors() {
        let axioms = vec![
            axiom("eq", Formula::Eq(Term::Const("a".into()), Term::Const("a".into()))),
            axiom("not", Formula::Not(Box::new(Formula::Pred("P".into(), vec![])))),
        ];
        let index = ProofSearchIndex::new(&axioms, &HashMap::new());

        assert_eq!(index.axiom_candidates(&Formula::Eq(
            Term::Var("x".into(), Sort::object()),
            Term::Var("y".into(), Sort::object()),
        )), &[0]);
        assert_eq!(index.axiom_candidates(&Formula::Not(Box::new(
            Formula::Pred("Q".into(), vec![]),
        ))), &[1]);
        assert!(index.axiom_candidates(&Formula::Pred("P".into(), vec![])).is_empty());
    }
}
#[cfg(test)]
mod forward_index_tests {
    use super::*;

    #[test]
    fn forward_indexes_filter_irrelevant_rules_and_facts() {
        let p = Formula::Pred("P".into(), vec![Term::Const("a".into())]);
        let q = Formula::Pred("Q".into(), vec![Term::Const("a".into())]);
        let r = Formula::Pred("R".into(), vec![Term::Const("a".into())]);
        let axioms = vec![
            Axiom { name: "P_to_R".into(), vars: vec![], premises: vec![p.clone()], conclusion: r.clone() },
            Axiom { name: "Q_to_R".into(), vars: vec![], premises: vec![q.clone()], conclusion: r.clone() },
            Axiom { name: "Fact_R".into(), vars: vec![], premises: vec![], conclusion: r.clone() },
        ];
        let givens = HashMap::from([("known_p".into(), p)]);
        let fact_index = FactIndex::new(&givens);
        let rule_index = ForwardAxiomIndex::new(&axioms);

        assert_eq!(rule_index.candidates(&fact_index), vec![0]);
        assert_eq!(fact_index.candidates(&q).len(), 0);
        assert_eq!(fact_index.candidates(&Formula::Pred("P".into(), vec![
            Term::Var("x".into(), Sort::object()),
        ])).len(), 1);
    }

    #[test]
    fn premise_matching_uses_index_without_changing_bindings() {
        let premise = Formula::Pred("P".into(), vec![Term::Var("x".into(), Sort::object())]);
        let fact = Formula::Pred("P".into(), vec![Term::Const("alice".into())]);
        let givens = HashMap::from([("alice_is_p".into(), fact)]);
        let index = FactIndex::new(&givens);

        let matches = match_premises_forward_delta(
            &[premise], &givens, &index, 0, &Formula::Pred(
                "P".into(), vec![Term::Const("alice".into())],
            ), &HashMap::new(),
        );
        assert_eq!(matches.len(), 1);
        assert_eq!(matches[0].get("x"), Some(&Term::Const("alice".into())));
    }
    #[test]
    fn semi_naive_deduction_uses_new_facts_as_non_first_premises() {
        let mut universe = Universe::new();
        let x = Term::Var("x".into(), Sort::object());
        let a = Term::Const("a".into());
        let pred = |name: &str, term: Term| Formula::Pred(name.into(), vec![term]);

        universe.givens.insert("p_a".into(), pred("P", a.clone()));
        universe.givens.insert("s_a".into(), pred("S", a.clone()));

        universe.add_axiom(Axiom {
            name: "S_implies_Q".into(),
            vars: vec!["x".into()],
            premises: vec![pred("S", x.clone())],
            conclusion: pred("Q", x.clone()),
        });
        universe.add_axiom(Axiom {
            name: "P_and_Q_implies_R".into(),
            vars: vec!["x".into()],
            premises: vec![pred("P", x.clone()), pred("Q", x.clone())],
            conclusion: pred("R", x),
        });

        let derived = forward_deduce(&mut universe, 5);
        assert!(derived.iter().any(|(_, f)| *f == pred("Q", a.clone())));
        assert!(derived.iter().any(|(_, f)| *f == pred("R", a.clone())));
    }

    #[test]
    fn semi_naive_deduction_emits_premise_free_facts_once() {
        let mut universe = Universe::new();
        universe.add_axiom(Axiom {
            name: "BaseFact".into(),
            vars: vec![],
            premises: vec![],
            conclusion: Formula::Pred("Base".into(), vec![Term::Const("a".into())]),
        });

        let derived = forward_deduce(&mut universe, 5);
        assert_eq!(derived.len(), 1);
        assert_eq!(derived[0].1, Formula::Pred("Base".into(), vec![Term::Const("a".into())]));
    }

}
