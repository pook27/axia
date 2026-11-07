use std::cell::Cell;
use std::collections::HashMap;
use crate::ast::{Term, Formula, Sort, VarId};

pub type Bindings = HashMap<VarId, Term>;

// ---------------------------------------------------------------------------
// Proof tree
// ---------------------------------------------------------------------------

/// The logical rule used at a proof-tree node. Display labels are deliberately
/// kept separate from the constructors consumed by the trusted checker.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ProofRule {
    EqualityReflexivity,
    Given(String),
    Axiom(String, Bindings),
    ConjunctionIntroduction,
    DisjunctionIntroductionLeft,
    DisjunctionIntroductionRight,
    ExistentialIntroduction,
}

impl ProofRule {
    pub fn label(&self) -> &str {
        match self {
            Self::EqualityReflexivity => "Eq_Refl",
            Self::Given(name) => name,
            Self::Axiom(name, _) => name,
            Self::ConjunctionIntroduction => "Conjunction",
            Self::DisjunctionIntroductionLeft => "Disjunction_Left",
            Self::DisjunctionIntroductionRight => "Disjunction_Right",
            Self::ExistentialIntroduction => "Existential_Instantiation",
        }
    }
}

/// One node in a successful proof tree.
#[derive(Debug, Clone)]
pub struct ProofStep {
    /// The formula that was proved at this node, with all bindings applied.
    pub goal: Formula,
    /// Typed logical constructor; never infer semantics from a display string.
    pub rule: ProofRule,
    /// Sub-goals that had to be proved to discharge this goal.
    pub sub_proofs: Vec<ProofStep>,
    /// Existential witnesses introduced at this step (may be empty).
    pub witnesses: Vec<(String, Term)>,
}

impl ProofStep {
    /// Convenience constructor for steps with no witnesses.
    fn simple(goal: Formula, rule: ProofRule, sub_proofs: Vec<ProofStep>) -> Self {
        ProofStep { goal, rule, sub_proofs, witnesses: vec![] }
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
        if let ProofRule::Axiom(_, instantiations) = &mut self.rule {
            for term in instantiations.values_mut() {
                *term = term.substitute(bindings);
            }
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
    pub vars:       Vec<VarId>,
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
    /// Explicitly trusted assumptions supplied by the user or imported theory.
    /// These are premises of the current logical context, not engine results.
    pub assumptions: HashMap<String, Formula>,
    /// Consequences discovered by forward deduction. Kept separate so callers
    /// can inspect the trust boundary instead of treating derived facts as input.
    pub derived: HashMap<String, Formula>,
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

    /// Add a trusted, named assumption to this universe.
    pub fn add_given(&mut self, name: String, formula: Formula) {
        self.assumptions.insert(name, formula);
    }

    /// Add a fact discovered by the reasoning engine.
    pub fn add_derived(&mut self, name: String, formula: Formula) {
        self.derived.insert(name, formula);
    }

    /// Return the complete fact view used by the reasoning engine.
    /// The source maps remain separate; assumptions take precedence if a
    /// caller has reused a name in both namespaces.
    pub fn all_facts(&self) -> HashMap<String, Formula> {
        let mut facts = self.derived.clone();
        facts.extend(self.assumptions.clone());
        facts
    }

    pub fn summary(&self) -> String {
        format!(
            "{} axiom(s), {} type(s), {} predicate(s), {} constant(s), {} assumption(s), {} derived fact(s)",
            self.axioms.len(), self.types.len(),
            self.predicates.len(), self.constants.len(),
            self.assumptions.len(), self.derived.len(),
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

// Helpers for name-based alpha-renaming. These keep the current AST compatible
// while ensuring that a binder never captures a variable introduced by a
// substitution. A future VarId migration can replace this machinery.
fn term_contains_variable(term: &Term, name: &VarId) -> bool {
    match term {
        Term::Var(variable, _) => variable == name,
        Term::Const(_) => false,
        Term::Apply(_, args) => args.iter().any(|arg| term_contains_variable(arg, name)),
    }
}

fn formula_contains_variable(formula: &Formula, name: &VarId) -> bool {
    match formula {
        Formula::Eq(left, right) =>
            term_contains_variable(left, name) || term_contains_variable(right, name),
        Formula::Pred(_, args) => args.iter().any(|arg| term_contains_variable(arg, name)),
        Formula::And(left, right)
        | Formula::Or(left, right)
        | Formula::Implies(left, right) =>
            formula_contains_variable(left, name) || formula_contains_variable(right, name),
        Formula::Not(inner) => formula_contains_variable(inner, name),
        Formula::Exists { var, body, .. } =>
            var == name || formula_contains_variable(body, name),
    }
}

fn rename_bound_term(term: &Term, old: &VarId, new: &VarId) -> Term {
    match term {
        Term::Var(name, sort) if name == old => Term::Var(new.clone(), sort.clone()),
        Term::Var(_, _) | Term::Const(_) => term.clone(),
        Term::Apply(name, args) => Term::Apply(
            name.clone(),
            args.iter().map(|arg| rename_bound_term(arg, old, new)).collect(),
        ),
    }
}

/// Rename occurrences bound by the surrounding quantifier. A nested
/// quantifier using the same name shadows it, so its body is left untouched.
fn rename_bound_occurrences(formula: &Formula, old: &VarId, new: &VarId) -> Formula {
    match formula {
        Formula::Eq(left, right) => Formula::Eq(
            rename_bound_term(left, old, new),
            rename_bound_term(right, old, new),
        ),
        Formula::Pred(name, args) => Formula::Pred(
            name.clone(),
            args.iter().map(|arg| rename_bound_term(arg, old, new)).collect(),
        ),
        Formula::And(left, right) => Formula::And(
            Box::new(rename_bound_occurrences(left, old, new)),
            Box::new(rename_bound_occurrences(right, old, new)),
        ),
        Formula::Or(left, right) => Formula::Or(
            Box::new(rename_bound_occurrences(left, old, new)),
            Box::new(rename_bound_occurrences(right, old, new)),
        ),
        Formula::Not(inner) => Formula::Not(Box::new(rename_bound_occurrences(inner, old, new))),
        Formula::Implies(left, right) => Formula::Implies(
            Box::new(rename_bound_occurrences(left, old, new)),
            Box::new(rename_bound_occurrences(right, old, new)),
        ),
        Formula::Exists { var, .. } if var == old => formula.clone(),
        Formula::Exists { var, sort, body } => Formula::Exists {
            var: var.clone(),
            sort: sort.clone(),
            body: Box::new(rename_bound_occurrences(body, old, new)),
        },
    }
}

fn fresh_alpha_name(base: &VarId, formulas: &[&Formula], bindings: &Bindings) -> VarId {
    let mut suffix = 0usize;
    loop {
        let candidate = base.derived(&format!("__alpha{suffix}"));
        let used_in_formula = formulas
            .iter()
            .any(|formula| formula_contains_variable(formula, &candidate));
        let used_in_bindings = bindings.contains_key(&candidate)
            || bindings.values().any(|term| term_contains_variable(term, &candidate));
        if !used_in_formula && !used_in_bindings {
            return candidate;
        }
        suffix += 1;
    }
}

impl Formula {
    /// Apply a capture-avoiding substitution.
    ///
    /// Bound variables are first removed from the active substitution. If any
    /// remaining substitution value contains the binder's name, the binder is
    /// alpha-renamed before substitution is applied to its body.
    pub fn substitute(&self, bindings: &Bindings) -> Formula {
        match self {
            Formula::Eq(left, right) =>
                Formula::Eq(left.substitute(bindings), right.substitute(bindings)),
            Formula::Pred(name, args) => Formula::Pred(
                name.clone(),
                args.iter().map(|arg| arg.substitute(bindings)).collect(),
            ),
            Formula::And(left, right) => Formula::And(
                Box::new(left.substitute(bindings)),
                Box::new(right.substitute(bindings)),
            ),
            Formula::Or(left, right) => Formula::Or(
                Box::new(left.substitute(bindings)),
                Box::new(right.substitute(bindings)),
            ),
            Formula::Not(inner) => Formula::Not(Box::new(inner.substitute(bindings))),
            Formula::Implies(left, right) => Formula::Implies(
                Box::new(left.substitute(bindings)),
                Box::new(right.substitute(bindings)),
            ),
            Formula::Exists { var, sort, body } => {
                let mut inner_bindings = bindings.clone();
                inner_bindings.remove(var);

                let would_capture = inner_bindings
                    .values()
                    .any(|term| term_contains_variable(term, var));

                if would_capture {
                    let fresh = fresh_alpha_name(var, &[body], &inner_bindings);
                    let renamed_body = rename_bound_occurrences(body, var, &fresh);
                    Formula::Exists {
                        var: fresh,
                        sort: sort.clone(),
                        body: Box::new(renamed_body.substitute(&inner_bindings)),
                    }
                } else {
                    Formula::Exists {
                        var: var.clone(),
                        sort: sort.clone(),
                        body: Box::new(body.substitute(&inner_bindings)),
                    }
                }
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Rollback-capable substitutions and unification
// ---------------------------------------------------------------------------

/// A substitution environment with an undo trail.
///
/// A checkpoint is the current trail length. Any bindings introduced after
/// that point can be discarded in O(number of changes), without cloning the
/// complete environment. This is the primitive used by the search engine when
/// it explores alternatives.
#[derive(Debug, Clone, Default)]
pub struct Substitution {
    bindings: Bindings,
    trail: Vec<(VarId, Option<Term>)>,
}

impl Substitution {
    pub fn new() -> Self { Self::default() }

    pub fn from_bindings(bindings: Bindings) -> Self {
        Self { bindings, trail: Vec::new() }
    }

    pub fn checkpoint(&self) -> usize { self.trail.len() }

    pub fn rollback(&mut self, checkpoint: usize) {
        assert!(checkpoint <= self.trail.len(), "invalid substitution checkpoint");
        while self.trail.len() > checkpoint {
            let (name, previous) = self.trail.pop().expect("trail length checked");
            match previous {
                Some(term) => { self.bindings.insert(name, term); }
                None => { self.bindings.remove(&name); }
            }
        }
    }

    pub fn bind(&mut self, name: VarId, term: Term) {
        let previous = self.bindings.insert(name.clone(), term);
        self.trail.push((name, previous));
    }

    pub fn resolve(&self, term: &Term) -> Term {
        term.substitute(&self.bindings)
    }

    pub fn get(&self, name: &VarId) -> Option<&Term> {
        self.bindings.get(name)
    }

    pub fn as_bindings(&self) -> &Bindings { &self.bindings }

    pub fn into_bindings(self) -> Bindings { self.bindings }

    /// Unify two terms transactionally. On failure, this call leaves the
    /// environment exactly as it was before the call.
    pub fn unify_terms(&mut self, left: &Term, right: &Term) -> bool {
        let checkpoint = self.checkpoint();
        if unify_terms_inner(left, right, self) {
            true
        } else {
            self.rollback(checkpoint);
            false
        }
    }

    /// Unify two formulas transactionally. This is the reusable entry point
    /// for proof search; callers can checkpoint once and roll back an entire
    /// candidate branch without copying a HashMap.
    pub fn unify_formulas(&mut self, left: &Formula, right: &Formula) -> bool {
        let checkpoint = self.checkpoint();
        if unify_formulas_inner(left, right, self) {
            true
        } else {
            self.rollback(checkpoint);
            false
        }
    }
}

fn unify_formulas_inner(left: &Formula, right: &Formula, subst: &mut Substitution) -> bool {
    match (left, right) {
        (Formula::Pred(n1, a1), Formula::Pred(n2, a2)) =>
            n1 == n2 && a1.len() == a2.len()
            && a1.iter().zip(a2).all(|(a, b)| unify_terms_inner(a, b, subst)),
        (Formula::Eq(l1, r1), Formula::Eq(l2, r2)) =>
            unify_terms_inner(l1, l2, subst) && unify_terms_inner(r1, r2, subst),
        (Formula::Not(a), Formula::Not(b)) => unify_formulas_inner(a, b, subst),
        (Formula::And(l1, r1), Formula::And(l2, r2))
        | (Formula::Or(l1, r1), Formula::Or(l2, r2))
        | (Formula::Implies(l1, r1), Formula::Implies(l2, r2)) =>
            unify_formulas_inner(l1, l2, subst)
            && unify_formulas_inner(r1, r2, subst),
        (
            Formula::Exists { var: v1, sort: s1, body: b1 },
            Formula::Exists { var: v2, sort: s2, body: b2 },
        ) => {
            if s1 != s2 {
                false
            } else {
                // Compare quantified formulas modulo binder names. Pick a name
                // absent from both bodies so renaming cannot capture free vars.
                let fresh = fresh_alpha_name(v1, &[b1, b2], subst.as_bindings());
                let left = rename_bound_occurrences(b1, v1, &fresh);
                let right = rename_bound_occurrences(b2, v2, &fresh);
                unify_formulas_inner(&left, &right, subst)
            }
        },
        _ => false,
    }
}

fn unify_terms_inner(left: &Term, right: &Term, subst: &mut Substitution) -> bool {
    let left = subst.resolve(left);
    let right = subst.resolve(right);

    match (left, right) {
        (Term::Var(n1, s1), Term::Var(n2, s2)) => {
            if n1 == n2 { return true; }
            if !sorts_compatible(&s1, &s2) { return false; }
            subst.bind(n1, Term::Var(n2, s2));
            true
        }
        (Term::Var(name, sort), value) | (value, Term::Var(name, sort)) => {
            if occurs_check(&name, &value, subst.as_bindings()) { return false; }
            if !sorts_compatible(&sort, &value.sort()) { return false; }
            subst.bind(name, value);
            true
        }
        (Term::Const(a), Term::Const(b)) => a == b,
        (Term::Apply(n1, a1), Term::Apply(n2, a2)) =>
            n1 == n2 && a1.len() == a2.len()
            && a1.iter().zip(&a2).all(|(a, b)| unify_terms_inner(a, b, subst)),
        _ => false,
    }
}

impl Formula {
    /// Compatibility API returning an owned binding map.
    pub fn unify(&self, goal: &Formula) -> Option<Bindings> {
        let mut subst = Substitution::new();
        if subst.unify_formulas(self, goal) {
            Some(subst.into_bindings())
        } else {
            None
        }
    }

    /// Transactional API for callers that want to reuse one substitution
    /// environment across several unification attempts.
    pub fn unify_into(&self, goal: &Formula, subst: &mut Substitution) -> bool {
        subst.unify_formulas(self, goal)
    }

    pub fn unify_term(t1: &Term, t2: &Term, bindings: &mut Bindings) -> bool {
        let mut subst = Substitution::from_bindings(bindings.clone());
        if subst.unify_terms(t1, t2) {
            *bindings = subst.into_bindings();
            true
        } else {
            false
        }
    }
}

fn occurs_check(n: &VarId, t: &Term, bindings: &Bindings) -> bool {
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
/// The shared counter survives across IDDFS depth iterations within a
/// single `prove()` call. This guarantees that
/// Skolem names are unique within one top-level proof attempt.
fn fresh_skolem(counter: &Cell<u32>) -> String {
    let next = counter.get() + 1;
    counter.set(next);
    format!("?w{}", next)
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
    let rename: HashMap<VarId, VarId> = axiom.vars
        .iter()
        .map(|v| (v.clone(), v.derived(&format!("__instance{}", counter))))
        .collect();

    /// Rename variables inside a Term.
    fn rename_term(t: &Term, rename: &HashMap<VarId, VarId>) -> Term {
        match t {
            Term::Var(n, s) =>
                Term::Var(rename.get(n).cloned().unwrap_or_else(|| n.clone()), s.clone()),
            Term::Const(_) => t.clone(),
            Term::Apply(n, args) =>
                Term::Apply(n.clone(), args.iter().map(|a| rename_term(a, rename)).collect()),
        }
    }

    /// Rename variables inside a Formula.
    fn rename_formula(f: &Formula, rename: &HashMap<VarId, VarId>) -> Formula {
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
        vars:       axiom.vars.iter().map(|v| v.derived(&format!("__instance{}", counter))).collect(),
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
    let mut facts = universe.all_facts();
    let mut known: HashSet<Formula> = facts.values().cloned().collect();
    // Build the complete-fact index once. New discoveries are inserted into
    // it as they enter the database instead of re-indexing every old fact on
    // every saturation round.
    let mut known_index = FactIndex::new(&facts);
    let mut delta = facts.clone();
    let mut all_new = Vec::new();
    let mut deduction_counter = 0usize;
    let mut axiom_counter = 0usize;

    for step in 0..max_steps {
        if step > 0 && delta.is_empty() {
            break;
        }

        let delta_index = FactIndex::new(&delta);
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
                        &facts,
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
            universe.add_derived(name.clone(), formula.clone());
            facts.insert(name.clone(), formula.clone());
            known_index.insert(name.clone(), formula.clone());
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
        // Iterate the distinct heads that actually arrived in this delta,
        // rather than scanning every head represented by every rule.
        for head in delta.by_head.keys() {
            if let Some(positions) = self.by_premise_head.get(head) {
                candidates.extend_from_slice(positions);
            }
        }
        // Hash-map key iteration is intentionally unordered; sort and dedupe
        // to preserve deterministic rule exploration.
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
            index.insert(name.clone(), formula.clone());
        }
        index
    }

    fn insert(&mut self, name: String, formula: Formula) {
        let names = self.by_head.entry(formula_head(&formula)).or_default();
        // Facts are inserted in deduction order, but keep this index's
        // ordering invariant explicit for callers that build it from maps.
        match names.binary_search(&name) {
            Ok(_) => {}
            Err(position) => names.insert(position, name),
        }
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
        for names in index.givens_by_head.values_mut() {
            names.sort();
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
// Proof search (IDDFS) — trail-backed continuation search
// ---------------------------------------------------------------------------

/// A continuation is called while the successful branch's substitution is
/// still active. Returning true stops the search; returning false asks the
/// caller to roll back this branch and try the next alternative.
type ProofContinuation<'a> = dyn FnMut(&mut Substitution, ProofStep) -> bool + 'a;

/// Attempt to prove `goal` using axioms from the given `universe`.
pub fn prove(goal: &Formula, universe: &Universe, max_depth: u32) -> Option<ProofStep> {
    let goal = match goal {
        Formula::Eq(left, right) => {
            let simped_left = simplify_term(left, &universe.axioms);
            let simped_right = simplify_term(right, &universe.axioms);
            if simped_left == simped_right {
                let refl_goal = Formula::Eq(simped_left.clone(), simped_right.clone());
                return Some(ProofStep::simple(refl_goal, ProofRule::EqualityReflexivity, vec![]));
            }
            Formula::Eq(simped_left, simped_right)
        }
        Formula::Pred(name, args) => Formula::Pred(
            name.clone(),
            args.iter().map(|a| simplify_term(a, &universe.axioms)).collect(),
        ),
        _ => goal.clone(),
    };

    let facts = universe.all_facts();
    let search_index = ProofSearchIndex::new(&universe.axioms, &facts);

    // Keep the direct fact lookup as a cheap fast path.
    for given_name in search_index.given_candidates(&goal) {
        if let Some(given_formula) = facts.get(given_name) {
            let mut subst = Substitution::new();
            if given_formula.unify_into(&goal, &mut subst) {
                return Some(ProofStep::simple(
                    goal.clone(),
                    ProofRule::Given(given_name.to_string()),
                    vec![],
                ));
            }
        }
    }

    let skolem_counter = Cell::new(0u32);
    let axiom_counter = Cell::new(0usize);
    let operations_budget = Cell::new(500_000usize);

    for depth in 1..=max_depth {
        let mut subst = Substitution::new();
        let mut found = None;

        prove_dfs(
            &goal,
            &universe.axioms,
            &facts,
            &search_index,
            depth,
            &mut subst,
            &[],
            &skolem_counter,
            &axiom_counter,
            &operations_budget,
            &mut |subst, proof| {
                // This is the only full binding-map snapshot in a successful
                // search. All intermediate alternatives share the undo trail.
                found = Some((proof, subst.as_bindings().clone()));
                true
            },
        );

        if let Some((mut proof, final_bindings)) = found {
            proof.apply_bindings(&final_bindings);
            return Some(proof);
        }
        if operations_budget.get() == 0 {
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
    let candidate = prove(goal, universe, max_depth);
    if let Some(proof) = &candidate {
        crate::kernel::check_proof_for_goal(proof, goal, universe)
            .map_err(|error| format!("proof kernel rejected search result: {}", error))?;
    }
    Ok(candidate)
}

/// Search one goal using a shared substitution trail.
///
/// Every candidate owns a checkpoint. Its continuation runs before that
/// checkpoint is rolled back, which lets conjunctions and axiom premises
/// explore their next subgoal using the bindings established by earlier ones.
/// A failed later subgoal therefore backtracks into the earlier candidate
/// without cloning or merging complete binding maps.
fn prove_dfs(
    goal: &Formula,
    axioms: &[Axiom],
    givens: &HashMap<String, Formula>,
    search_index: &ProofSearchIndex,
    depth: u32,
    subst: &mut Substitution,
    path: &[Formula],
    skolem_ctr: &Cell<u32>,
    axiom_ctr: &Cell<usize>,
    operations_budget: &Cell<usize>,
    continuation: &mut ProofContinuation<'_>,
) -> bool {
    if depth == 0 || operations_budget.get() == 0 {
        return false;
    }
    operations_budget.set(operations_budget.get() - 1);

    let current_goal = goal.substitute(subst.as_bindings());

    if let Formula::Eq(left, right) = &current_goal {
        if left == right {
            return continuation(
                subst,
                ProofStep::simple(current_goal, ProofRule::EqualityReflexivity, vec![]),
            );
        }
    }

    // Facts are tried in index order. The index sorts names so the first
    // successful proof is stable across HashMap iteration orders.
    for given_name in search_index.given_candidates(&current_goal) {
        let Some(given_formula) = givens.get(given_name) else { continue; };
        let checkpoint = subst.checkpoint();
        if given_formula.unify_into(&current_goal, subst) {
            let stop = continuation(
                subst,
                ProofStep::simple(
                    current_goal.clone(),
                    ProofRule::Given(given_name.to_string()),
                    vec![],
                ),
            );
            subst.rollback(checkpoint);
            if stop {
                return true;
            }
        }
        // unify_into is transactional on failure; successful attempts are
        // rolled back above, before another fact is considered.
    }

    if path.contains(&current_goal) {
        return false;
    }

    let mut next_path = path.to_vec();
    next_path.push(current_goal.clone());

    match &current_goal {
        Formula::And(left, right) => {
            prove_dfs(
                left, axioms, givens, search_index, depth, subst, &next_path,
                skolem_ctr, axiom_ctr, operations_budget,
                &mut |subst, left_proof| {
                    let right_goal = right.substitute(subst.as_bindings());
                    prove_dfs(
                        &right_goal, axioms, givens, search_index, depth, subst,
                        &next_path, skolem_ctr, axiom_ctr, operations_budget,
                        &mut |subst, right_proof| {
                            continuation(
                                subst,
                                ProofStep::simple(
                                    current_goal.clone(),
                                    ProofRule::ConjunctionIntroduction,
                                    vec![left_proof.clone(), right_proof],
                                ),
                            )
                        },
                    )
                },
            )
        }
        Formula::Or(left, right) => {
            let left_succeeded = prove_dfs(
                left, axioms, givens, search_index, depth, subst, &next_path,
                skolem_ctr, axiom_ctr, operations_budget,
                &mut |subst, proof| {
                    continuation(
                        subst,
                        ProofStep::simple(
                            current_goal.clone(),
                            ProofRule::DisjunctionIntroductionLeft,
                            vec![proof],
                        ),
                    )
                },
            );
            if left_succeeded {
                true
            } else {
                prove_dfs(
                    right, axioms, givens, search_index, depth, subst, &next_path,
                    skolem_ctr, axiom_ctr, operations_budget,
                    &mut |subst, proof| {
                        continuation(
                            subst,
                            ProofStep::simple(
                                current_goal.clone(),
                                ProofRule::DisjunctionIntroductionRight,
                                vec![proof],
                            ),
                        )
                    },
                )
            }
        }
        Formula::Exists { var, sort, body } => {
            let skolem_name = fresh_skolem(skolem_ctr);
            let skolem_term = Term::Var(VarId::from(skolem_name), sort.clone());
            let checkpoint = subst.checkpoint();
            subst.bind(var.clone(), skolem_term.clone());
            let witness_goal = body.substitute(subst.as_bindings());

            let stop = prove_dfs(
                &witness_goal, axioms, givens, search_index, depth - 1, subst,
                &next_path, skolem_ctr, axiom_ctr, operations_budget,
                &mut |subst, sub_proof| {
                    let resolved_witness = skolem_term.substitute(subst.as_bindings());
                    let concrete_goal = witness_goal.substitute(subst.as_bindings());
                    let mut step = ProofStep {
                        goal: current_goal.clone(),
                        rule: ProofRule::ExistentialIntroduction,
                        sub_proofs: vec![sub_proof],
                        witnesses: vec![(var.clone(), resolved_witness)],
                    };
                    step.sub_proofs[0].goal = concrete_goal;
                    continuation(subst, step)
                },
            );
            subst.rollback(checkpoint);
            stop
        }
        _ => {
            for &axiom_index in search_index.axiom_candidates(&current_goal) {
                if operations_budget.get() == 0 {
                    return false;
                }

                let axiom = &axioms[axiom_index];
                axiom_ctr.set(axiom_ctr.get() + 1);
                let fresh_axiom = instantiate_axiom(axiom, axiom_ctr.get());
                let checkpoint = subst.checkpoint();

                if fresh_axiom.conclusion.unify_into(&current_goal, subst) {
                    let stop = prove_axiom_premises(
                        &fresh_axiom.premises,
                        0,
                        axioms,
                        givens,
                        search_index,
                        depth,
                        subst,
                        &next_path,
                        skolem_ctr,
                        axiom_ctr,
                        operations_budget,
                        &current_goal,
                        &fresh_axiom.name,
                        &axiom.vars.iter().cloned().zip(fresh_axiom.vars.iter().cloned()).collect::<Vec<_>>(),
                        Vec::new(),
                        continuation,
                    );
                    subst.rollback(checkpoint);
                    if stop {
                        return true;
                    }
                }
            }
            false
        }
    }
}

/// Prove an axiom's premises left-to-right while retaining the same mutable
/// substitution. A later premise can reject an earlier match, causing that
/// earlier goal's search to resume at its next candidate.
#[allow(clippy::too_many_arguments)]
fn prove_axiom_premises(
    premises: &[Formula],
    position: usize,
    axioms: &[Axiom],
    givens: &HashMap<String, Formula>,
    search_index: &ProofSearchIndex,
    depth: u32,
    subst: &mut Substitution,
    path: &[Formula],
    skolem_ctr: &Cell<u32>,
    axiom_ctr: &Cell<usize>,
    operations_budget: &Cell<usize>,
    root_goal: &Formula,
    axiom_name: &str,
    axiom_vars: &[(VarId, VarId)],
    sub_proofs: Vec<ProofStep>,
    continuation: &mut ProofContinuation<'_>,
) -> bool {
    if position == premises.len() {
        let instantiations = axiom_vars
            .iter()
            .filter_map(|(original, fresh)| {
                subst.get(fresh).map(|term| (original.clone(), subst.resolve(term)))
            })
            .collect();
        return continuation(
            subst,
            ProofStep::simple(
                root_goal.clone(),
                ProofRule::Axiom(axiom_name.to_string(), instantiations),
                sub_proofs,
            ),
        );
    }

    if depth <= 1 || operations_budget.get() == 0 {
        return false;
    }

    let premise_goal = premises[position].substitute(subst.as_bindings());
    prove_dfs(
        &premise_goal,
        axioms,
        givens,
        search_index,
        depth - 1,
        subst,
        path,
        skolem_ctr,
        axiom_ctr,
        operations_budget,
        &mut |subst, proof| {
            let mut next_proofs = sub_proofs.clone();
            next_proofs.push(proof);
            prove_axiom_premises(
                premises,
                position + 1,
                axioms,
                givens,
                search_index,
                depth,
                subst,
                path,
                skolem_ctr,
                axiom_ctr,
                operations_budget,
                root_goal,
                axiom_name,
                axiom_vars,
                next_proofs,
                continuation,
            )
        },
    )
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

        universe.add_given("p_a".into(), pred("P", a.clone()));
        universe.add_given("s_a".into(), pred("S", a.clone()));

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


#[cfg(test)]
mod fact_provenance_tests {
    use super::*;

    fn pred(name: &str, term: &str) -> Formula {
        Formula::Pred(name.into(), vec![Term::Const(term.into())])
    }

    #[test]
    fn explicit_givens_are_stored_only_as_assumptions() {
        let mut universe = Universe::new();
        let assumption = pred("P", "a");

        universe.add_given("P_a".into(), assumption.clone());

        assert_eq!(universe.assumptions.get("P_a"), Some(&assumption));
        assert!(universe.derived.is_empty());
        assert_eq!(universe.all_facts().get("P_a"), Some(&assumption));
    }

    #[test]
    fn forward_deduction_stores_results_separately_from_assumptions() {
        let mut universe = Universe::new();
        let assumption = pred("P", "a");
        let conclusion = pred("Q", "a");

        universe.add_given("P_a".into(), assumption.clone());
        universe.add_axiom(Axiom {
            name: "P_implies_Q".into(),
            vars: vec![],
            premises: vec![assumption.clone()],
            conclusion: conclusion.clone(),
        });

        let discoveries = forward_deduce(&mut universe, 2);

        assert!(discoveries.iter().any(|(_, formula)| formula == &conclusion));
        assert_eq!(universe.assumptions.len(), 1);
        assert_eq!(universe.assumptions.get("P_a"), Some(&assumption));
        assert!(universe.derived.values().any(|formula| formula == &conclusion));
        assert_eq!(universe.all_facts().len(), 2);
    }
}

#[cfg(test)]
mod rollback_substitution_tests {
    use super::*;

    fn var(name: &str) -> Term {
        Term::Var(name.into(), Sort::object())
    }

    fn c(name: &str) -> Term { Term::Const(name.into()) }

    #[test]
    fn failed_formula_unification_rolls_back_partial_bindings() {
        let pattern = Formula::Pred("Pair".into(), vec![var("x"), c("left")]);
        let target = Formula::Pred("Pair".into(), vec![c("alice"), c("right")]);
        let mut subst = Substitution::new();

        assert!(!pattern.unify_into(&target, &mut subst));
        assert!(subst.get("x").is_none());
        assert!(subst.as_bindings().is_empty());
    }

    #[test]
    fn checkpoint_restores_overwritten_bindings_and_new_bindings() {
        let mut subst = Substitution::new();
        subst.bind("x".into(), c("first"));
        let checkpoint = subst.checkpoint();

        subst.bind("x".into(), c("second"));
        subst.bind("y".into(), c("third"));
        subst.rollback(checkpoint);

        assert_eq!(subst.get("x"), Some(&c("first")));
        assert!(subst.get("y").is_none());
    }

    #[test]
    fn successful_unification_can_be_rolled_back_for_next_branch() {
        let mut subst = Substitution::new();
        let checkpoint = subst.checkpoint();
        assert!(subst.unify_terms(&var("x"), &c("alice")));
        assert_eq!(subst.resolve(&var("x")), c("alice"));

        subst.rollback(checkpoint);
        assert_eq!(subst.resolve(&var("x")), var("x"));
    }

    #[test]
    fn occurs_check_failure_does_not_change_existing_environment() {
        let mut subst = Substitution::new();
        subst.bind("known".into(), c("alice"));
        let before = subst.as_bindings().clone();

        assert!(!subst.unify_terms(
            &var("x"),
            &Term::Apply("f".into(), vec![var("x")]),
        ));
        assert_eq!(subst.as_bindings(), &before);
    }
}



#[cfg(test)]
mod trail_backtracking_tests {
    use super::*;

    fn var(name: &str) -> Term {
        Term::Var(name.into(), Sort::object())
    }

    fn constant(name: &str) -> Term {
        Term::Const(name.into())
    }

    fn pred(name: &str, term: Term) -> Formula {
        Formula::Pred(name.into(), vec![term])
    }

    #[test]
    fn conjunction_backtracks_into_earlier_goal_without_leaking_bindings() {
        let mut universe = Universe::new();
        let a = constant("a");
        let b = constant("b");
        let x = var("x");

        // P(a) is deliberately tried before P(b). It binds x to a, but the
        // second conjunct cannot be proved with that binding. Search must
        // revisit the first conjunct and try P(b).
        universe.add_given("P_a".into(), pred("P", a));
        universe.add_given("P_b".into(), pred("P", b.clone()));
        universe.add_given("T_b".into(), pred("T", b.clone()));
        universe.add_axiom(Axiom {
            name: "P_implies_R".into(),
            vars: vec!["x".into()],
            premises: vec![pred("P", x.clone())],
            conclusion: pred("R", x),
        });

        let goal = Formula::And(
            Box::new(pred("R", var("x"))),
            Box::new(pred("T", var("x"))),
        );
        let proof = prove(&goal, &universe, 3).expect("the conjunction should be provable");

        let expected = Formula::And(
            Box::new(pred("R", constant("b"))),
            Box::new(pred("T", constant("b"))),
        );
        assert_eq!(proof.goal, expected);
        assert_eq!(proof.sub_proofs.len(), 2);
    }

    #[test]
    fn axiom_premises_share_bindings_across_the_entire_rule_application() {
        let mut universe = Universe::new();
        let a = constant("a");
        let b = constant("b");
        let x = var("x");

        universe.add_given("P_a".into(), pred("P", a));
        universe.add_given("P_b".into(), pred("P", b.clone()));
        universe.add_given("S_b".into(), pred("S", b.clone()));
        universe.add_axiom(Axiom {
            name: "P_and_S_implies_R".into(),
            vars: vec!["x".into()],
            premises: vec![pred("P", x.clone()), pred("S", x.clone())],
            conclusion: pred("R", x),
        });

        let proof = prove(&pred("R", var("result")), &universe, 3)
            .expect("the rule should backtrack from a to b");

        assert_eq!(proof.goal, pred("R", constant("b")));
        assert_eq!(proof.sub_proofs.len(), 2);
    }
}


#[cfg(test)]
mod trail_structural_search_tests {
    use super::*;

    fn var(name: &str) -> Term {
        Term::Var(name.into(), Sort::object())
    }

    fn constant(name: &str) -> Term {
        Term::Const(name.into())
    }

    fn pred(name: &str, term: Term) -> Formula {
        Formula::Pred(name.into(), vec![term])
    }

    #[test]
    fn existential_instantiation_preserves_the_resolved_witness() {
        let mut universe = Universe::new();
        universe.add_given("P_a".into(), pred("P", constant("a")));

        let goal = Formula::Exists {
            var: "x".into(),
            sort: Sort::object(),
            body: Box::new(pred("P", var("x"))),
        };
        let proof = prove(&goal, &universe, 2).expect("the existential should be provable");

        assert_eq!(proof.witnesses, vec![("x".into(), constant("a"))]);
        assert_eq!(proof.sub_proofs[0].goal, pred("P", constant("a")));
    }

    #[test]
    fn substitution_renames_a_binder_to_prevent_variable_capture() {
        let formula = Formula::Exists {
            var: "y".into(),
            sort: Sort::object(),
            body: Box::new(Formula::Pred(
                "R".into(),
                vec![var("x"), var("y")],
            )),
        };
        let bindings = Bindings::from([("x".into(), var("y"))]);

        let result = formula.substitute(&bindings);
        let Formula::Exists { var: binder, body, .. } = result else {
            panic!("substitution must preserve the existential");
        };
        assert_ne!(binder, "y");
        assert_eq!(
            *body,
            Formula::Pred("R".into(), vec![var("y"), var(&binder)])
        );
    }

    #[test]
    fn substitution_respects_a_shadowing_quantifier() {
        let formula = Formula::Exists {
            var: "x".into(),
            sort: Sort::object(),
            body: Box::new(pred("P", var("x"))),
        };
        let bindings = Bindings::from([("x".into(), constant("a"))]);

        assert_eq!(formula.substitute(&bindings), formula);
    }

    #[test]
    fn quantified_formula_unification_is_alpha_equivalent() {
        let left = Formula::Exists {
            var: "x".into(),
            sort: Sort::object(),
            body: Box::new(pred("P", var("x"))),
        };
        let right = Formula::Exists {
            var: "y".into(),
            sort: Sort::object(),
            body: Box::new(pred("P", var("y"))),
        };

        assert!(left.unify(&right).is_some());
        assert!(left.unify(&Formula::Exists {
            var: "y".into(),
            sort: Sort::object(),
            body: Box::new(pred("Q", var("y"))),
        }).is_none());
    }

    #[test]
    fn disjunction_search_tries_the_right_branch_after_left_fails() {
        let mut universe = Universe::new();
        universe.add_given("Q_a".into(), pred("Q", constant("a")));

        let goal = Formula::Or(
            Box::new(pred("P", constant("a"))),
            Box::new(pred("Q", constant("a"))),
        );
        let proof = prove(&goal, &universe, 1).expect("the right disjunct should be provable");

        assert_eq!(proof.rule, ProofRule::DisjunctionIntroductionRight);
        assert_eq!(proof.sub_proofs[0].goal, pred("Q", constant("a")));
    }
}


#[cfg(test)]
mod incremental_forward_index_tests {
    use super::*;

    #[test]
    fn fact_index_accepts_new_facts_without_rebuilding() {
        let p = Formula::Pred("P".into(), vec![Term::Const("a".into())]);
        let q = Formula::Pred("Q".into(), vec![Term::Const("a".into())]);
        let mut index = FactIndex::new(&HashMap::new());

        assert!(index.candidates(&p).is_empty());
        index.insert("p_second".into(), p.clone());
        index.insert("p_first".into(), p.clone());
        index.insert("p_first".into(), p.clone());
        index.insert("q".into(), q.clone());

        assert_eq!(
            index.candidates(&p),
            &["p_first".to_string(), "p_second".to_string()]
        );
        assert_eq!(index.candidates(&q), &["q".to_string()]);
    }

    #[test]
    fn delta_heads_select_only_relevant_forward_rules_deterministically() {
        let p = Formula::Pred("P".into(), vec![Term::Var("x".into(), Sort::object())]);
        let q = Formula::Pred("Q".into(), vec![Term::Var("x".into(), Sort::object())]);
        let r = Formula::Pred("R".into(), vec![Term::Var("x".into(), Sort::object())]);
        let axioms = vec![
            Axiom { name: "P_rule".into(), vars: vec![], premises: vec![p.clone()], conclusion: p.clone() },
            Axiom { name: "Q_rule".into(), vars: vec![], premises: vec![q.clone()], conclusion: q.clone() },
            Axiom { name: "R_rule".into(), vars: vec![], premises: vec![r.clone()], conclusion: r.clone() },
        ];
        let rules = ForwardAxiomIndex::new(&axioms);
        let mut delta = FactIndex::new(&HashMap::new());
        delta.insert("q".into(), q);
        delta.insert("p".into(), p);

        assert_eq!(rules.candidates(&delta), vec![0, 1]);
        assert_eq!(rules.candidates(&FactIndex::new(&HashMap::new())), Vec::<usize>::new());
    }
}
