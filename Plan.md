##### **ChatGPT said:** 

# **Axia — Architecture, Performance & Long-Term Vision** 

Repository inspected Rust Formal logic 

Repository: github.com/pook27/axia 

I've looked through the current implementation, particularly: 

- `src/ast.rs` — logical representation. 

- `src/parser.rs` — lexer, parser, declarations and formula syntax. 

- `src/engine.rs` — unification, rewriting, forward deduction and backward proof search. 

- `src/main.rs` — REPL, universe management, module loading and proof presentation. 

- `Cargo.toml` — current dependencies. 

The repository describes Axia as a mathematical logic parser and prover. Its current architecture already contains several important pieces, so I wouldn't recommend throwing it away. 

**My recommendation is to evolve Axia into a small, extensible proof assistant with a trusted logical kernel, an efficient reasoning engine, and a modular theory system.** 

The most important conceptual change is this: 

Axia should stop being primarily a program that searches for ways to prove formulas, and become a system that constructs, checks, and extends formal mathematical knowledge. 

That is the distinction that will take it towards Lean. 

# **1. Where Axia currently stands** 

First, I want to distinguish what you already have from what is still missing. 

## **1.1 Existing architecture** 

## **Current Axia architecture** 



<!-- Start of picture text -->
Input language<br>Mathematical declarations, formulas, axioms and commands<br>Lexer and Parser<br>Recursive descent, mathematical precedence, declarations<br>AST<br>Terms, formulas, sorts, statements<br>Universe<br>Axioms, types, predicates, constants and givens<br>Backward proving Forward deduction<br>IDDFS, unification, proof trees Axiom application, matching, saturation<br>Proof formatter<br>Human-readable proof explanations<br><!-- End of picture text -->

This is a reasonable starting point. 

You already have: 

|**Feature**|**Current state**|
|---|---|
|Typed terms|Partial|
|First-order predicates|Yes|
|Equality|Yes|
|Conjunction|Yes|
|Disjunction|Yes|
|Implication|Yes|
|Negation|Yes|
|Existential quantification|Yes|
|Universal quantification|Primarily through axiom variables|
|Unification|Yes|
|Occurs check|Yes|
|Equational rewriting|Yes|
|Forward chaining|Yes|
|Backward chaining|Yes|
|Proof trees|Yes|
|Named universes|Basic implementation|
|Module loading|Basic implementation|
|Verified proof kernel|Initial proof-tree checker integrated; full kernel incomplete|
|Theorem declarations<br>Universe dependency graph|Not yet a distinct proof-checked concept<br>Not yet|



The interesting thing is that the current engine is already approaching a miniature logic programming system. 

However, it isn't yet a proper proof assistant. 

## **1.2 The problems I would address first** 

There are several architectural issues worth fixing before introducing more sophisticated reasoning. 

### **A. The type system isn't sufficiently enforced.** 

In `engine.rs` , `Term::sort()` returns `Object` for constants and function applications. Meanwhile, `sorts_compatible()` treats `Object` as a wildcard. 

This means that although you maintain a constant-to-sort table, the engine doesn't consistently preserve and enforce that information during unification. 

I would make type correctness a fundamental invariant, not a convenience of the parser. 

### **B. The rewriting system isn't guaranteed to terminate.** 

`simplify_term()` recursively applies equational rules. It ignores identity rewrites, but that doesn't prevent a pair of rules from cycling: 

|`A = B`<br>`B = A`<br>Plain text|
|---|



You need a termination policy, rewrite ordering, cycle detection and resource limits. 

### **C. Proof search performs considerable redundant work.** 

Your current prover uses iterative deepening DFS, with a 500,000-node budget. 

At each search node, it can: 

Example 

Iterate through the available axioms. 

Attempt unification. Iterate through all givens. 

Allocate and clone binding maps. Construct additional proof trees. 

Copy the current path for recursive branches. 

This is manageable for small theories, but becomes increasingly expensive as the number of axioms and available facts increases. 

### **D. Forward deduction doesn't scale particularly well.** 

`forward_deduce()` repeatedly scans axioms and attempts to match their premises against the entire collection of givens. 

This can become combinatorial when an axiom has multiple premises and the universe contains many facts. 

### **E. The AST needs stronger foundations.** 

Variables are represented using strings, and quantifier binding is handled through variable names. 

For a larger formal system, I would introduce unique variable identities or de Bruijn indices. This makes substitution, shadowing, alpha-equivalence and capture avoidance much more reliable. 

### **F. Axioms and theorems aren't sufficiently distinguished.** 

Currently, an axiom is essentially a collection of premises and a conclusion. 

There is no fundamental distinction between: 

Something the user assumes. Something the system derives. Something the system has formally verified. 

This is probably the most important conceptual change. 

# **2. The new vision: Axia as a mathematical Universe** 

This is where I think your idea becomes particularly interesting. 

I would make `Universe` the central organizing concept of the entire language. 

However, I would give it a much more precise meaning. 

A Universe is a **self-contained mathematical context** containing a set of definitions, types, axioms, theorems and dependencies. 

It defines the logical world in which statements are interpreted. 

For example: 

## **Example mathematical universe** 

### **Universe: NaturalNumbers** 

Plain text `universe NaturalNumbers type Nat constant Zero : Nat function Succ : Nat -> Nat axiom Succ_Never_Zero: forall n : Nat, Succ(n) != Zero axiom Succ_Injective: forall a b : Nat, Succ(a) = Succ(b) -> a = b` 

```
theorem Zero_Is_Zero:
    Zero = Zero
```

Illustrative syntax, not currently supported Axia syntax. The example uses axioms and a trivial theorem to demonstrate the intended distinction. 

The universe defines what exists, what is assumed to be true, and what can be derived. 

Now imagine another universe: 

### **Universe: NaturalNumberArithmetic** 

Plain text 

```
universe NaturalNumberArithmetic
import NaturalNumbers
function Add : Nat -> Nat -> Nat
axiom Add_Zero:
    forall n : Nat,
    Add(n, Zero) = n
axiom Add_Succ:
    forall n m : Nat,
    Add(n, Succ(m)) = Succ(Add(n, m))
theorem Zero_Add_Zero:
    Add(Zero, Zero) = Zero
```

Illustrative theory extension. 

This universe extends the previous one. 

It doesn't need to redefine `Nat` , `Zero` , or `Succ` . 

It inherits the mathematical assumptions and definitions of the imported universe. 

Then: 

### **Universe: ElementaryNumberTheory** 

Plain text 

```
universe ElementaryNumberTheory
import NaturalNumberArithmetic
-- Further definitions and theorems
theorem ...
```

You now have a hierarchy of mathematical knowledge. 

But I would go further. 

## **2.1 Universes should form a dependency graph** 

I wouldn't restrict universes to a simple parent-child tree. 

A mathematical theory can depend on multiple independent theories. 

For example: 

**Mathematical dependency graph** 



<!-- Start of picture text -->
Logic<br>Base logical rules and foundations<br>NaturalNumbers SetTheory<br>NumberTheory<br>Imports NaturalNumbers and SetTheory<br>AdvancedMathematics<br>Combines multiple mathematical theories<br><!-- End of picture text -->

This gives you something powerful: 

A file doesn't merely import other files. 

It declares the mathematical environment under which its contents are valid. 

For example: 



<!-- Start of picture text -->
Plain text<br>module PrimeNumbers<br>requires:<br>    NaturalNumbers<br>    NaturalNumberArithmetic<br>    BasicLogic<br>theorem ...<br><!-- End of picture text -->

The compiler resolves the dependencies, constructs the effective logical context and checks every declaration against it. 

**An important distinction** 

I would distinguish two concepts: 

**Logical universe:** A mathematical theory or context containing assumptions, definitions and results. **Type universe:** A hierarchy of types, if Axia eventually introduces dependent type theory. 

They shouldn't be the same object. 

Lean has a sophisticated type-universe hierarchy. You don't need to implement that immediately to achieve your goal. 

# **3. The most important architectural change: A trusted kernel** 

This is what I would prioritize above almost everything else. 

Currently, the engine searches for proofs and produces proof trees. 

But a search algorithm is not, by itself, a guarantee that its result is logically valid. 

I would separate Axia into two components: 

**1.** The reasoning engine, which tries to discover proofs. 

**2.** The kernel, which independently verifies proofs. 

## **Proposed proof architecture** 

**User's theorem** A mathematical proposition to establish 



<!-- Start of picture text -->
Elaborator<br><!-- End of picture text -->

Resolves names, types and notation 

### **Reasoning engine** 

Searches, rewrites, applies tactics and constructs candidate proofs 

**Proof object** 

A structured representation of the derivation 

Trusted component 

### **Kernel / Proof Checker** 

Independently verifies the proof against the logical rules and context 



<!-- Start of picture text -->
Accepted Rejected<br>Theorem is verified Invalid or incomplete proof<br><!-- End of picture text -->

The critical property: 

**The kernel must not trust the reasoning engine.** 

Even if your search algorithm has bugs, it should not be able to convince the kernel to accept an invalid proof. 

This is the same fundamental architectural philosophy that makes proof assistants such as Lean reliable. 

The kernel should be small, deterministic and extensively tested. 

## **3.1 Introduce proof objects** 

Instead of only storing a human-readable proof tree: 

Rust `pub struct ProofStep { pub goal: Formula, pub rule_name: String, pub sub_proofs: Vec<ProofStep>, }` 

Introduce a formal proof representation. 

For example, conceptually: 

Rust `enum Proof { Axiom(AxiomId), AndIntro( Box<Proof>, Box<Proof>, ), AndElimLeft(Box<Proof>), AndElimRight(Box<Proof>), ImpIntro(Box<Proof>), ImpElim( Box<Proof>, Box<Proof>, ), EqRefl(TermId),` 

```
EqSubst {
proof: Box<Proof>,
equality: Box<Proof>,
    },
ForallIntro(Box<Proof>),
ForallElim {
proof: Box<Proof>,
term: TermId,
    },
ExistsIntro {
```

This is illustrative rather than a complete set of constructors. 

The important idea is that every proof step has an explicit logical meaning. 

The kernel checks whether the proof object actually establishes the requested proposition. 

This also gives you a natural separation between: 

How a proof was discovered. What the proof actually consists of. Whether the proof is valid. 

That separation will make future optimizations considerably safer. 

# **4. Rebuild the logical foundation** 

Before making Axia significantly smarter, I would make its underlying logic more expressive and mathematically rigorous. 

The current AST is a good prototype, but it needs to evolve. 

## **4.1 A more complete logical language** 

I would target the following logical constructs: 

|**Construct**|**Meaning**|**Priority**|
|---|---|---|
|`True`|Truth|High|
|`False`|Contradiction|High|
|`And`|Conjunction|Existing|
|`Or`|Disjunction|Existing|
|`Not`|Negation|Existing|
|`Implies`|Implication|Existing|
|`Iff`|Logical equivalence|High|
|`Forall`|Universal quantification|Critical|
|`Exists`|Existential quantification|Existing|
|`Eq`|Equality|Existing|
|`Neq`|Inequality|High|



The biggest missing piece is proper universal quantification. 

Currently, universally quantified variables in axioms are represented through `Axiom.vars` , rather than being represented as a first-class formula. 

That works for basic theorem proving, but it becomes limiting when you want to reason about quantified statements themselves. 

For example, you should eventually be able to prove: 

∀ _x_ , _P_ ( _x_ ) → _Q_ ( _x_ ) 

and then use that theorem elsewhere as a quantified proposition. 

I would make `Forall` and `Exists` first-class AST constructs. 

## **4.2 Replace string-based variable identity** 

Currently: 

Rust `Term::Var(String, Sort)` 

I would eventually move towards: 



<!-- Start of picture text -->
Rust<br>struct VarId(u32);<br>struct Variable {<br>id: VarId,<br>name: String,<br>sort: TypeId,<br>}<br><!-- End of picture text -->

The name becomes presentation metadata. 

The identity is the actual identifier used by the logical engine. 

This prevents accidental collisions between variables with the same textual name. 

It also makes substitution and quantifier handling considerably easier. 

For the eventual kernel, I would seriously consider de Bruijn indices for bound variables. 

## **4.3 Make the type system real** 

I would distinguish: 

Types. Terms. Propositions. Functions. Predicates. Proofs. 

For example: 

_f_ : _A_ → _B P_ : _A_ → _Prop x_ : _A P_ ( _x_ ) : _Prop_ 

This is more than syntactic annotation. 

The type checker must establish that every function receives arguments of the correct types and every proposition is well-formed. 

A useful intermediate goal would be a simply typed first-order logic system. 

I would not immediately implement full dependent type theory. That would multiply the complexity considerably. 

Instead, build a strong typed first-order foundation, then introduce more expressive types later. 

# **5. Making Axia substantially faster** 

I would approach performance systematically rather than immediately introducing multithreading or complicated optimizations. 

There are several obvious opportunities in the existing implementation. 

## **5.1 Replace repeated linear searches with indexing** 

Currently, when proving a goal, Axia iterates through the available axioms. 

Imagine a universe containing 10,000 axioms. 

You want to prove: 

Plain text `Prime(17)` 

There is little reason to attempt unification against axioms whose conclusions have completely different predicate symbols. 

### Introduce an axiom index: 

#### Rust 

```
struct AxiomIndex {
predicates: HashMap<PredicateId, Vec<AxiomId>>,
equalities: Vec<AxiomId>,
other: Vec<AxiomId>,
}
```

When searching for `Prime(17)` , retrieve only relevant candidates. 

You can eventually make this more sophisticated using argument patterns and discrimination trees. 

Apply the same principle to givens. 

Instead of: 

#### Rust 

```
for given in givens.values() {
// Try unification
}
```

Use an index: 

Plain text `Prime(2) Prime(3) Prime(5) Prime(7) Even(2) Even(4) Even(6)` 

A query for `Prime(x)` should immediately retrieve the relevant facts. 

High priority This is probably one of the easiest significant performance improvements. 

## **5.2 Replace cloned HashMaps with efficient substitutions** 

One of the expensive operations in the current engine is copying binding maps throughout recursive proof search. 

You repeatedly create new maps, merge them and clone them. 

I would introduce a substitution engine based on: 

- A compact variable representation. Union-find for variable equivalence. 

- An occurs check. 

- A rollback mechanism for exploring alternative search branches. 

Conceptually: 



<!-- Start of picture text -->
Rust<br>struct Substitution {<br>parent: Vec<VarId>,<br>bindings: Vec<Option<TermId>>,<br>trail: Vec<UndoEntry>,<br>}<br><!-- End of picture text -->

When the prover explores a branch: 

**1.** Save the current trail position. 

**2.** Apply substitutions. 

**3.** Explore the branch. 

**4.** If unsuccessful, roll back to the saved position. 

This avoids copying the entire substitution environment for every branch. 

Be careful: ordinary union-find with path compression isn't automatically compatible with rollback. Use a rollback-aware implementation. 

## **5.3 Replace naive forward chaining with semi-naive evaluation** 

This is particularly important. 

Your current forward deduction algorithm repeatedly examines all axioms against all known facts. 

Instead, implement a worklist-based system. 

The idea: 

**Only reconsider deductions that could be affected by newly discovered facts.** 

For example: 



<!-- Start of picture text -->
Plain text<br>Given:<br>    Parent(A, B)<br>    Parent(B, C)<br>Rule:<br>    Parent(x, y) AND Parent(y, z)<br>        -> Grandparent(x, z)<br><!-- End of picture text -->

When `Parent(B, C)` is introduced, the engine doesn't need to reconsider every previously established fact and every possible rule combination. 

It only needs to evaluate relevant rule instances involving the newly introduced fact. 

This is closely related to semi-naive evaluation in Datalog engines. 

The architecture could look like: 

Rust 



```
struct FactDatabase {
facts: Vec<Fact>,
by_predicate: HashMap<PredicateId, Vec<FactId>>,
pending: Vec<FactId>,
}
```

Then: 

Plain text `while pending is not empty: take newly discovered facts find rules affected by those facts evaluate only new combinations insert genuinely new conclusions` 

This is a much better foundation for large mathematical theories. 

## **5.4 Introduce memoization and tabling** 

Another issue with ordinary DFS is that it can repeatedly solve the same subproblem. 

Suppose two different proof paths both require: 

Plain text `Even(100)` 

There is no reason to independently explore the same search space twice if the logical context and relevant substitutions are equivalent. Introduce a proof-search cache. 

Conceptually: 

Rust 

```
struct ProofCache {
completed: HashMap<GoalKey, ProofResult>,
}
```

A more sophisticated implementation would use tabling: 

- Record goals currently being evaluated. 

- Record discovered answers. 

- Reuse those answers when another branch encounters the same goal. 

- Detect recursive dependencies and avoid endless repeated exploration. 

This is particularly useful for recursive mathematical definitions. 

## **5.5 Use arenas and interned expressions** 

Your current AST recursively owns its children through `Vec` and `Box` . 

That's convenient, but creates substantial allocation and cloning overhead as expressions become large. 

I would eventually move towards an arena-based representation: 

Rust 

```
struct TermArena {
terms: Vec<TermNode>,
}
struct FormulaArena {
formulas: Vec<FormulaNode>,
}
```

Expressions are referenced by compact IDs. 

For example: 

Rust `struct TermNode { kind: TermKind, } enum TermKind { Variable(VarId), Constant(ConstantId), Application(FunctionId, Vec<TermId>), }` 

You can additionally introduce hash-consing: 

If two structurally identical expressions are created, they can share the same representation. 

This gives you: 

Faster equality checks. Reduced memory consumption. Less cloning. Better cache performance. Easier proof DAG construction. 

I wouldn't do this before establishing benchmarks, though. 

## **5.6 Make proof trees directed acyclic graphs** 

A proof tree can contain enormous amounts of repeated information. 

### Consider: 

Plain text `Theorem A /         \ Lemma B      Lemma C \         / Lemma D` 

If both branches depend on the same proof of `Lemma D` , storing the entire proof twice is wasteful. 

Use proof IDs and shared nodes. 

Rust `struct ProofArena { nodes: Vec<ProofNode>, } struct ProofNode { proposition: FormulaId, rule: RuleId, premises: Vec<ProofId>, }` 

Now the proof structure is a DAG rather than necessarily a tree. 

The formatter can still expand it into a readable tree, while the kernel checks the shared proof object. 

# **6. Making Axia smarter: Beyond brute-force theorem proving** 

I think this is where Axia can become genuinely interesting. 

A theorem prover shouldn't just try every axiom until something works. 

It should understand the structure of the problem and select appropriate reasoning strategies. 

I would build this incrementally. 

## **6.1 A tactic system** 

Introduce a language for reasoning strategies. 

For example: 

Plain text `theorem Add_Zero: forall n : Nat, Add(n, Zero) = n proof: induction n case Zero: simplify case Succ(n): rewrite Add_Succ rewrite induction_hypothesis qed` 

The important thing is that tactics don't establish truth by themselves. 

They construct proof objects that the kernel checks. 

I would start with a small collection: 

|**Tactic**|**Purpose**|
|---|---|
|`exact`|Use an existing theorem or hypothesis|
|`apply`|Apply an implication or theorem|
|`intro`|Introduce a quantified variable or implication hypothesis|
|`assumption`|Search available hypotheses|
|`constructor`|Construct conjunctions and other compound goals|
|`cases`|Split logical alternatives|
|`rewrite`|Apply a proven equality|
|`simp`|Simplify expressions using approved rewrite rules|
|`induction`|Perform structural induction|
|`decide`|Solve supported decidable propositions|
|`auto`|Try a collection of bounded tactics|



Eventually, you could support tactic composition: 



#### Plain text 

```
proof:
```

```
    intro
    apply Some_Theorem
    simp
    exact Some_Hypothesis
```

## **6.2 Implement mathematical induction** 

This deserves special attention. 

Induction is essential for mathematical reasoning. 

For natural numbers: 

_P_ (0) 

and 

∀ _n_ , _P_ ( _n_ ) → _P_ ( _S_ ( _n_ )) 

give: 

∀ _n_ , _P_ ( _n_ ) 

But don't implement induction as an ordinary search heuristic. 

It should be an explicit logical principle in the foundation of the natural numbers. 

I would introduce inductive types eventually: 

Plain text `inductive Nat: Zero Succ(Nat)` 

Then define induction as a legitimate eliminator for that type. 

Later, the same machinery can support: 

Lists. Binary trees. Finite sets. Algebraic structures. Recursive mathematical objects. 

This is one of the most important steps towards Lean-like expressiveness. 

## **6.3 Add a proper simplifier** 

Your existing `simp` mechanism is a useful prototype. 

But I would evolve it into a dedicated simplification engine. 

It should support: 

**1.** Registered rewrite theorems. **2.** Pattern matching. 

**3.** Recursive normalization. 

**4.** Rewrite priorities. 

**5.** Termination protection. 

**6.** Memoization. 

**7.** Conditional rewriting when its conditions are proved. 

### **8.** Normalization of propositions, not just terms. 

For example: 

Plain text `theorem Add_Zero: forall x : Nat, Add(x, Zero) = x theorem Mul_Zero: forall x : Nat, Mul(x, Zero) = Zero` 

Once proven, these can be registered: 

Plain text `attribute [simp] Add_Zero attribute [simp] Mul_Zero` 

### Then: 

Plain text `simp: Add(Mul(x, Zero), Zero) result: x` 

The crucial difference is that rewrite rules should be backed by verified theorems, rather than automatically trusting arbitrary equations as simplification rules. 

## **6.4 Introduce reasoning strategies** 

Eventually, Axia should have a strategy selector. 

### For example: 

Plain text `prove SomeTheorem` 

The engine analyzes the goal. 

|**Goal structure**|**Potential strategy**|
|---|---|
|Equality|Simplification, rewriting, congruence|
|Implication|Introduce hypothesis, backward chaining|
|Conjunction|Prove both components|
|Disjunction|Prove either component|
|Universal quantification|Introduce arbitrary variable|
|Existential quantification|Construct a witness|
|Inductive proposition|Consider induction|
|Arithmetic proposition|Arithmetic decision procedure|
|Recursive predicate|Tabling and structural reasoning|



This is how I would make Axia smarter without turning it into an unpredictable collection of heuristics. 

The strategy selector proposes proof methods. The kernel remains the authority. 

# **7. The file system: Mathematical modules and universe dependencies** 

Now let's connect the vision back to the actual `.axia` files. 

I think Axia should eventually have a module system that is much closer to a mathematical library than a traditional programming-language import system. 

## **7.1 A proposed project structure** 

I would aim for something like: 



<!-- Start of picture text -->
Plain text<br>axia/<br>│<br>├── axia.toml<br>│<br>├── foundations/<br>│   ├── Logic.axia<br>│   ├── Equality.axia<br>│   └── Induction.axia<br>│<br>├── mathematics/<br>│   │<br>│   ├── NaturalNumbers/<br>│   │   ├── Universe.axia<br>│   │   ├── Arithmetic.axia<br>│   │   ├── Ordering.axia<br>│   │   └── Primes.axia<br>│   │<br>│   ├── Sets/<br>│   │   ├── Universe.axia<br>│   │   ├── Operations.axia<br>│   │   └── Relations.axia<br>│   │<br>│   ├── Algebra/<br>│   │   ├── Groups.axia<br>│   │   ├── Rings.axia<br>│   │   └── Fields.axia<br>│   │<br>│   └── Geometry/<br>│       ├── Points.axia<br>│       ├── Lines.axia<br>│ ├<br><!-- End of picture text -->

The important part is that a mathematical concept is not necessarily tied to a single file. 

A universe can contain multiple modules, and a module can depend on multiple universes. 

## **7.2 Make dependencies explicit** 

A module should declare its requirements. 

For example: 

Plain text `module EuclideanGeometry requires: Logic Equality RealNumbers BasicGeometry` 

The dependency resolver should: 

**1.** Find the requested modules. 

**2.** Resolve their dependencies recursively. 

**3.** Detect circular dependencies. 

**4.** Build a dependency graph. 

**5.** Check version and compatibility requirements. 

**6.** Construct the combined logical environment. 

**7.** Compile and check the current module. 

Circular dependencies should be rejected rather than resolved through arbitrary import order. 

## **7.3 Separate axioms, definitions and theorems** 

I would make this distinction explicit in the language. 

Plain text `axiom ParallelPostulate: ... definition Distance: ... theorem PythagoreanTheorem: ...` 

These declarations have very different meanings. 

|**Declaration**|**Meaning**|**Trust**|
|---|---|---|
|`axiom`|Accepted assumption|Trusted input|
|`definition`|Introduces a mathematical definition|Kernel-checked|
|`theorem`|Must have a valid proof|Kernel-checked|
|`lemma`|Supporting theorem|Kernel-checked|
|`example`|Demonstration proof|Kernel-checked|



A theorem should never silently become an axiom just because the prover cannot establish it. 

That would undermine the entire system. 

## **7.4 Universe consistency and trust tracking** 

There is another important consideration. 

If a universe contains contradictory axioms, classical logic can derive arbitrary propositions from them. 

Therefore, Axia should track the provenance of every assumption. 

For example: 



<!-- Start of picture text -->
Plain text<br>theorem SomeResult<br>depends on:<br>    Axiom_A<br>    Axiom_B<br>    Imported_Theory_C<br>status:<br>    kernel verified<br><!-- End of picture text -->

This doesn't prove that the assumptions are mathematically true. 

It proves that the conclusion follows from those assumptions under the selected logical rules. 

I would also introduce: 

Axiom inventories. 

Dependency inspection. Imported-theory fingerprints. Versioned theory snapshots. Explicit trust reports. 

That would make it possible to answer: 

_"Exactly what assumptions does this theorem depend on?"_ 

That is a genuinely useful feature for a formal mathematics environment. 

## **7.5 Cache compiled universes** 

This is another major performance opportunity. 

Suppose `AdvancedGeometry` imports: 

Plain text `Logic RealNumbers BasicGeometry` 

You shouldn't have to parse, elaborate and reconstruct those theories every time you open the project. 

Instead, serialize a compiled representation containing: 

- Resolved symbols. Type information. Axiom declarations. Definitions. Verified theorem references. Dependency fingerprints. 

Use content hashes to identify unchanged modules. 

If a dependency changes, invalidate only the affected modules. 

This gives Axia something resembling incremental compilation. 

# **8. A proposed internal architecture** 

I would gradually reorganize the Rust code around separate responsibilities. 

Something along these lines: 

Plain text `src/ │ ├── syntax/ │   ├── lexer.rs │   ├── parser.rs │   ├── ast.rs │   └── diagnostics.rs │ ├── elaboration/ │   ├── resolver.rs │   ├── typecheck.rs │   ├── inference.rs │   └── notation.rs │ ├── kernel/ │   ├── proof.rs │   ├── checker.rs` 

- `│   ├── rules.rs │   ├── substitution.rs │   └── equality.rs │ ├── engine/ │   ├── search.rs │   ├── unification.rs │   ├── indexing.rs │   ├── tabling.rs │   ├── simplifier.rs │   ├── induction.rs │   └── tactics/ │ ├──apply rs` 

This is a target architecture, not a recommendation to create all these files immediately. 

The key boundaries are: 

- `syntax` understands what the user wrote. 

- `elaboration` determines what their expressions mean. 

- `kernel` checks mathematical correctness. 

- `engine` searches for proofs. 

- `universe` manages mathematical contexts and dependencies. 

- `library` handles persistence and compiled modules. 

- `interface` communicates with the user. 

The kernel should ideally have very few dependencies and no dependency on the search engine. 

That prevents the reasoning engine from accidentally becoming part of the trusted foundation. 

# **9. Performance roadmap, in priority order** 

I wouldn't implement every optimization at once. 

Some of them depend on others, and optimizing an unstable logical foundation is wasted effort. 

Here's the order I recommend. 



<!-- Start of picture text -->
Priority Improvement Expected benefit<br>P0 Correctness tests and profiling Establish trustworthy baseline<br>P1 Axiom and fact indexing Avoid irrelevant searches<br>P1 Fix substitution and variable identity Correctness and reduced overhead<br>P1 Termination-safe rewriting Prevent runaway normalization<br>P2 Rollback substitutions Reduce branch allocation<br>P2 Semi-naive forward chaining Much better deduction scaling<br>P2 Memoization and tabling Avoid repeated proof searches<br>P3 Arena-based AST Reduce allocations and memory<br>P3 Proof DAGs Reduce repeated proof storage<br>P3 Incremental module compilation Faster project loading<br>P4 Parallel proof exploration Utilize multiple CPU cores<br><!-- End of picture text -->

## **9.1 Benchmarking must become part of development** 

I would add Criterion benchmarks and a dedicated collection of test theories. 

For example: 

Plain text `benchmarks/ parsing.rs` 

```
    unification.rs
    rewriting.rs
    forward_chaining.rs
    proof_search.rs
    module_loading.rs
tests/
    logic/
    arithmetic/
    geometry/
    universe/
    kernel/
```

### Track: 

Time to parse a module. 

- Time to elaborate a module. Time to prove a theorem. Number of search nodes. Number of unification attempts. Number of cache hits. 

- Number of allocated expressions. Peak memory consumption. 

The most important metric isn't just execution time. 

It's how execution time scales as the theory grows. 

For example, compare the prover against increasingly large versions of the same theory: 

### **Illustrative scaling experiment** 

A hypothetical benchmark design, not measured Axia performance. Compare search time as the axiom database grows. 



<!-- Start of picture text -->
120<br>90<br>60<br>30<br>0<br>100 500 1,000 5,000 10,000<br>Linear axiom scanning Indexed candidate lookup<br><!-- End of picture text -->

The values above are deliberately illustrative. The actual results need to come from Axia. 

I would also establish a correctness test suite before making substantial changes. 

A faster prover that occasionally accepts invalid proofs is not an improvement. 

# **10. The development roadmap** 

This is how I would actually build the project. 

I would divide it into six phases, with each phase producing something usable. 

# **Axia development roadmap** 

- 1 **Phase 1 — Stabilize the existing engine** 

Foundation 

Add comprehensive logical tests. 

Fix sort enforcement. 

Fix variable identity and substitution. 

Add safe rewrite termination. 

Make parsing reject malformed and incomplete input. 

Separate axioms, givens and deductions. 

Add performance instrumentation. 

Deliverable: a predictable and tested first-order prover. 

### 2 **Phase 2 — Performance overhaul** 

Introduce axiom and fact indexing. 

Implement rollback-based substitutions. Introduce semi-naive forward chaining. Add tabling and memoization. Reduce allocations. Make proof generation deterministic. 

Deliverable: an engine capable of handling substantially larger theories. 

3 **Phase 3 — Trusted kernel** 

Most important milestone 

- **Partially implemented:** a standalone checker validates the current proof-tree format and is called by `prove_checked`.
- **Still required:** replace display-oriented proof trees with formal typed proof objects; introduce first-class universal quantification and its introduction/elimination rules; separate theorem declarations from axioms; require every theorem to pass a complete kernel verification. 

Deliverable: the first genuinely proof-checking Axia. 

### 4 **Phase 4 — Universe system** 

Introduce explicit universe declarations. Build the dependency graph. Implement multi-universe imports. Introduce module namespaces. Add trust and axiom provenance. Implement module caching and incremental loading. 

Deliverable: independently developed mathematical theories that can safely build on one another. 

### 5 **Phase 5 — Advanced reasoning** 

Introduce tactics. Add mathematical induction. Implement a theorem-backed simplifier. Add arithmetic decision procedures. Improve goal-directed search. Introduce inductive types and structural recursion. 

Deliverable: an assistant that can solve nontrivial mathematical problems using multiple reasoning strategies. 

### 6 **Phase 6 — Axia ecosystem** 

Compiled mathematical libraries. Dependency-aware compilation. Rich proof explanations. Interactive proof development. Library versioning. Standard mathematical foundations. Optional parallel proof search. 

Deliverable: a small but capable formal mathematics environment. 

## **10.1 What I would deliberately postpone** 

There are several tempting features I would avoid implementing too early: 

Full dependent type theory. Universe polymorphism. Higher inductive types. Sophisticated automated theorem proving. Distributed proof search. A large standard library. A complex graphical interface. 

These aren't bad ideas. They're simply not the foundation you need right now. 

In particular, I wouldn't attempt to replicate Lean's entire type system before Axia can reliably check ordinary first-order proofs. 

# **11. What should Axia eventually be capable of?** 

I think it's useful to define a concrete target rather than simply saying "something like Lean." 

Here's what I would consider a successful version of Axia. 

**Example: Proving theorems across multiple universes** 

Imagine the following files. 

#### `NaturalNumbers.axia` 

Plain text `universe NaturalNumbers inductive Nat: Zero Succ(Nat) theorem Zero_Is_Natural: Zero : Nat theorem Succ_Is_Natural: forall n : Nat, Succ(n) : Nat` 

#### `Arithmetic.axia` 

Plain text `universe Arithmetic requires: NaturalNumbers definition Add: ... theorem Add_Zero: forall n : Nat, Add(n, Zero) = n theorem Add_Succ: forall n m : Nat, Add(n, Succ(m)) = Succ(Add(n, m))` 

```
NumberTheory.axia
```

Plain text `universe NumberTheory requires:` 



<!-- Start of picture text -->
    Arithmetic<br>definition Even:<br>    ...<br><!-- End of picture text -->



<!-- Start of picture text -->
theorem Even_Zero:<br>    Even(Zero)<br>theorem Even_Add:<br>    forall a b : Nat,<br>    Even(a) AND Even(b)<br>        -> Even(Add(a, b))<br><!-- End of picture text -->

#### `Main.axia` 



<!-- Start of picture text -->
Plain text<br>universe Main<br>requires:<br>    NumberTheory<br>theorem My_Theorem:<br>    Even(Add(Zero, Zero))<br>proof:<br>    rewrite Add_Zero<br>    exact Even_Zero<br>qed<br><!-- End of picture text -->

This example illustrates the direction, not the exact syntax or a claim that the current engine could prove these declarations. 

What matters is the workflow: 

**1.** Axia resolves the dependencies. 

**2.** It loads the appropriate logical context. 

**3.** It elaborates the proposition. 

**4.** It searches for a proof. 

**5.** It constructs a proof object. 

**6.** The kernel verifies the proof. 

**7.** The verified theorem becomes available to dependent modules. 

And crucially, if someone modifies `Add_Zero` , Axia knows which dependent modules need to be rechecked. 

That's the kind of system I would aim for. 

# **12. A few design decisions I would settle early** 

There are some choices that will have enormous consequences later. 

|**Question**|**My recommendation**|
|---|---|
|Logic|Start with intuitionistic first-order logic, with an explicit classical extension|
|Types|Simply typed foundation initially|
|Variable representation|Unique IDs, eventually de Bruijn indices for binders|
|Proof representation|Explicit proof terms|
|Verification|Small independent kernel|
|Search|Backward chaining, tabling and indexed forward chaining|
|Equality|Kernel-supported equality with theorem-backed rewriting|
|Universes|Named logical contexts|
|Dependencies|Directed acyclic graph|



|Module compilation|Content-addressed caching|
|---|---|
|Storage|Human-readable source plus compiled artifacts|
|Language implementation|Continue with Rust|



One particularly important decision is the logic. 

I would start with intuitionistic logic and make classical reasoning an explicit extension or imported theory. 

This avoids silently baking classical principles into the foundation. 

You can then make the assumptions of a mathematical universe visible. 

# **13. My suggested first implementation sprint** 

I wouldn't start by implementing the universe graph or induction. 

I would first make the existing implementation safe enough to build upon. 

These are the first changes I would actually make: 

|**Sprint 1**|Recommended starting point|
|---|---|
|8 / 9 completed|89%|
|**- [x] Add integration tests for the existing logical operators**<br>Tests<br>**- [x] Fix sort propagation and enforce function signatures**<br>Type system<br>**Introduce unique variable IDs**<br>AST<br>**- [x] Correct capture-avoiding substitution and quantifier handling**<br>Logic<br>**- [x] Add termination protection to the simplifier**<br>Engine<br>**- [x] Reject malformed input and trailing unparsed tokens**<br>Parser<br>**- [x] Add axiom/fact indexing**<br>Performance<br>**- [x] Add Criterion benchmarks**<br>Performance<br>**- [x] Separate trusted assumptions from derived facts**<br>Architecture||



### **Sprint 1 progress log**

**Unique variable identity — parser migration started**

- Parser-created bound variables now receive globally unique internal identities instead of using their source spelling as their identity.
- Nested binders with the same spelling resolve to different identities; occurrences inside each scope retain the matching identity.
- Repeated occurrences of a free variable within one parsed expression share an identity, while separate parser scopes do not accidentally alias.
- Axiom instantiation and alpha-renaming preserve identity suffixes, and AST / REPL formatting hides the internal representation so users continue to see the source variable name.
- Added parser regression tests for nested same-name binders and repeated free-variable occurrences, separate free-variable scopes, and alpha-equivalence across distinct binder identities.
- This is the first functional identity step. The public AST and substitution map still encode identity in opaque strings; replacing those with a dedicated `VarId` type and migrating the kernel's binding interfaces remains outstanding. Do not mark the Sprint 1 identity objective complete yet.

### **Sprint 1 progress log**

**Simplifier termination protection — done**

- Added active-path cycle detection for rewrite loops.
- Added a 256-rewrite budget per simplification call to bound expanding rewrite rules.
- Added regression tests for cyclic and expanding rewrite rules. The project maintainer ran the test suite successfully.

### **Sprint 1 progress log**

**Reject malformed input and trailing unparsed tokens — done**

- `lex_checked` reports unknown characters instead of silently dropping them (`A & B` previously parsed as two formulas because `&` vanished). `lex` keeps its lenient behaviour.
- `Parser::parse_formula_complete` and `parse_statement_complete` fail on leftover tokens and incomplete input. The REPL (`prove`, `assert`, bare statements) now uses them and prints the reason.
- The parser rejects unbalanced parentheses, trailing or leading commas in argument lists, `Name :` followed by nothing valid, numeric sort names, and malformed `forall` headers. The catch-all that silently declared a predicate has been removed.
- New tests in `tests/malformed_input.rs`. The bundled `lib/` files still load with no parse errors.

**Observed while testing (not fixed, belongs to Phase 2):** deduction order in `lib/geometry/euclid.axia` varies between runs because of HashMap iteration. This matches the Phase 2 goal of deterministic proof generation.

One thing I would explicitly avoid: rewriting the entire engine in one go. 

Keep the current prover operational while introducing the new architecture alongside it. You can gradually move functionality across boundaries and compare the new implementation against the old one. 

# **14. Final assessment** 

I think Axia has a genuinely interesting direction, and I would preserve its current identity rather than turn it into a conventional programming language with a theorem-proving feature bolted on. 

The Universe concept should be its defining architectural feature. 

I would summarize the vision in three layers: 

# **01 — The Foundation** 

**A formal logical system** 

Types, propositions, axioms, definitions, quantifiers, equality and a trusted kernel. 

# **02 — The Intelligence** 

### **A mathematical reasoning engine** 

Proof search, unification, rewriting, induction, tactics, caching and automated deduction. 

# **03 — The Universe** 

**An interconnected body of mathematical knowledge** 

Independent theories, logical dependencies, reusable theorems, definitions and explicit assumptions. 

The ultimate objective: 

**A mathematical statement should be able to exist in its own logical universe, depend on other mathematical universes, and be proven using everything those universes establish — without ever sacrificing formal verification.** 

That's a much more interesting goal than simply making a theorem prover that can handle more complicated formulas. 

## **References to the current implementation** 

These are the main files I based the assessment on: 

ast.rs 

<u>parser.rs</u> engine.rs main.rs Cargo.toml 

This is an architectural review of the source, not a completed runtime audit: I haven't benchmarked the implementation or exhaustively tested its existing mathematical library. 

**My strongest recommendation:** Start with Phase 1, but design the new proof-object and kernel interfaces before committing to the AST changes. That way, performance improvements and new logical features will all move towards the same architecture instead of requiring another major redesign later. 

The next useful step would be turning this roadmap into a concrete, dependency-ordered implementation specification, including Rust structures, module interfaces and acceptance tests for every phase. 



**Axiom/fact indexing — done**

- Indexed backward proof-search axioms by conclusion head and givens by formula head.
- Indexed forward rules by their first premise head and facts by formula head.
- Added regression tests proving that irrelevant formula constructors, predicate names and arities are filtered without changing unification bindings.
- The project maintainer ran the test suite successfully.


**Criterion benchmark suite — done**

- Added `benches/engine.rs` with separate proof-search and forward-deduction benchmarks at chain sizes 8, 32 and 128.
- Each workload includes unrelated facts and rules to exercise formula-head indexing rather than measuring only a trivial linear chain.
- Workload construction is outside the timed routine via Criterion's batched iteration.
- Validated with `cargo test` and `cargo bench --bench engine`.
- Latest proof-search benchmark changes after trail migration: 8 = 9.1% faster, 32 = 29.4% faster, 128 = 35.0% faster.
- Forward deduction: 8 = 4.6% slower, 32 = 10.7% faster, 128 = no statistically significant change.


**Trusted assumptions vs. derived facts — done**

- Split the universe fact store into `assumptions` (explicitly supplied by the user) and `derived` (facts produced by forward deduction).
- Added `Universe::all_facts()` as the combined read-only reasoning view, preserving existing proof-search and deduction behavior while retaining provenance in storage.
- Changed `assert` to add an assumption rather than manufacturing a premise-free axiom.
- Updated `universe_info` and universe summaries to report trusted assumptions and derived facts separately.
- Forward deduction now reads the combined fact view and writes discoveries only to the derived store.


**Rollback-capable substitution core — done**

- Introduced a trail-backed `Substitution` environment with checkpoints, rollback, binding resolution and transactional term/formula unification.
- A failed unification now restores the exact pre-attempt environment, including failures that occur after earlier arguments have already matched.
- Kept the existing `Formula::unify` and `Bindings` interfaces as compatibility adapters, while adding `unify_into` for callers that reuse a substitution environment.
- Added regression tests for partial-match rollback, overwritten bindings, branch rollback and occurs-check failure.
- This is the first migration step, not the completed proof-search optimization: recursive DFS still carries legacy binding snapshots. The next step is to move its branch exploration onto this shared trail and remove those repeated map clones.


**Trail-backed backward proof search — done**

- Replaced branch-local binding-map snapshots in backward DFS with one mutable `Substitution` and checkpoint/rollback.
- Added continuation-based search: a successful earlier premise remains active while later premises are explored, so failure backtracks directly into the earlier candidate.
- Preserved IDDFS depth accounting, the global operation budget, cycle detection, existential witness handling, indexed candidate lookup and proof-tree construction.
- Sorted indexed given names to make candidate exploration reproducible.
- Added regression tests for conjunction backtracking, shared bindings across multiple premises, existential witness preservation and disjunction fallback.
- The successful top-level result takes one final binding snapshot; intermediate branches no longer clone and merge complete substitution maps.
- Validated by the maintainer: all 30 library tests, 30 binary tests, 11 logical-operator integration tests and 8 malformed-input tests passed.
- Criterion showed proof-search improvements of 9.1%, 29.4% and 35.0% at chain sizes 8, 32 and 128 respectively.


**Capture-avoiding substitution and quantifier alpha-equivalence — done**

- Substitution now removes a locally bound variable from the active environment and alpha-renames the binder whenever a replacement would otherwise be captured.
- Bound-occurrence renaming respects nested shadowing.
- Existential formulas now unify modulo binder names, while requiring matching sorts.
- Added regression tests for capture prevention, shadowing and alpha-equivalent quantified formulas.
- The maintainer ran `cargo fmt --check` and `cargo test` successfully; this Sprint 1 objective is complete.


---

# Current implementation status — 2026-11-06

This section records the implementation that now exists, rather than the longer-term target architecture described above.

## Trusted kernel — initial boundary implemented

**Standalone proof-tree checker — implemented**

- Added `src/kernel.rs`, which checks candidate proof trees without invoking proof search.
- The checker explicitly validates the currently supported proof steps: equality reflexivity, named assumptions/derived facts, conjunction introduction, disjunction introduction, existential witness instantiation, and named axiom applications.
- It checks that axiom applications establish their conclusion and provide a proof for every premise.
- Malformed proof trees and references to unknown axioms/facts are rejected with a structured error containing the failing child path.
- Integrated kernel checking into `prove_checked`; a search result is no longer returned as a checked proof until the checker accepts it.
- Added positive and adversarial unit tests for assumptions, conjunctions, axiom premises, unknown rules and malformed reflexivity.
- The maintainer reported that the full test suite passed after the initial checker integration.

**Original-goal binding check — implemented (initial guard)**

- The checked entry point must verify that the root of the candidate proof still establishes the exact proposition requested by the caller.
- This is necessary because the search engine currently simplifies equality terms before constructing a reflexivity proof. Checking only the simplified proof tree could otherwise accept a proof of a different equality.
- The current implementation adds `check_proof_for_goal`, which checks that the proof root unifies with the caller's original goal before recursively checking the tree.
- A regression test rejects a valid reflexivity proof when it is offered for a different requested equality.
- This is an initial guard, not a replacement for explicit proof steps for rewriting. Rewriting must eventually be represented in the proof object and checked from equality premises/rules.

**Still required for a genuinely small trusted kernel**

- Strengthen existential witness checking, including sort correctness and capture avoidance.
- Represent equality rewriting as explicit checked derivations rather than preprocessing performed outside the proof tree.
- Add first-class universal quantification and its introduction/elimination rules.
- Distinguish theorem declarations from axioms and require every theorem to pass kernel verification.

## Next architectural priorities

1. Finish the kernel trust boundary: exact goal preservation, checked rewriting, and stronger validation of existential witness data.
2. Introduce first-class universal quantification and robust variable identity/capture-avoiding substitution.
3. Separate verified theorem declarations from axioms and assumptions.
4. Continue with the named-universe dependency graph after theorem provenance and verification are reliable.

The existing search engine remains a proof-discovery component. It is not part of the trusted kernel, and passing the current tests does not yet establish that Axia has a complete formal proof assistant kernel.


## Typed proof-rule migration — done

- Introduced a `ProofRule` enum for equality reflexivity, named givens, named axioms, conjunction/disjunction introduction, and existential introduction.
- Migrated proof search to construct these variants directly rather than encoding rule identity in strings.
- Migrated the kernel checker to match on typed constructors. Every `ProofRule` variant is handled explicitly; the checker no longer parses display strings.
- Kept human-readable labels at the presentation boundary for the REPL formatter.
- Extended typed axiom proof nodes to carry explicit variable instantiations. The kernel checks that every supplied key is declared by the referenced axiom, applies the substitution to the conclusion and every premise, and rejects mismatches.
- The search engine records the resolved instantiation at the point where all premises have succeeded; the proof object no longer asks the kernel to invent one by unifying the conclusion with the goal.
- This remains an incremental proof-object design: existential witness sort/capture validation and explicit equality-rewrite derivations are still outstanding.

**Explicit axiom instantiations — implemented (first stage)**

- Extended `ProofRule::Axiom` with a substitution map keyed by the axiom's declared variable names.
- Proof search captures each declared variable's resolved term after all premises have succeeded, then stores that data in the proof node.
- `ProofStep::apply_bindings` also resolves terms stored inside axiom proof data.
- The kernel no longer derives an axiom substitution by unifying the conclusion with the claimed goal. It applies the supplied substitution to the axiom conclusion and every premise, checks the conclusion exactly, and rejects substitution keys not declared by the axiom.
- Added adversarial tests for undeclared substitution keys and mismatched premises, plus an end-to-end test that checks proof search records an instantiation accepted by the kernel.
- The maintainer should run `cargo test` before this change is merged.

**Incremental semi-naive forward indexes — implemented and benchmark-validated**

- The complete known-fact index is built once at the start of saturation instead of being reconstructed from every known fact on every deduction round.
- Newly derived facts are inserted into that index as they enter the fact database.
- Forward-rule candidate selection iterates the distinct formula heads in the current delta and looks up only those heads in the rule index, rather than scanning every indexed premise head.
- Candidate rule positions remain sorted and deduplicated, preserving deterministic rule exploration despite hash-map iteration order.
- Added regressions for incremental fact insertion, duplicate insertion, sorted fact names, and delta-driven rule selection.
- The maintainer reported the full suite passing: 46 library tests, 46 binary tests, 11 logical-operator integration tests and 8 malformed-input tests.
- Criterion results against the saved baseline:
  - 8 distractors: 97.640 µs median, 21.635% faster.
  - 32 distractors: 359.13 µs median, 64.916% faster.
  - 128 distractors: 1.4192 ms median, 88.960% faster.
- Proof-search benchmarks in the same run regressed by approximately 5–7% at all three sizes. This change does not modify the backward proof-search implementation, so that result is recorded for investigation rather than attributed to the forward-index change.
- The optimization is validated for correctness and shows substantial measured gains in forward deduction.


## Sprint 1 final item — typed variable identities (implementation in review)

- Added an opaque `VarId` newtype to the AST. Variable identity is now a distinct type rather than an ordinary `String`; its payload is private and source-level spelling is exposed only through the display boundary.
- Migrated `Term::Var`, existential binders, and parsed axiom-variable declarations to carry `VarId`.
- Migrated substitution maps and rollback-trail keys to `VarId`, including unification, occurs checks, capture avoidance, and alpha-renaming.
- Axiom instantiation now derives fresh typed identities, and proof-object existential witnesses carry `VarId`.
- The kernel's existential substitutions and explicit axiom-instantiation validation now consume the typed identities.
- Parser scopes and free-variable interning now store `VarId`; nested shadowing still receives distinct identities while repeated free-variable occurrences share one identity within a parser.
- Added AST regressions for fresh identity uniqueness and stable display names across derived instances.
- **Validation status:** implementation is on `logic/typed-varid-sprint-one`; the Rust toolchain is unavailable in the editing environment, so this migration has not yet been compiled or tested here. Keep the Sprint 1 checkbox open until the maintainer runs `cargo test` (and `cargo fmt --check`, if rustfmt is installed) against this branch.
