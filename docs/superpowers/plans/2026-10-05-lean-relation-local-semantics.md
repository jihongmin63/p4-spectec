# Relation-local SpecTec to Lean Semantics Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Replace the default global WFS/fresh-counter translation with ordered relation-local SCC semantics, typed callbacks, branch-local nominal fresh allocation, local proof tools, and complete verified case 0/1/5 obligations.

**Architecture:** Preserve the existing typed rule AST and legacy counter modes.  The new default runs an ordered lowering, computes typed callback-aware relation SCCs, and prints one local WFS/evaluator component per SCC.  A local nominal supply is hidden behind public direct judgements, and accepted/rejected corpus obligations use checked certificates without assuming determinism.

**Tech Stack:** OCaml 4.14/dune, Lean 4.34.1, Python 3 regression and measurement runners.

**Spec:** `docs/superpowers/specs/2026-10-05-lean-relation-local-semantics-design.md`

## Global Constraints

- Default generation must not emit a root `Atom`, root `InProgram`, or program-wide fresh counter.
- Preserve `--fresh-rollback` exactly as a separately labelled legacy experiment and expose the previous default as `--fresh-exact-counter`.
- Do not treat one failed output candidate as failure of a call or infer relation-wide determinism.
- Propagate recoverable `Unmatch` to the next alternative; propagate `Err`/extern abort, unsupported syntax, and timeout as distinct terminal outcomes.
- Keep source premise order, callback target types, extern conditions, protected ordinary names, capture avoidance, and whole-output alpha consistency.
- Do not claim global-WFS equivalence outside the checked graph-decomposition conditions.
- Generated proof/certificate declarations may depend only on `propext`, `Classical.choice`, and `Quot.sound`.

## Review Focus

- A callback passed through two higher-order relations and invoked recursively must join only the SCCs reached by that value; Task 1 adds `callback-transitive.watsup`.
- A relation with multiple successful outputs must not be rejected after the first output mismatches; Task 3 adds `output-search.watsup`.
- An extern abort after a successful prefix must stop before `otherwise`; Task 3 adds an abort certificate fixture.
- A fresh-derived value entering lexical ordering or concatenation must produce an explicit compatibility obligation/error; Task 4 adds unsafe-observation fixtures.
- An unrelated pure relation in a spec containing extern declarations must have no extern type/model parameter; Task 2 extends the locality checker.

---

### Task 1: Typed callbacks and relation dependency SCCs

**Files:**
- Modify: `p4spec/lib/lean-skeleton/ast.ml`
- Modify: `p4spec/lib/lean-skeleton/translator.ml`
- Modify: `p4spec/lib/lean-skeleton/traversal.ml`
- Modify: `p4spec/lib/lean-skeleton/order.ml`
- Modify: `p4spec/lib/lean-skeleton/relation_optimizer.ml`
- Create: `p4spec/lib/lean-skeleton/relation_graph.ml`
- Modify: `p4spec/lib/lean-skeleton/dune`
- Create: `p4spec/test/backend-lean/check_relation_graph.py`
- Create: `p4spec/test/backend-lean/callback-transitive.watsup`
- Modify: `p4spec/test/backend-lean/dune`

**Interfaces:**
- Consumes: translated `L.program`, rule applications, `RelationType`, and source input positions.
- Produces: typed `L.FunctionReference { target; signature }`; `Relation_graph.analyze : L.program -> (analysis, Diagnostic.t) result`; components in dependency order with signed direct edges, resolved callback edges, extern callback sites, and checked decomposition conditions.

- [ ] **Step 1: Write the failing graph regression**

Create a fixture with direct recursion, negative recursion, a callback passed through two functions, two same-typed but unreachable named functions, and an external callback.  Assert literal component membership and edge kinds from `--dump-relation-graph`; assert the unreachable same-typed target is absent.

- [ ] **Step 2: Run the graph regression and verify RED**

Run: `opam exec --switch=spectecx -- dune build p4spec/test/backend-lean/relation-graph-test`

Expected: FAIL because `--dump-relation-graph` and typed callback metadata do not exist.

- [ ] **Step 3: Preserve callback signatures and implement points-to propagation plus Tarjan SCCs**

Add exact callback signatures to function references.  Propagate named targets through callback arguments to local invocation sites, retain edge polarity, reject unresolved named callbacks, and keep extern callbacks as typed boundary edges.

- [ ] **Step 4: Run focused and existing translation tests**

Run: `opam exec --switch=spectecx -- dune build p4spec/test/backend-lean/relation-graph-test @p4spec/test/backend-lean/backend-lean`

Expected: PASS with the new graph fixture and the unchanged legacy output path.

- [ ] **Step 5: Commit**

```bash
git add p4spec/lib/lean-skeleton p4spec/test/backend-lean
git commit -m "feat(lean): compute typed relation dependency SCCs"
```

### Task 2: Relation-local printer and legacy mode split

**Files:**
- Modify: `p4spec/lib/lean-skeleton/main.ml`
- Modify: `p4spec/lib/lean-skeleton/pipeline.ml`
- Modify: `p4spec/lib/lean-skeleton/printer.ml`
- Modify: `p4spec/lib/lean-skeleton/wfs_backend.ml`
- Modify: `p4spec/lib/lean-skeleton/README.md`
- Create: `p4spec/test/backend-lean/check_relation_local.py`
- Create: `p4spec/test/backend-lean/relation-local.watsup`
- Create: `p4spec/test/backend-lean/relation-local-proof.lean`
- Modify: `p4spec/test/backend-lean/dune`

**Interfaces:**
- Consumes: `Relation_graph.analysis` from Task 1 and the ordered `L.program`.
- Produces: default SCC-local atom/program declarations, direct public relations plus `.fails`/`.undetermined`; legacy global output selected only by `--fresh-exact-counter` or `--fresh-rollback`; checked WFS decomposition metadata.

- [ ] **Step 1: Write the failing locality tests**

Assert behavior by compiling a proof that inverts only an `errorDeclaration` relation, a negative-cycle proof confined to its SCC, and a typed callback proof.  Inspect generated declaration names only to enforce the public compatibility contract: no root `Atom`/`InProgram`, no global membership aliases, and no extern context on an unrelated relation.

- [ ] **Step 2: Run and verify RED**

Run: `opam exec --switch=spectecx -- dune build p4spec/test/backend-lean/relation-local-test`

Expected: FAIL because default output still contains root `Atom` and `InProgram`.

- [ ] **Step 3: Add the explicit legacy option and local SCC printer**

Implement `--fresh-exact-counter`; retain current printer/lowering behind the two legacy flags.  In default mode partition rule premises at print time: same-SCC calls remain WFS atoms, earlier-SCC calls become direct side judgements, and external callbacks remain typed boundary outcomes.  Generate failure over all output positions and undetermined only for cyclic SCCs.

- [ ] **Step 4: Add and use the WFS decomposition theorem**

Extend `wfs_backend.ml` with the program-extension/decomposition result needed by generated metadata.  Compile a fixture proving the local/public result and its legacy global counterpart under the emitted closure conditions.

- [ ] **Step 5: Run focused, legacy, and full backend tests**

Run: `opam exec --switch=spectecx -- dune build p4spec/test/backend-lean/relation-local-test @p4spec/test/backend-lean/backend-lean`

Expected: PASS; legacy fixture source hashes remain reproducible under their explicit flags.

- [ ] **Step 6: Commit**

```bash
git add p4spec/lib/lean-skeleton p4spec/test/backend-lean
git commit -m "feat(lean): emit relation-local WFS components by default"
```

### Task 3: Ordered evaluator and shared premise execution

**Files:**
- Modify: `p4spec/lib/lean-skeleton/ast.ml`
- Create: `p4spec/lib/lean-skeleton/ordered_semantics.ml`
- Modify: `p4spec/lib/lean-skeleton/translator.ml`
- Modify: `p4spec/lib/lean-skeleton/printer.ml`
- Modify: `p4spec/lib/lean-skeleton/wfs_backend.ml`
- Modify: `p4spec/lib/lean-skeleton/dune`
- Create: `p4spec/test/backend-lean/ordered-eval.watsup`
- Create: `p4spec/test/backend-lean/ordered-eval-proof.lean`
- Create: `p4spec/test/backend-lean/output-search.watsup`
- Create: `p4spec/test/backend-lean/output-search-proof.lean`
- Create: `p4spec/test/backend-lean/check_ordered_eval.py`
- Modify: `p4spec/test/backend-lean/dune`

**Interfaces:**
- Consumes: relation rules in source order, premise provenance/catchability, input/output positions, and local SCC calls.
- Produces: shared prefix-flow helpers and `SpecTecEval.Outcome`; per-relation `eval`, `success_sound`, failure, abort, unsupported, timeout, and local-undetermined certificate interfaces.

- [ ] **Step 1: Write failing behavioral regressions**

Cover distinct constructors, same-pattern premise failure followed by success, failure at each premise position, multiple possible outputs, `otherwise` after all ordinary failures, `Err`/extern abort before fallback, unsupported syntax, timeout, and negative-cycle undetermined.

- [ ] **Step 2: Run and verify RED**

Run: `opam exec --switch=spectecx -- dune build p4spec/test/backend-lean/ordered-eval-test`

Expected: FAIL because the outcome/evaluator declarations and prefix certificates do not exist.

- [ ] **Step 3: Implement prefix-flow lowering and ordered alternative certificates**

Generate one prefix relation per rule and premise boundary.  Failure constructors reference the prefix certificate and the first failing premise; they do not duplicate earlier premises.  Constructor mismatch is discharged by local no-confusion.  Unknown outputs are searched existentially and a call fails only with a universal no-success certificate.

- [ ] **Step 4: Implement evaluator outcomes and soundness**

Add fuel-indexed evaluator certificates, immediate propagation for abort/unsupported, timeout at zero fuel, and local WFS undetermined.  Prove only `success_sound`; add separate theorems for all-output/rejection when their premises explicitly supply universal evidence.

- [ ] **Step 5: Run focused mutation checks and full backend tests**

Run: `opam exec --switch=spectecx -- dune build p4spec/test/backend-lean/ordered-eval-test @p4spec/test/backend-lean/backend-lean`

Expected: PASS.  Mutating the next-rule gate to accept abort or one-output failure must make the focused proof fail.

- [ ] **Step 6: Commit**

```bash
git add p4spec/lib/lean-skeleton p4spec/test/backend-lean
git commit -m "feat(lean): model ordered evaluation outcomes"
```

### Task 4: Nominal fresh IDs, local supplies, and alpha compatibility audit

**Files:**
- Modify: `p4spec/lib/lean-skeleton/translator.ml`
- Modify: `p4spec/lib/lean-skeleton/printer.ml`
- Modify: `p4spec/lib/lean-skeleton/fresh_alpha.ml`
- Modify: `p4spec/lib/lean-skeleton/case_obligation.ml`
- Create: `p4spec/lib/lean-skeleton/fresh_nominal.ml`
- Modify: `p4spec/lib/lean-skeleton/dune`
- Create: `p4spec/test/backend-lean/fresh-nominal.watsup`
- Create: `p4spec/test/backend-lean/fresh-nominal-proof.lean`
- Create: `p4spec/test/backend-lean/check_fresh_nominal.py`
- Modify: `p4spec/test/backend-lean/dune`

**Interfaces:**
- Consumes: evaluator call/rule/premise/iteration paths and protected input/context names.
- Produces: `FreshSite`, `FreshId`, `FreshName`, branch-local `FreshSupply`, nominal alpha bijection, erasure/render compatibility obligations, and a static fresh-text observation audit.

- [ ] **Step 1: Write failing nominal regressions**

Cover failed-alternative rollback, sequential/recursive/iterated uniqueness, repeated references, ordinary collision, binder scope, capture avoidance, context extension, and consistent whole-output alpha.  Add unsafe concatenation, lexical comparison, and sorted-set fixtures that must fail with a precise compatibility diagnostic.

- [ ] **Step 2: Run and verify RED**

Run: `opam exec --switch=spectecx -- dune build p4spec/test/backend-lean/fresh-nominal-test`

Expected: FAIL because default output still uses `Nat`/`FRESH__` counter state.

- [ ] **Step 3: Implement nominal allocation and protected rendering**

Allocate by dynamic local path and site occurrence.  Snapshot at alternatives, discard on recoverable failure, and commit successful sequential state.  Preserve one identifier across repeated references and prohibit rendered collision with protected ordinary names.

- [ ] **Step 4: Replace prefix-string alpha with nominal whole-output alpha**

Generate one injective mapping over all allocated IDs, fix every ordinary name, and prove erasure respects binders/scope/capture avoidance.  Case obligations use nominal provenance, never the `FRESH__` prefix alone.

- [ ] **Step 5: Implement compatibility audit and legacy correspondence conditions**

Permit nominal equality/capture operations.  Emit a checked obligation or reject fresh-derived concatenation, order, printing-as-control, and sorted-set use.  Document and test the condition under which legacy exact-counter output erases to an alpha-equivalent nominal output.

- [ ] **Step 6: Run focused, legacy fresh, and full backend tests**

Run: `opam exec --switch=spectecx -- dune build p4spec/test/backend-lean/fresh-nominal-test @p4spec/test/backend-lean/backend-lean`

Expected: PASS; legacy exact-counter and rollback fixtures still pass only under their explicit modes.

- [ ] **Step 7: Commit**

```bash
git add p4spec/lib/lean-skeleton p4spec/test/backend-lean
git commit -m "feat(lean): use branch-local nominal fresh supplies"
```

### Task 5: Local induction, inversion, and certificate proof support

**Files:**
- Modify: `p4spec/lib/lean-skeleton/SpecTecProof.lean`
- Modify: `p4spec/lib/lean-skeleton/printer.ml`
- Modify: `p4spec/test/backend-lean/check_proof_support.py`
- Modify: `p4spec/test/backend-lean/proof-support-proof.lean`
- Create: `p4spec/test/backend-lean/local-proof-support.lean`
- Modify: `p4spec/test/backend-lean/dune`

**Interfaces:**
- Consumes: generated SCC-local membership, public judgement, evaluator outcomes, and certificates.
- Produces: `spec_induction`, `spec_invert`, and `spec_check_certificate` scoped to one relation/SCC; preserved axiom audit.

- [ ] **Step 1: Write a failing local proof-support check**

Prove `Decl_ok/errorDeclaration` inversion without handlers for constant, instantiation, function, or action constructors.  Assert certificate rejection for a wrong rule index, wrong premise position, one-output failure, and abort-as-failure.

- [ ] **Step 2: Run and verify RED**

Run: `opam exec --switch=spectecx -- dune build p4spec/test/backend-lean/local-proof-support-test`

Expected: FAIL because only global `spec_invariant` closure generation exists.

- [ ] **Step 3: Implement local commands and remove global closure assumptions**

Generate induction/inversion from the selected local membership type and no-confusion lemmas.  Check certificate constructors against the local evaluator.  Keep stale/unused handler errors and the allowed-axiom audit.

- [ ] **Step 4: Verify generated support size and axioms**

Run: `opam exec --switch=spectecx -- dune build p4spec/test/backend-lean/local-proof-support-test @p4spec/test/backend-lean/backend-lean`

Expected: PASS with no `sorryAx` and no unapproved axioms.

- [ ] **Step 5: Commit**

```bash
git add p4spec/lib/lean-skeleton p4spec/test/backend-lean
git commit -m "feat(lean): add relation-local proof certificates"
```

### Task 6: Complete cases 0, 1, and 5 and record new-mode measurements

**Files:**
- Modify: `p4spec/test/backend-lean/experiments/cases-0-1-5/Case0000Common.lean`
- Modify: `p4spec/test/backend-lean/experiments/cases-0-1-5/Case0000.lean`
- Modify: `p4spec/test/backend-lean/experiments/cases-0-1-5/Case0001Common.lean`
- Modify: `p4spec/test/backend-lean/experiments/cases-0-1-5/Case0001.lean`
- Modify: `p4spec/test/backend-lean/experiments/cases-0-1-5/Case0005Common.lean`
- Modify: `p4spec/test/backend-lean/experiments/cases-0-1-5/Case0005.lean`
- Create: `p4spec/test/backend-lean/experiments/cases-0-1-5/relation-local-run.py`
- Create: `p4spec/test/backend-lean/experiments/cases-0-1-5/RELATION_LOCAL_RESULTS.md`
- Create: `p4spec/test/backend-lean/experiments/cases-0-1-5/relation-local-measurements.json`

**Interfaces:**
- Consumes: new default semantics, local proof/certificate tools, fixed exact interpreter oracles, and nominal fresh provenance.
- Produces: complete `case_0_proof`, `case_1_proof`, `case_5_proof`, and `case_5_all_outputs_alpha`; separately labelled reproducible measurements.

- [ ] **Step 1: Make the new runner fail on the full goals**

Generate new-mode semantics and cases 0, 1, and 5; compile explicit `example : case_N := case_N_proof` checks plus the case 5 all-output alpha theorem.

Run: `python3 p4spec/test/backend-lean/experiments/cases-0-1-5/relation-local-run.py --artifacts /tmp/lean-cases-0-1-5-relation-local`

Expected: FAIL until all four full goals exist and pass their axiom checks.

- [ ] **Step 2: Prove complete case 0 and case 1 rejection**

Use local inversion and stable shared lemmas.  Do not assume the recorded interpreter rejection or replace WFS failure with absence of success.

- [ ] **Step 3: Prove complete case 5 acceptance**

Check the full 68-declaration execution certificate, including every context/fresh connection.  A first-`ERROR` or conditional reconstruction lemma does not satisfy the runner.

- [ ] **Step 4: Prove the separate all-success-output alpha property**

Use evaluator/certificate completeness and nominal alpha; do not derive it from one successful evaluation or unproved global determinism.

- [ ] **Step 5: Measure the verified new-mode artifacts**

Record generation lines/bytes/theorem and certificate counts; compile wall/CPU/max RSS; proof source length; authoring and failed-check time; and `.olean` sizes.  Preserve the old `RESULTS.md`, `measurements.json`, and `baseline.json` unchanged as the rollback baseline.

- [ ] **Step 6: Run the complete runner, full backend suite, and axiom scan**

Run: `python3 p4spec/test/backend-lean/experiments/cases-0-1-5/relation-local-run.py --artifacts /tmp/lean-cases-0-1-5-relation-local`

Run: `opam exec --switch=spectecx -- dune build @p4spec/test/backend-lean/backend-lean`

Expected: PASS; status records all four full goals true, and no admitted/unapproved axiom appears.

- [ ] **Step 7: Commit**

```bash
git add p4spec/test/backend-lean/experiments/cases-0-1-5
git commit -m "test(lean): verify relation-local corpus cases 0 1 and 5"
```

### Task 7: Final verification and documentation

**Files:**
- Modify: `p4spec/lib/lean-skeleton/README.md`
- Modify: `docs/superpowers/specs/2026-10-05-lean-relation-local-semantics-design.md` only if implementation rulings require clarification

**Interfaces:**
- Consumes: all prior task outputs and measurement records.
- Produces: reproducible user documentation and a clean verified branch.

- [ ] **Step 1: Update mode, semantics, proof, and reproduction documentation**

Document the new default, both legacy flags, exact correspondence conditions, evaluator outcome meanings, nominal alpha, and measurement commands.

- [ ] **Step 2: Run formatting/diff checks and the complete test matrix fresh**

Run: `git diff --check`

Run: `opam exec --switch=spectecx -- dune clean && opam exec --switch=spectecx -- dune build @p4spec/test/backend-lean/backend-lean`

Run the relation-local case runner in a new `/tmp` artifact directory.

Expected: all commands exit 0; generated proofs contain no `sorry`; axiom scans list only the allowed set.

- [ ] **Step 3: Commit final verified documentation or fixes**

```bash
git add p4spec/lib/lean-skeleton/README.md docs/superpowers/specs/2026-10-05-lean-relation-local-semantics-design.md
git commit -m "docs(lean): document relation-local proof workflow"
```
