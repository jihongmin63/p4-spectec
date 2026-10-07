# Lean Reified Evaluator Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Replace rule-specialized Lean evaluator declarations with one reified plan per rule and shared plan selection, failure, evaluation, and soundness definitions while preserving the complete default relation-local semantics.

**Architecture:** Add `SpecTecEval.EvalRulePlan` with a dependent witness and common `Succeeds`/`Fails` interpretations, then interpret ordered or nondeterministic lists through a shared `SpecTecEval.Evaluator`.  Generate only rule data and relation wiring; keep required relation-level aliases and migrate rule-internal proof fixtures to typed plan certificates.

**Tech Stack:** OCaml/Dune, SpecTec IL, Lean 4.34.1, Python 3 structural and proof regressions.

**Spec:** `docs/superpowers/specs/2026-10-06-lean-reified-evaluator-design.md`

## Global Constraints

- Start from `5e85ed7f` on `analysis/il-to-lean4` and preserve any user changes.
- Emit the complete specification and every evaluator in default relation-local mode; do not add or use `--core-only`.
- Preserve source premise order, recoverable positions, ordered and nondeterministic selection, and `otherwise` only after all ordinary rules fail.
- Keep recoverable `Unmatch`, `Err`/extern abort, unsupported, timeout, and undetermined outcomes distinct.
- Failure of one output candidate is not failure of an output-unknown call; `ruleFailure_sound` remains universal over outputs.
- Do not assume relation determinism or generalize one success certificate to rejection, uniqueness, or all-output properties.
- Preserve typed callbacks, extern boundaries, fresh sites and supplies, rollback, nominal alpha, protected ordinary names, and WFS public soundness without new axioms.
- Preserve `Order.extern_dependent_types`, separated fresh-alpha/relation-protection shapes, separated extern/non-extern fresh sections, removal of eager `InProgram.head_property`, and leaf-local `SpecTecProof.spec_invariant` checking.
- Do not modify or run `p4spec/test/backend-lean/experiments/cases-0-1-5/` as a completion condition.
- Compare generation and Lean compilation only with the supplied baseline and the same default-mode input, Lean concurrency, and measurement fields.

## Review Focus

- A rule with dependent and shadowing binders must elaborate through the packed witness without leaking binder names or requiring a global type closure; Task 2 compiles the polymorphic/shadow fixtures and a direct dependent-witness proof.
- A relation with no premises and a relation with 64 ordered guards must avoid empty-list corner failures and recursive-selector elaboration blow-up; Tasks 1 and 3 check both.
- An evaluator call whose target has extern-dependent types must receive exactly the existing inferred contexts, while an unrelated relation remains unparameterized; Task 3 runs extern and locality regressions.
- A recursive positive call and a negative SCC must use the shared selector without turning recursion into rule failure or losing undetermined evidence; Tasks 2 and 3 compile both proofs.
- Two byte-identical full generations from one executable must remain identical even though plans contain dependent witnesses and proof fields; Task 4 performs the byte comparison.

---

### Task 1: RED structure contract and shared rule-plan semantics

**Files:**
- Modify: `p4spec/test/backend-lean/check_ordered_eval.py`
- Modify: `p4spec/lib/lean-skeleton/ordered_semantics.ml`

**Interfaces:**
- Consumes: existing `SpecTecEval.Prefix`, `RuleFailure`, `OutputSearchFailure`, `Boundary`, and `Evaluation`.
- Produces: `SelectionPolicy`; `EvalRulePlan Input Output Public` with `Witness`, `input`, `output`, `premises`, `recoverable`, and `publicSound`; `EvalRulePlan.Succeeds`; `EvalRulePlan.Fails`; indexed `Selected`; `AllFailed`; and their generic soundness theorems.

- [ ] **Step 1: Change the focused checker to require the common reified semantics**

Assert that generated Lean contains one `structure EvalRulePlan`, shared `EvalRulePlan.Succeeds`, `EvalRulePlan.Fails`, `Selected`, and `AllFailed`.  Add isolated Lean snippets that instantiate a no-premise plan, a two-output nondeterministic plan, an ordered two-plan list, and a dependent `Sigma` witness; check success soundness, ordered continuation, all-failed construction, and the inability to use `AlternativeResult.abort`, `.unsupported`, or `.timeout` as continuation evidence.

- [ ] **Step 2: Run the focused test and verify RED**

Run: `opam exec --switch=spectecx -- dune build @p4spec/test/backend-lean/ordered-eval-test`

Expected: FAIL at the new `EvalRulePlan` assertion because `5e85ed7f` has no reified rule-plan semantics.

- [ ] **Step 3: Add the common rule-plan definitions**

Implement the interfaces above in `Ordered_semantics.source`.  `Succeeds` existentially chooses a witness and checks input, output, and `Prefix`; `Fails` universally quantifies output and witness and requires a head mismatch or `RuleFailure`; ordered `Selected` advances only with head `Fails`, while nondeterministic `Selected` may advance directly.

- [ ] **Step 4: Run the focused test and verify GREEN**

Run: `opam exec --switch=spectecx -- dune build p4spec/lib/lean-skeleton/main.exe @p4spec/test/backend-lean/ordered-eval-test`

Expected: PASS; the existing generated evaluator proofs still compile and the new isolated common-semantics snippets pass.

- [ ] **Step 5: Commit the common semantics**

```bash
git add p4spec/lib/lean-skeleton/ordered_semantics.ml \
  p4spec/test/backend-lean/check_ordered_eval.py
git commit -m "feat(lean): define shared reified evaluator plans"
```

### Task 2: Generate one plan per rule and one evaluator per relation

**Files:**
- Modify: `p4spec/lib/lean-skeleton/printer.ml`
- Modify: `p4spec/test/backend-lean/check_ordered_eval.py`
- Modify: `p4spec/test/backend-lean/ordered-eval-proof.lean`
- Modify: `p4spec/test/backend-lean/output-search-proof.lean`

**Interfaces:**
- Consumes: Task 1's `EvalRulePlan`, `Selected`, and `AllFailed`; translated `L.rule.binders`, ordered premises, `catchable`, input positions, and `selection_policy`.
- Produces: `print_eval_rule_plan`; `«relation:eval:rule:N:plan»`; `relation.evalRules`; `relation.evaluator`; and required relation aliases `evalSelected`, `allRulesFailed`, `evalUndetermined`, and `eval`.

- [ ] **Step 1: Add the failing generated-structure assertions**

Require one `:eval:rule:N:plan` per fixture rule; reject generated `:premises`, `:recoverable`, `:succeeds`, `:failed`, and `:sound` declarations; count the common definitions once; and assert nondeterministic selection uses the common `Selected` type rather than a generated disjunction.

- [ ] **Step 2: Run the focused test and verify RED**

Run: `opam exec --switch=spectecx -- dune build @p4spec/test/backend-lean/ordered-eval-test`

Expected: FAIL at the plan-count/legacy-declaration assertions because the printer still emits five declarations per rule.

- [ ] **Step 3: Replace rule-flow printing with dependent witness packing**

Replace `eval_rule_flow`/`print_eval_rule_flow` with a plan result carrying only the plan declaration and call.  Pack binders as nested `Sigma` ending in `Unit`, generate witness destructuring once inside `publicSound`, preserve the exact premise propositions and recoverable indices, and preserve the existing fresh-premise/public-evidence conversions.

- [ ] **Step 4: Replace generated selection and relation proof trees**

Make `print_ordered_evaluator` emit the plan list, `SelectionPolicy`, relation-specific undetermined predicate, and `SpecTecEval.Evaluator`.  Implement `evalSelected` and `allRulesFailed` as aliases/projections of that evaluator; make nested evaluator premises use the generic selected-sound theorem.  Do not emit a per-relation disjunction or case tree.

- [ ] **Step 5: Migrate the focused proof fixtures to plan certificates**

Express mismatch, recoverable failure, ordered next-rule selection, nondeterministic multiple outputs, universal output-search failure, and public soundness through plan projections and `Selected` constructors.  Keep the existing abort, unsupported, timeout, positive recursion, and negative-cycle undetermined examples.

- [ ] **Step 6: Run the focused tests and verify GREEN**

Run: `opam exec --switch=spectecx -- dune build @p4spec/test/backend-lean/ordered-eval-test`

Expected: PASS; the checker reports shared plans/selection and both Lean proof files compile.

- [ ] **Step 7: Compare dependent and shallow prototype costs**

Generate the ordered/search fixtures and the 64-guard size fixture once with the dependent witness implementation.  Record bytes and `lean -j 2` wall/max-RSS in the plan workspace.  If the dependent representation fails to elaborate or is measurably worse than a shallow witness-erasing constructor on the same inputs, use the spec-authorized erasure combinator and record a `Ruling:` with both measurements; do not restore specialized rule declarations.

- [ ] **Step 8: Commit the generator migration**

```bash
git add p4spec/lib/lean-skeleton/printer.ml \
  p4spec/test/backend-lean/check_ordered_eval.py \
  p4spec/test/backend-lean/ordered-eval-proof.lean \
  p4spec/test/backend-lean/output-search-proof.lean
git commit -m "refactor(lean): emit reified evaluator rule plans"
```

### Task 3: Certificate compatibility, integration regressions, and size guard

**Files:**
- Modify: `p4spec/test/backend-lean/check_local_proof_support.py`
- Modify: `p4spec/test/backend-lean/check_size.py`
- Modify: `p4spec/lib/lean-skeleton/README.md`
- Modify if required by typed integration: `p4spec/lib/lean-skeleton/printer.ml`
- Test: `p4spec/test/backend-lean/check_fresh_nominal.py`
- Test: `p4spec/test/backend-lean/check_fresh_supply.py`
- Test: `p4spec/test/backend-lean/check_fresh_rollback.py`
- Test: `p4spec/test/backend-lean/check_relation_local.py`

**Interfaces:**
- Consumes: Task 2's relation evaluator values and plan-list certificate types.
- Produces: generic `SpecTecEval.Evaluator` success/failure/timeout certificate API, documented migration from rule-internal declarations, wrong-rule/wrong-position negative checks, and a structural/byte size ceiling that rejects specialized-flow regression.

- [ ] **Step 1: Migrate the typed certificate checker**

Update successful examples to use the generic evaluator theorem or a measured cheap relation alias.  Rewrite `WrongRule` so a failure certificate indexed by rule 1 is offered where rule 0 is required, and `WrongPosition` so a non-recoverable premise index is offered to the selected plan's premise list.  Keep `AbortAsFailure` and `OneOutputFailure` as compile-fail mutations and assert all successful `#print axioms` output excludes `sorryAx`.

- [ ] **Step 2: Tighten size and repetition assertions**

In `check_size.py`, assert the 16/32/64 rule-growth ratio remains linear, count exactly one plan per source rule, reject the legacy five rule-flow declaration suffixes, and lower the absolute ceilings only after recording the new fixture sizes.  Do not use a timing threshold as a test assertion.

- [ ] **Step 3: Document the generated API migration**

Update the evaluator section of the README with the common plan/evaluator model, the retained relation-level aliases, and the replacement syntax for removed rule-internal names.  State that compatibility aliases omitted for measured cost are intentionally removed rather than silently renamed.

- [ ] **Step 4: Run certificate, size, fresh, extern, recursion, and locality regressions**

Run: `opam exec --switch=spectecx -- dune build @p4spec/test/backend-lean/local-proof-support-test @p4spec/test/backend-lean/ordered-eval-test @p4spec/test/backend-lean/relation-local-test @p4spec/test/backend-lean/fresh-nominal-test @p4spec/test/backend-lean/fresh-supply-test @p4spec/test/backend-lean/backend-lean`

Expected: PASS with no `sorryAx`; ordered/nondeterministic selection, output search, negative-cycle undetermined, fresh/rollback, callbacks, and extern isolation remain checked.

- [ ] **Step 5: Commit the compatibility and regression changes**

```bash
git add p4spec/lib/lean-skeleton p4spec/test/backend-lean
git commit -m "test(lean): verify shared evaluator certificates"
```

### Task 4: Full-spec determinism, compilation, and measured result

**Files:**
- Create: `docs/superpowers/specs/2026-10-06-lean-reified-evaluator-results.md`
- Modify if a verified full-spec issue is found: files owned by Tasks 1--3
- Record temporary artifacts: `.superpowers/sdd/2026-10-06-lean-reified-evaluator/`

**Interfaces:**
- Consumes: the complete implementation, the supplied baseline, default relation-local full `spec` generation, and Lean 4.34.1 with `-j 2`.
- Produces: deterministic generated Lean, total/evaluator bytes and lines, generation wall/CPU/RSS, full compile wall/CPU/RSS, `.olean` bytes, target-attainment statement, and an exact remaining-specialization/obligation inventory.

- [ ] **Step 1: Run the complete backend suite from a fresh implementation build**

Run: `opam exec --switch=spectecx -- dune build @backend-lean`

Expected: PASS.

- [ ] **Step 2: Generate the full default relation-local specification twice**

Use `_build/default/p4spec/lib/lean-skeleton/main.exe --keep-going spec` for both runs, with `/usr/bin/time -v` and separate stdout/stderr files in this plan's workspace.  Do not pass a fresh legacy flag or a relation root.

Expected: both commands exit successfully under the same diagnostics policy; `cmp` reports byte-identical Lean output.

- [ ] **Step 3: Record baseline-compatible source metrics**

Count total bytes/lines, evaluator bytes/lines, header, rule-plan flow, selection wiring, certificate aliases, evaluator relation count, and rule-plan count using the same lexical boundaries as the supplied baseline.  Record generation wall, user, system, and peak RSS.  Report any classifier change caused by new declaration names alongside both raw totals.

- [ ] **Step 4: Compile the complete generated source**

Run: `/usr/bin/time -v lean -j 2 -o <workspace>/Full.olean <workspace>/Full.lean`

Expected: exit 0 with no `sorryAx`; record wall, user, system, peak RSS, and `.olean` bytes.

- [ ] **Step 5: Write the measured result and target assessment**

Record the chosen common representation, per-rule and per-relation generated surface, preserved meanings, every verification command, before/after metrics and percentages, whether ten and five minutes were achieved, remaining specialization or proof obligations, and the final commit hash placeholder to be filled after commit.  Do not claim unmeasured causality.

- [ ] **Step 6: Run final hygiene and whole-change review**

Run: `git diff --check`; inspect `git status --short`; scan changed generated Lean support and proof output for `sorry`, `admit`, `axiom`, and unintended global `head_property`; create the executing-plans review package and request one fresh whole-branch review.  Fix every critical or important finding with a RED→GREEN regression and rerun the full suite.

Expected: only intended source, test, README, spec, plan, and result files differ; no forbidden case-experiment file changed.

- [ ] **Step 7: Commit the verified measurement record**

```bash
git add docs/superpowers/specs/2026-10-06-lean-reified-evaluator-results.md \
  p4spec/lib/lean-skeleton p4spec/test/backend-lean
git commit -m "perf(lean): share reified evaluator interpretation"
```

- [ ] **Step 8: Refresh the result's final hash without rewriting history**

Record `git rev-parse HEAD` in the execution ledger and final report.  If the committed result document used `pending` for the hash, leave it as an explicit self-reference placeholder; do not amend a verified commit solely to embed its own hash.
