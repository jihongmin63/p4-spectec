# Lean SpecTec `$print_` Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Translate `$print_<X>(X) : text` with the exact successful outputs and failure domain of `P4.Unparse.pp_value`, while generating printers only for the four concrete call-site closures.

**Architecture:** Add a partial `SpecTecPrint` typeclass and expose successful calls through an inductive builtin relation. Preserve variant print formats and semantic tuple arity in the Lean AST, propagate printer instance requirements through relations, and extend ordering/printer generation with closure-limited structurally recursive printer functions modeled on manual `DecidableEq`.

**Tech Stack:** OCaml 5.1.1, Dune, SpecTec IL, Lean 4.34.1

**Spec:** `docs/superpowers/specs/2026-09-30-lean-spectec-print-design.md`

## Global Constraints

- `P4.Unparse.pp_value`, `Hints.Alter.alternate`, `Mixfix.assemble`, and OCaml 5.1.1 `Bytes.unsafe_escape` define observable behavior.
- OCaml failures produce no Lean result; no arbitrary catch-all relation rule is allowed.
- Do not use `sorry`, `admit`, `axiom`, or `opaque`.
- Do not modify `spec/` or interpreter code.
- Generate custom printers only for types reachable from concrete `$print_` calls.
- Use `opam exec --switch=spectecx`; use the session-local elan directory without changing the home directory or system PATH.
- Do not create commits; the user's explicit no-commit instruction overrides normal plan commit steps.

## Review Focus

- A hint sequence containing absent or empty fragments must retain the exact number of separator spaces.
- A variant copied into a containing variant must use its origin typcase's print hint after Lean upcast conversion.
- A three-or-more-element tuple must print flat, while a genuinely nested tuple must retain nested parentheses.
- A non-ASCII code point must escape each UTF-8 byte independently as `\\ddd`.
- A structure reached under a list, option, tuple, or variant must make the whole print fail with no `$print_` derivation.

---

### Task 1: Differential Oracle and RED Integration Fixture

**Files:**
- Create: `p4spec/test/backend-lean/print_diff.ml`
- Create: `p4spec/test/backend-lean/print.watsup`
- Create: `p4spec/test/backend-lean/print-proof.lean`
- Modify: `p4spec/test/backend-lean/dune`

**Interfaces:**
- Consumes: `Pass.algo`, `P4.Unparse.hints_of_spec_al`, `P4.Unparse.pp_value`, and `Runtime.Value.Make`.
- Produces: literal expected strings for every Lean example and a focused `print.lean` backend test target.

- [ ] **Step 1: Build a scratch OCaml differential executable**

Construct fixture values with the same type notes and mixops as the test spec, derive the hint environment from the fixture's AL spec, and print labeled outputs only through `P4.Unparse.pp_value`.

- [ ] **Step 2: Run the oracle and record its output**

Run: `cd p4spec && opam exec --switch=spectecx -- dune exec test/backend-lean/print_diff.exe -- test/backend-lean/print.watsup`

Expected: one labeled byte-exact output for every test case, including doubled spaces and decimal byte escapes.

- [ ] **Step 3: Add the complete print fixture and literal Lean expectations**

The fixture defines the builtin and representative default/hinted/included/generic/recursive/structure types. The proof asserts positive relation results, reduction of `SpecTecPrint.print?`, and no derivation for structures.

- [ ] **Step 4: Run the focused target and verify RED**

Run: `cd p4spec && ELAN_HOME=/tmp/p4-spectec-elan.ENxF2N/elan PATH=/tmp/p4-spectec-elan.ENxF2N/elan/bin:$PATH opam exec --switch=spectecx -- dune build test/backend-lean/print.lean`

Expected: FAIL because the Lean backend rejects builtin `print_`.

### Task 2: Partial Builtin Contract and Exact Format Metadata

**Files:**
- Modify: `p4spec/lib/lean-skeleton/ast.ml`
- Modify: `p4spec/lib/lean-skeleton/builtin.ml`
- Modify: `p4spec/lib/lean-skeleton/builtin_relation.ml`
- Modify: `p4spec/lib/lean-skeleton/translator.ml`
- Modify: `p4spec/lib/lean-skeleton/traversal.ml`
- Test: `p4spec/test/backend-lean/print.watsup`
- Test: `p4spec/test/backend-lean/print-proof.lean`

**Interfaces:**
- Consumes: IL typcase hints and origins, existing relation translation, and existing instance-argument propagation.
- Produces: `print_format`, arity-preserving tuple type metadata, `$print_` relation AST, and separate printer-class requirements on declarations/applications.

- [ ] **Step 1: Preserve semantic tuple arity and print formats in the Lean AST**

Add an arity-preserving tuple type form and a normalized fragment tree supporting absent, present, hole, filtered join, positional join, and fuse. Attach one format to each datatype constructor.

- [ ] **Step 2: Translate default mixfix rendering and `hint(print ...)` exactly**

Normalize cursor positions during translation. Use lower-cased atom rendering, omit default Tag atoms, retain hint Tag atoms as present empty strings, and carry copied typcase formats through included variants.

- [ ] **Step 3: Translate `$print_` as a partial relation**

Add `print_` to `Builtin_relation.names`, validate signature `[X] -> String`, and emit one success rule whose premise is `SpecTecPrint.print? value = some result`.

- [ ] **Step 4: Generalize instance propagation**

Track printer parameters and printer application arguments separately from `DecidableEq`; close both requirements through calls and update traversal/dependency logic.

- [ ] **Step 5: Build the translator**

Run: `cd p4spec && opam exec --switch=spectecx -- dune build lib/lean-skeleton/main.exe`

Expected: PASS; the test still fails because no `SpecTecPrint` class or generated instances exist yet.

### Task 3: Closure-Limited Structurally Recursive Printers

**Files:**
- Modify: `p4spec/lib/lean-skeleton/ast.ml`
- Modify: `p4spec/lib/lean-skeleton/order.ml`
- Modify: `p4spec/lib/lean-skeleton/printer.ml`
- Test: `p4spec/test/backend-lean/print.watsup`
- Test: `p4spec/test/backend-lean/print-proof.lean`

**Interfaces:**
- Consumes: print roots from `$print_` applications, constructor formats, tuple arity, and printer class requirements from Task 2.
- Produces: Lean `SpecTecPrint`, exact primitive/container helpers, one function per reachable datatype, nested container helpers, and named type instances.

- [ ] **Step 1: Add the generated Lean print prelude**

Define `SpecTecPrint`, fragment combinators, exact UTF-8 byte escaping, base instances, and generic list/option/binary-product behavior without hidden assumptions.

- [ ] **Step 2: Discover the concrete print closure**

Collect non-self `$print_` type arguments, expand aliases, stop traversal at structures, and mark only reachable data declarations. Report unsupported root/generic shapes using the owning source region.

- [ ] **Step 3: Build printer shapes for each reachable data SCC**

Generate datatype, structure, list, option, and semantic tuple functions. Detect non-uniform recursive instantiations using the manual-equality pattern and create stable helper names from `Translator.type_code`.

- [ ] **Step 4: Render mutual functions and instances**

Emit one function per type/shape, `termination_by structural`, `none` for structures, and instances after the mutual block. Constructor branches print every argument before evaluating the normalized format.

- [ ] **Step 5: Run the focused test and verify GREEN**

Run: `cd p4spec && ELAN_HOME=/tmp/p4-spectec-elan.ENxF2N/elan PATH=/tmp/p4-spectec-elan.ENxF2N/elan/bin:$PATH opam exec --switch=spectecx -- dune build test/backend-lean/print.lean`

Expected: PASS with all oracle-derived string examples and no-result examples checked by Lean.

### Task 4: Regression and Full-Spec Verification

**Files:**
- Modify if required by findings: files owned by Tasks 2--3
- Record artifacts: `.superpowers/sdd/lean-spectec-print/`

**Interfaces:**
- Consumes: complete implementation and tests from Tasks 1--3.
- Produces: fresh regression results, full-spec metrics, and final comparison against baseline.

- [ ] **Step 1: Run all Lean backend tests**

Run: `cd p4spec && ELAN_HOME=/tmp/p4-spectec-elan.ENxF2N/elan PATH=/tmp/p4-spectec-elan.ENxF2N/elan/bin:$PATH opam exec --switch=spectecx -- dune build @backend-lean`

Expected: PASS.

- [ ] **Step 2: Run SpecTec language regressions**

Run: `cd p4spec && opam exec --switch=spectecx -- dune build @speclang`

Expected: PASS.

- [ ] **Step 3: Translate the full specification and collect metrics**

Run the requested `--keep-going spec` command, save stdout/stderr in the plan workspace, count root diagnostics and translated relations/functions with the baseline-compatible filters, and confirm that no root diagnostic names `print_`.

Expected: root diagnostics do not increase; translated declarations do not decrease; all `print_` root diagnostics disappear.

- [ ] **Step 4: Check the generated Lean file and time it**

Run Lean 4.34.1 with the session-local elan installation and record wall-clock time and error count.

Expected: zero Lean errors.

- [ ] **Step 5: Inspect the final diff and run a fresh whole-change review**

Check for forbidden placeholders, unintended spec/interpreter edits, unhandled print formats, and accidental printer generation outside the closure. Fix any critical or important finding with a RED-to-GREEN regression test, then rerun the full aliases and Lean check.
