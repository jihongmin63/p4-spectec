# Numeric Fresh Spelling and Typed Rule Plans Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:executing-plans to implement this plan task by task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Restrict default fresh spellings and generate WFS semantics, success checking, and inversion from one typed rule plan in split modules.

**Architecture:** Keep `FreshId` and supply behavior while recording an independent numeric spelling. Replace duplicate rule bodies with typed telescopes interpreted by generic Core definitions. Emit SCCs in dependency order and put evaluators above semantics in the import graph.

**Tech Stack:** OCaml Dune generator, Lean 4 WFS proofs, Python fixture harnesses.

**Spec:** `docs/superpowers/specs/2026-10-07-typed-rule-plan-fresh-design.md`

## Global Constraints

- Preserve exact-counter and rollback compatibility modes and current failure supply policy.
- Keep public relation names and signatures where possible; treat `Program_ok` uniformly.
- Preserve source alternative and premise order, negation, callback boundaries, and recoverable failure positions.
- Do not weaken accepted universal-alpha goals or rejection goals.
- No `sorry`, `admit`, `sorryAx`, or new axioms.
- Preserve pre-existing untracked diagnostics and user files.

## Review Focus

- A protected `FRESH__0` forces a different numeric suffix without changing `FreshId`.
- A derived nonnumeric string still blocks a later colliding allocation without itself becoming an allocated fresh spelling.
- A failed nested call follows the existing supply policy and does not become a successful certificate.
- A same-SCC negative call remains WFS failure, not Boolean negation of a guessed result.
- A forged subcertificate cannot make the parent checker accept.

---

### Task 1: Numeric fresh spelling

**Files:** Modify `p4spec/lib/lean-skeleton/fresh_nominal.ml`; test `p4spec/test/backend-lean/fresh-nominal-proof.lean`, `fresh-supply-proof.lean`, and their check scripts.

**Interfaces:** `freshText : Nat → String`; `Supply.assigned : List (FreshId × Nat)`; `Allocates` requires numeric spelling; `Rendering` agrees with assigned numbers; `allocatedAt_of_text` takes a number.

- [x] Write Lean negative and positive fixtures that fail under arbitrary spelling, plus ID/collision/nested-supply fixtures.
- [x] Run the focused Dune aliases and confirm the expected failure.
- [x] Implement the smallest coherent change across all fresh entry points and evaluator premises.
- [x] Run focused aliases and compatibility fixtures; check theorem axioms.
- [x] Commit only the verified Task 1 files.

### Task 2: Core typed plan and WFS interpretation

**Files:** Modify `ordered_semantics.ml`, `wfs_backend.ml`, `printer.ml`; create a focused plan fixture and checker script.

**Interfaces:** typed relation tag, typed step telescope, rule interpretation, image-based `InProgram`, and bidirectional membership lemmas.

- [ ] Add failing fixture for unbound values and old/new rule membership.
- [ ] Implement the generic telescope and WFS interpretation without a public-soundness field.
- [ ] Generate one rule plan per source rule and derive WFS membership from it.
- [ ] Verify local, recursive, negative, ordered, and callback fixtures; commit.

### Task 3: Success certificates and inversion

**Files:** Modify Core and printer modules; add certificate and rejection-proof fixtures.

**Interfaces:** certificate with rule choice, bound values, checked subcalls and fresh records; `checkSuccess` and its public soundness; generated public rule cases theorem.

- [ ] Add fixtures rejecting wrong rule, intermediate value, child certificate, and fresh record.
- [ ] Implement checker and generic soundness by induction, requiring evidence at opaque boundaries.
- [ ] Generate typed public inversion and write one rejection proof without positional projections.
- [ ] Verify exact theorem and axiom sets; commit.

### Task 4: Module graph and aggregate output

**Files:** Modify `pipeline.ml`, `printer.ml`, `main.ml`, and fixture harnesses; add generated module writer if needed.

**Interfaces:** Core, support, dependency-ordered SCC, evaluator, case, proof, and aggregate imports.

- [ ] Add failing deterministic-output and acyclic-import fixture.
- [ ] Emit split modules from the checked SCC graph and one aggregate entry that imports all evaluators.
- [ ] Build clean and incremental full P4 output; commit.

### Task 5: Cases and measured comparison

**Files:** Add case proofs/measurements and update backend documentation; preserve existing oracle and logs.

**Interfaces:** unchanged case propositions and fresh-specific new regression propositions.

- [ ] Run cases 589, 196, 616, 487, 1491, 1380, 454 with ready-signal watcher and isolated candidates.
- [ ] Check exact proof targets, axioms, process cleanup, and all required time/size/RSS counters.
- [ ] Run backend suite, document the actual improvements and constraints, and commit verified files.
