# Shared typed plan compaction

- Worktree: `/tmp/p4-spectec-reified-spec-diagnosis`
- Branch: `codex/reified-spec-diagnosis`
- Baseline: `3deed878`
- Implementation: `1297d0e4`, `403a8b72`, `201562b6`

No tracked changes preceded this work. The user-owned untracked
`docs/diagnostics/` directory was not changed or staged.

## Structure

A source rule now has one dependent `SpecTecPlan.Alternative`: its source
index, recoverable positions and typed body. Lexical bind nodes introduce
intermediate values at their original source positions. The same body supplies:

- WFS rules through `Plan.compile` and SCC-local `ProgramOf Allowed ()`,
  interpreted by the existing public `SpecTecWFS.Holds`, `Fails` and
  `Undetermined` relations;
- ordered evaluator premises through `Plan.premises true`, with one shared
  `Alternative.toEvalRule` proof and `SpecTecPlan.evaluator` interpreter;
- public typed inversion through `ProgramOf.holds_cases` and `Cases`.

There are no generated per-rule `EvalRulePlan` definitions, duplicated evaluator
premise lists or `publicSound` bodies. Relation-specific inversion disjunctions
and `RuleCasesShape` proofs are gone. Public inversion delegates once to Core,
returning the allowed alternative, its dependent witness, head equality and
source-order premises. The optional common proof-support tactics traverse
`Allowed` wrapper trees and unpack witnesses; no relation-specific tactics are
generated for this operation.

Prior-SCC plans reference shared external signatures carrying both public
success and the stronger ordered selection predicate with its soundness proof.
This creates a real dependency on earlier evaluators, so SCC semantics and
evaluators are now emitted together in dependency order. The old evaluator
module names remain as import facades. All of these files are included below.

## Complete generated source

| Category | Before LoC | After LoC | Before bytes | After bytes |
|---|---:|---:|---:|---:|
| Core + Support | 22,214 | 22,601 | 1,323,252 | 1,342,986 |
| SCC + evaluators, including facades | 336,606 | 329,687 | 69,033,918 | 51,759,554 |
| Public inversion | 90,432 | 36,354 | 16,632,563 | 2,429,953 |
| Entrypoints | 9 | 9 | 210 | 210 |
| **All generated modules** | **449,261** | **388,651** | **86,989,943** | **55,532,703** |

The original SpecTec source remains 33,473 lines. Generated module count is
293→275. Total LoC falls 13.49%; bytes fall 36.16%. These are physical source
counts including blank lines, Core, support, all evaluators and all inversion
wrappers. They are not estimates of compiler performance.

Both outputs contain exactly 5,210 public relations, 1,104 evaluator APIs and
5,210 public inversion wrappers. All public relation argument signatures and
all these API names compare equal. A second comparison exports the actual Lean
kernel types of all 10,420 success/failure predicates, retaining implicit
instance arguments and universe parameters. They match exactly after erasing
binder names and metadata. Two independent final whole-P4 generations
produce byte-identical module files. The source comparison records each file's
SHA256 and scans for proof holes and axiom declarations.

`SpecTecProof.lean` is optional hand-written proof support, outside the original
293-module baseline. It grows from 261 to 314 lines (+53); it is reported
separately rather than used to hide generated semantic/evaluator code.

## The two-line `$empty_typeFrame` relation

Counts use the same complete-spec component 608 boundaries as the baseline;
LoC includes the two phase marker lines. Bytes below exclude those markers in
both versions. Its external signature is included even though it is used by
later relations.

| Phase | Before LoC | After LoC | Before bytes | After bytes |
|---|---:|---:|---:|---:|
| SCC semantics / rule / public APIs | 35 | 40 | 2,694 | 2,829 |
| Evaluator / external signature | 47 | 32 | 2,743 | 2,020 |
| Typed inversion | 13 | 6 | 743 | 270 |
| **Combined** | **95** | **78** | **6,180** | **5,119** |

The required rule data is one output type, a prior-SCC `$empty_map` call, a
head constructor, rule index 0 and an empty recoverable-position list. The
new signature and `Allowed` image add five semantic lines. Removing the
separate evaluator body and inversion proof saves more than this addition.
The original introductory theorem, public success/failure relations,
certificate API and evaluator outcome API are retained.

### Exact generated rule / inversion excerpts

**Before**

```lean
def rule_0_plan : SpecTecPlan.Alternative Atom Unit :=
  { sourceIndex := 0, recoverable := [], body := (SpecTecPlan.Plan.at 0 (SpecTecPlan.Plan.externalCall ({ Input := _root_.Unit, Output := (map id varTypeIR), inputPositions := [], policy := .ordered, boundary := .priorSCC, holds := fun () «plan:arg:0» => (@«$empty_map» id varTypeIR «plan:arg:0») } : SpecTecPlan.ExternalSignature) (fun () => ()) (SpecTecPlan.Plan.ret (fun ⟨(), «eval:0»⟩ => (@Atom.«$empty_typeFrame» «eval:0»))))) }

inductive InProgram : SpecTecWFS.Rule Atom → Prop where
  | rule_0 («eval:0» : (map id varTypeIR)) : InProgram ((rule_0_plan).body.compile () ⟨«eval:0», ()⟩)

theorem «$empty_typeFrame».ruleCases (arg0 : typeFrame) (proof : («$empty_typeFrame» arg0)) :
    let __plan_expected_atom : «$empty_typeFrame:Semantics».Atom := (@«$empty_typeFrame:Semantics».Atom.«$empty_typeFrame» arg0)
    (∃ («eval:0» : (map id varTypeIR)), ((@«$empty_typeFrame:Semantics».Atom.«$empty_typeFrame» «eval:0») = __plan_expected_atom) ∧ ((@«$empty_map» id varTypeIR «eval:0»)) ∧ (True)) := by
  obtain ⟨__plan_rule, __plan_member, __plan_head_eq, __plan_side, __plan_positive, __plan_negative⟩ :=
    SpecTecWFS.Holds.cases proof
  cases __plan_member
  case rule_0 «eval:0» =>
    exact ⟨«eval:0», (by exact __plan_head_eq), __plan_side.1, trivial⟩
  all_goals cases __plan_head_eq
```

**After**

```lean
def rule_0_plan : SpecTecPlan.Alternative Atom Unit :=
  { sourceIndex := 0, recoverable := [], body := (SpecTecPlan.Plan.at 0 (SpecTecPlan.Plan.bindExternal (@«$empty_map».externalSignature id varTypeIR) (fun () => ()) (fun «eval:0» => (SpecTecPlan.Plan.ret (fun () => (@Atom.«$empty_typeFrame» «eval:0»)))))) }

inductive Allowed : SpecTecPlan.Alternative Atom Unit → Prop where
  | rule_0 : Allowed (rule_0_plan)

abbrev InProgram : SpecTecWFS.Program Atom := SpecTecPlan.ProgramOf Allowed ()

abbrev InProgram.rule_0 := SpecTecPlan.ProgramOf.compiled (allowed := Allowed) (entry := ()) (Allowed.rule_0 )

theorem «$empty_typeFrame».ruleCases (arg0 : typeFrame) (proof : («$empty_typeFrame» arg0)) : SpecTecPlan.Cases «$empty_typeFrame:Semantics».Allowed () (@«$empty_typeFrame:Semantics».Atom.«$empty_typeFrame» arg0) :=
  SpecTecPlan.ProgramOf.holds_cases proof
```

The complete phase excerpts, including evaluator code, are in
`../evidence/2026-10-07-shared-plan/empty-typeFrame.md`.

## Semantic preservation and proof scope

- `ProgramOf.compiled_iff` proves both directions of rule membership, quantified
  over alternatives and typed witnesses. `Plan.premises_iff` relates the ordered
  premise list to WFS side, positive and negative premises for every plan node.
- `Plan.eval_premises_sound` changes selected prior-SCC successes into public
  WFS successes. `Alternative.toEvalRule` uses this and `Plan.holds_rule` for
  the common evaluator soundness proof. Same-SCC positive/negative calls keep
  their WFS `Holds`/`Fails` interpretation, as before.
- The existing choice interpreter still preserves source rule order,
  recoverable positions, universal output-search failure, abort, unsupported,
  timeout and SCC-local undetermined outcomes. A public external success alone
  cannot bypass ordered selection; the negative fixture demonstrates this.
- Named callbacks remain typed local dispatch alternatives. External callbacks
  remain explicit predicate boundaries. Their compiled side is `f input output
  ∧ True`, propositionally equivalent to the earlier side `f input output`.
- Numeric fresh allocation still uses the existing `SpecTecFresh.Allocates`
  predicate and supply/record constraints. Missing records, wrong intermediate
  values, ordinary text masquerading as fresh and malformed certificates are
  rejected by the fixtures. Existing rollback, alpha, alias and protected-input
  tests pass without changing their goal propositions.
- Compatibility modes are tested separately and retain their existing semantics.
  No special `Program_ok` code path was added.

This is a sound relational evaluator, not a completeness proof for arbitrary
recursive/negative WFS programs. Opaque side premises still require evidence;
the implementation does not turn arbitrary propositions or callbacks into
executable decision procedures. Internal APIs intentionally change:
`InProgram.rule_N` takes a dependent witness; `ruleCases` returns generic
`Cases`; old generated `...:eval:rule:N:plan` names are replaced by indexed
access to `Relation.evalRules`. Public relation names/signatures remain fixed.

The Core fixture checks that `premises_iff`, `eval_premises_sound`,
`Alternative.toEvalRule` and `ProgramOf.holds_cases` use exactly `[propext]`.
The audit additionally checks every theorem in all `SpecTec*` namespace
families, including common Core. The final-source audit checks 63,222 theorems and
permits only `[propext, Classical.choice, Quot.sound]`. Final-source audit
measurements and case logs are recorded below.

## Compiler measurements

Every generated module compiles successfully in both clean runs.

| Metric | Baseline | Final | Reduction |
|---|---:|---:|---:|
| Fresh / reused modules | 293 / 0 | 275 / 0 | — |
| Clean wall seconds | 3,219.278 | 1,488.264 | 53.77% |
| User CPU seconds | 4,351.938 | 1,777.987 | 59.14% |
| System CPU seconds | 44.013 | 35.657 | 18.99% |
| Peak Lean RSS KiB | 4,449,480 | 3,758,696 | 15.53% |
| Total generated `.olean` bytes | 2,405,106,024 | 1,081,823,296 | 55.02% |
| Unchanged incremental wall seconds | 0.116 | 0.076 | — |
| Incremental fresh / reused modules | 0 / 293 | 0 / 275 | — |

The new fixed Core cost is included: Core alone grows from 1.498 to 9.144
seconds and from 3,894,760 to 6,107,752 olean bytes. Support has byte-identical
source and the same 135,257,808-byte olean, but took 144.082 versus 160.329
seconds, illustrating timing variation even under the same settings.

| Category | Before seconds | After seconds | Before olean bytes | After olean bytes |
|---|---:|---:|---:|---:|
| Core + Support | 145.580 | 169.472 | 139,152,568 | 141,365,560 |
| SCC + evaluators, including facades | 2,119.796 | 1,304.585 | 1,308,642,024 | 927,917,120 |
| Public inversion | 952.209 | 12.540 | 957,307,224 | 12,536,408 |
| Entrypoints | 1.121 | 1.236 | 4,208 | 4,208 |

Category times sum individual Lean process wall times; the total above also
includes driver bookkeeping. No generated proof or evaluator category is omitted.

Both versions use Lean 4.34.1 (commit
`5045d0056413266e57c625dcd7c365b10e377c52`), serial module order, `lean -j 2`,
the installed compiler binary directly (bypassing `elan`), CPU affinity 0,1
and the default 2,000,000-byte split limit. Each clean run
starts with zero generated oleans; the installed Lean standard library is
shared. The new clean run starts after the baseline clean run completes. An initial
`elan`-based run was discarded when its launcher waited on network sockets
without executing Lean; its elapsed time is not a compiler benchmark.
Module imports determine compilation order. Reported driver wall time covers
the compilation loop and its bookkeeping, excluding process startup, initial
source hashing and the compiler-version query. The incremental run is explicitly
an unchanged/no-op build, not a representative edited-SCC rebuild. With zero
Lean launches its compiler CPU is zero and compiler RSS is not applicable.
RSS is the maximum serial Lean
process peak from `wait4`, not a sum; all generated oleans are counted.

The host is shared with development checks on other CPUs; this is one paired
run, not a statistical benchmark or a machine-isolated performance claim.
The separate candidate preflight uses CPUs 2,3 and reuses already verified
modules after the shadow fix. Its time is excluded from clean comparisons.
The earlier 1,585.9 seconds combined 84 reused modules with 190 newly compiled
modules; it is not used as a clean baseline here.

Generation, measured separately and sequentially on CPUs 2,3 with the same CLI
and source paths (all module hashes match the compiler inputs):

| Metric | Baseline | Final |
|---|---:|---:|
| Wall seconds | 37.146 | 31.225 |
| User CPU seconds | 36.371 | 30.698 |
| System CPU seconds | 0.774 | 0.523 |
| Peak RSS KiB | 987,604 | 697,192 |

## Seven unchanged case goals

The case proof sources (`Case*.lean`) and exact goals (`RandomCases.lean`)
are preserved locally but excluded from Git. The measurement script expects
these ignored files beside it; their recorded hashes identify the replay inputs.

The exact existing `RandomCases.lean` is retained with SHA256
`274cc8745ef6efd922a857f62a0095feead17519fdd22fb5a943c941dfa46644`.
The accepted cases keep both existence of an alpha-equivalent output and
universal alpha-equivalence for every public output; rejection goals remain
negated public existence. No goal is weakened to evaluator success, an oracle
answer, a bounded search result or mere syntactic well-formedness.

| Case | Exact goal | Goal definition compiles | Theorem proved |
|---|---|---|---|
| 589 | Acceptance: existence + universal alpha-equivalence | Yes | No |
| 196 | Rejection: no public output | Yes | No |
| 616 | Acceptance: existence + universal alpha-equivalence | Yes | No |
| 487 | Rejection: no public output | Yes | Yes |
| 1491 | Acceptance: existence + universal alpha-equivalence | Yes | No |
| 1380 | Acceptance: existence + universal alpha-equivalence | Yes | No |
| 454 | Rejection: no public output | Yes | Yes |

Five goal definitions remain unproved. Their successful compilation is not
reported as proof success. The two rejection proofs use the same original
propositions with adapted internal inversion syntax. Case 487 normalizes only
new premises and substitutes explicit equality evidence; an unrestricted
`subst_vars` search was too costly in the dependent context. This is a proof
search change, with every resulting term checked by Lean.

| Additional module | Wall seconds | Peak RSS KiB | Olean bytes |
|---|---:|---:|---:|
| SpecTecProof | 1.415 | 1,677,920 | 1,449,048 |
| RandomCases | 2.184 | 1,417,136 | 6,838,936 |
| AxiomAudit | 1.646 | 2,399,260 | 2,648 |
| Case0454 | 94.468 | 5,963,904 | 308,611,672 |
| Case0487 | 365.623 | 11,199,200 | 305,336,216 |
| CaseAxioms | 0.818 | 2,367,752 | 2,520 |

These are additional fresh Lean compilations against the final modules on
CPUs 4,5, with the same compiler and `-j 2`. Both rejection theorems have
exactly `[propext, Classical.choice, Quot.sound]`; the separate importing audit
rejects every other dependency. All seven goal definitions compile together in
2.184 seconds, which does not prove the five open goals.

The additional sources total 825 lines / 617,146 bytes,
including the unchanged original goals and optional 314-line proof helper.
Their oleans total 622,241,040 bytes and compilation takes 466.153
seconds. Including them with the generated modules gives
**1,954.417 measured seconds, 1,704,064,336 olean bytes,
and 11,199,200 KiB peak RSS**. This excludes measurement-tool and
backend test-runner overhead. A matching baseline measurement for these manual
proofs was not performed, so no comparative speed or memory claim is made for
them. **Case 487's 11,199,200 KiB peak and the two large proof oleans remain a
significant limitation.** The generated-module memory reduction must not be
read as a reduction of this combined validation peak.

The complete generated theorem-family axiom audit checks 63,222 theorems;
the corresponding baseline audit checks 62,201. Both unions are exactly
`[propext, Classical.choice, Quot.sound]`. Source scans and successful case
compilation contain no proof holes or newly declared axioms.


## Reproduction and remaining limits

```sh
LEAN_COMPILER=/root/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean
export PATH="$(dirname "$LEAN_COMPILER"):$PATH"
opam exec --switch=spectecx -- dune build @p4spec/test/backend-lean/backend-lean
_build/default/p4spec/lib/lean-skeleton/main.exe --emit-modules /tmp/new-p4 spec
python3 p4spec/test/backend-lean/measure_modules.py /tmp/new-p4 \
  --mode clean --cpus 0,1 --lean "$LEAN_COMPILER" --report /tmp/new-p4-clean.json
python3 p4spec/test/backend-lean/measure_modules.py /tmp/new-p4 \
  --mode incremental --cpus 0,1 --lean "$LEAN_COMPILER" --report /tmp/new-p4-incremental.json
python3 p4spec/test/backend-lean/compare_module_sources.py BEFORE AFTER \
  --report /tmp/source-comparison.json
python3 docs/superpowers/evidence/2026-10-07-shared-plan/measure_proofs.py \
  --generated /tmp/new-p4 --support p4spec/lib/lean-skeleton/SpecTecProof.lean \
  --output /tmp/new-proofs --lean "$LEAN_COMPILER" --cpus 4,5
P4_PUBLIC_TYPES_OUTPUT=/tmp/public-types.json LEAN_PATH=/tmp/new-p4 \
  "$LEAN_COMPILER" -j 2 docs/superpowers/evidence/2026-10-07-shared-plan/ExportPublicTypes.lean
```

The full backend-lean alias passes, including explicit compatibility modes.
The final `dune build --force -j 4 @p4spec/test/backend-lean/backend-lean`
exited 0 with the direct Lean toolchain on PATH; its log is retained.
All 293 baseline and 275 final modules compile from zero generated oleans.
Complete per-module measurements, source manifests, kernel signature checks,
case sources and the test log are in
[`../evidence/2026-10-07-shared-plan/`](../evidence/2026-10-07-shared-plan/).
Implementation commits are `1297d0e4`, `403a8b72`, and `201562b6`, on
`codex/reified-spec-diagnosis`. The worktree and local branch are retained.

Remaining source cost includes original public introduction theorem types,
polymorphic atom/signature data, source rule alternatives and compatibility
APIs. This compiler refactoring is not a verified proof of the entire OCaml
translator against the SpecTec metatheory; the claimed generic Lean laws,
fixtures, coverage checks and full compilation delimit the evidence.

Independent final review of `3deed878..201562b6` found no Critical or Important
code issues. One Minor follow-up is deferred: `module_writer.ml` should
recognize `Allowed` declarations and aliases as additional safe split boundaries.
Today their 191–383 KB membership sections remain attached to the final plan
block; the default 2 MB split and full P4 compilation are unaffected, but
smaller split limits are less precise. No semantic rule or proof is omitted.
