# Reified SpecTec to Lean evaluator results

## Outcome

The Lean backend now emits one dependent `SpecTecEval.EvalRulePlan` per
source rule and interprets every relation through the shared
`SpecTecEval.Selected`, `AllFailed`, and `Evaluator` definitions.  The default
relation-local output retains the complete public specification and all 1,104
evaluators.  The generated source is deterministic, the forced backend suite
passes, and the complete generated file compiles with Lean 4.34.1 without
`sorryAx`.

The measured compile improved from 1,357.009 seconds to 947.125 seconds
(-30.20%), but it did **not** meet the design's required ten-minute target or
the five-minute stretch target.  Profiling and an evaluator-free control show
that further progress requires work outside the reified-evaluator boundary;
the remaining dominant costs are the existing SCC-local `InProgram`
declarations, fresh rename/`DecidableEq` definitions, whole-module kernel
checking, and `.olean` serialization.

The implementation result is therefore semantically complete but the original
performance acceptance criterion remains open.

## Implemented representation

`SpecTecEval.EvalRulePlan Input Output Public` stores a dependent `Witness`
together with the rule's input, output, source-ordered premise list,
recoverable premise positions, and public-soundness proof.  A rule succeeds by
choosing a witness and proving a `Prefix`; it fails only through a head
mismatch or a `RuleFailure` at a recoverable position with the complete earlier
prefix.

`SpecTecEval.Selected` interprets an indexed plan list under either ordered or
nondeterministic selection.  Ordered selection advances only through a plan
failure certificate.  `AllFailed` records failure of every plan.
`SpecTecEval.Evaluator` combines the policy, rule plans, and the existing
relation-specific undetermined predicate.  Its shared theorems expose success,
universal rule failure, and timeout certificates without adding determinism.

The generated surface is:

- per source rule: one `...:eval:rule:N:plan` definition;
- per relation: `EvalInput`, `EvalOutput`, `evalSucceeds`, `freshSites`,
  `evalRules`, `evalUndetermined`, `evaluator`, `allRulesFailed`,
  `evalSelected`, `selected_sound`, and `eval`;
- shared once: the plan, selection, failure, evaluation, and evaluator
  definitions and the generic certificate theorems.

The former per-rule `:premises`, `:recoverable`, `:succeeds`, `:failed`, and
`:sound` declarations are absent.  The former per-relation `success_sound`,
`ruleFailure_sound`, and `timeout` wrappers were also removed after the first
complete compile exceeded the target; proofs now call the corresponding
`SpecTecEval.Evaluator` theorem.  The relation `selected_sound` bridge remains
because generated premise proofs use it and an opacity experiment did not
show a meaningful focused benefit.

## Semantic checks

The checked fixtures cover:

- same-pattern premise failure followed by the next ordered rule;
- `otherwise` only after all ordinary rules fail;
- output-search failure quantified over every output;
- multiple successful outputs under nondeterministic selection;
- recoverable failure separated from abort, unsupported, and timeout;
- recursive and negative-cycle undetermined evidence;
- fresh allocation, rollback, nominal alpha, and extern isolation;
- public judgement reconstruction from every successful plan;
- rejection of wrong-rule, wrong-position, abort-as-failure, and
  one-output-as-universal-failure certificates;
- absence of `sorryAx` in the certificate proofs checked by the suite.

Two full `--keep-going` generations and a strict generation produced the same
35,254,485-byte file with SHA-256
`82880c1cf7d5186893e6e4527f197c95bd7d944a6e6a4be22797dd3aefd2c579`.
The `--keep-going` path initially pruned 2,289 valid fresh-dependent
declarations because it treated generated prelude aliases as missing IL
declarations.  `FreshSupply` and `FreshSite` are now recognized as Lean support
names, and a regression requires strict and keep-going output to agree for the
fresh-supply fixture.

A relation with no source rules initially left the plan witness universe
unconstrained.  Empty generated plan lists now pin
`EvalRulePlan.{0, 0, 0}`; nonempty lists retain normal inference.  The focused
checker compiles a polymorphic clause-free relation to guard this case.

## Source measurements

The raw full-source totals use the same input and default relation-local mode
as the supplied baseline.  Category rows use the checked-in lexical classifier
on both saved files.

| Measurement | Baseline | Reified | Change |
|---|---:|---:|---:|
| Total bytes | 38,971,279 | 35,254,485 | -9.54% |
| Total lines | 282,763 | 247,190 | -12.58% |
| Classified evaluator bytes | 10,640,517 | 6,919,315 | -34.97% |
| Classified evaluator lines | 105,941 | 70,271 | -33.67% |
| Evaluator header bytes / lines | 559,425 / 9,936 | 559,425 / 9,936 | unchanged |
| Rule-flow or plan bytes / lines | 6,704,448 / 57,662 | 4,371,400 / 36,514 | -34.80% / -36.68% |
| Selection bytes / lines | 1,566,585 / 18,459 | 1,616,871 / 20,470 | +3.21% / +10.89% |
| Wrapper bytes / lines | 1,810,059 / 19,884 | 371,619 / 3,351 | -79.47% / -83.15% |
| Evaluator relations | 1,104 | 1,104 | unchanged |
| Legacy rule flows | 2,621 | 0 | removed |
| Reified rule plans | 0 | 2,621 | added |

The design brief's hand-recorded baseline classified 10,691,090 evaluator
bytes and 108,435 evaluator lines, including 1,860,632 wrapper bytes and
22,378 wrapper lines.  Re-running the final classifier on the saved baseline
gives the values in the table.  Raw total bytes and lines are identical in both
accounts; the difference is only which common declarations the lexical
categories include.

The focused 64-one-rule default fixture is 221,615 bytes and contains exactly
64 plans after removal of the three relation certificate wrappers.  The
legacy exact-counter size guards remain 215,939 bytes for 64 clauses, 105,455
bytes for 64 guarded prefixes, and 175,818 bytes for 64 straight-line public
functions.

## Generation and compilation measurements

The environment used Lean 4.34.1 on the same checkout and inputs as the
baseline.  GNU `time` was unavailable, so a plan-local Python wrapper recorded
wall time and Linux child `getrusage` user, system, and peak-RSS fields.

| Measurement | Baseline | Reified | Change |
|---|---:|---:|---:|
| Strict generation wall | 9.933 s | 10.368 s | +4.38% |
| Strict generation user / system | not separately recorded | 10.116 / 0.251 s | — |
| Strict generation peak RSS | 588,840 KiB | 542,312 KiB | -7.90% |
| Keep-going generation wall, run 1 | — | 13.848 s | — |
| Keep-going generation wall, run 2 | — | 13.915 s | — |
| Full Lean wall (`-j 2`) | 1,357.009 s | 947.125 s | -30.20% |
| Full Lean CPU | 1,569.157 s | 1,140.676 s | -27.31% |
| Full Lean peak RSS | 34,878,464 KiB | 35,019,220 KiB | +0.40% |
| `.olean` bytes | 691,505,872 | 709,216,952 | +2.56% |

The full compile completed in 15 minutes 47.125 seconds.  It exceeded the
ten-minute requirement by 347.125 seconds and the five-minute stretch target
by 647.125 seconds.  Peak RSS and `.olean` size also did not improve.

A fresh completion-gate compile of the same byte-identical source under the
diagnostic filename `Full-final-1.lean` also exited 0, with 995.291 seconds
wall, 1,198.966 seconds CPU, 35,025,728 KiB peak RSS, and a 709,217,280-byte
`.olean`.  The comparison table retains the `Full.lean` measurement because
that filename and command match the baseline; the repeat records observed
run-to-run and module-name variation rather than selecting the faster result
silently.

## Performance diagnosis

A `--relation-root Expr_eval` representative closure contains 596 rule plans
and 10,934,910 bytes of Lean source.  Its profiled compile took 435.221 seconds
and 17,798,612 KiB peak RSS.  The dominant measured items were:

- 152 seconds in `.olean` serialization;
- 113 seconds in kernel type checking;
- 85.530 seconds type-checking the existing
  `Expr_eval:supply:Semantics.InProgram` declaration;
- large existing fresh rename, `DecidableEq`, and common-expression-sharing
  work.

Only three of the 596 evaluator plans crossed the profiler's 100 ms trace
threshold.  A diagnostic copy with all evaluator declarations removed still
took 414.699 seconds and 16,766,100 KiB, versus 435.221 seconds and 17,798,612
KiB for the original.  Its `.olean` was 326,092,120 bytes versus 348,317,744
bytes.  On this representative closure, all evaluator declarations therefore
accounted for about 20.5 seconds of wall time and 22.2 MB of `.olean` output.

This does not prove a whole-file percentage, but it falsifies the hypothesis
that another evaluator-only wrapper or opacity change can recover the 347
seconds needed for the ten-minute target.  Reaching that target requires a
separate design covering at least one of SCC-local `InProgram` representation,
fresh rename/decidable-equality generation, or generated-module splitting and
serialization.  Those changes were explicit non-goals of this evaluator
refactor and are not bundled into this result.

## Verification commands

The final implementation was checked with:

```sh
opam exec --switch=spectecx -- dune build --force @backend-lean

_build/default/p4spec/lib/lean-skeleton/main.exe --keep-going spec
_build/default/p4spec/lib/lean-skeleton/main.exe --keep-going spec
cmp Full.lean Full-repeat.lean

_build/default/p4spec/lib/lean-skeleton/main.exe spec
cmp Full.lean Full-strict.lean

lean -j 2 -o Full.olean Full.lean
lean -j 2 -o Full-final.olean Full-final-1.lean
git diff --check
```

The forced backend suite exited 0 in 81.598 seconds.  The full Lean compile
and its fresh completion-gate repeat both exited 0.  The completion-gate
compile emitted no diagnostics.  The only full-generation diagnostic was the
existing missing-clause warning for the intentionally clause-free `$sink<T>`
declaration.

## Remaining specialization and obligations

- Relation-specific input/output packaging, public success predicates,
  fresh-site data, one plan per source rule, plan lists, undetermined
  predicates, evaluator values, and the `selected_sound` bridge remain because
  they contain source-specific data or are used by generated proofs.
- External proofs using the removed relation-level success, universal failure,
  or timeout wrappers must use `SpecTecEval.Evaluator` as documented in the
  backend README.
- The ten-minute and five-minute full-compilation targets remain unmet.  A new
  design must broaden scope beyond evaluator commoning before claiming either
  target.
- The higher `.olean` size and essentially unchanged peak RSS remain open
  costs of the dependent plan representation even though wall time and source
  size improved substantially.
- Empty plan lists assume generated SpecTec values live in universe level 0.
  A future higher-universe generated relation must generalize that annotation.
- The pre-existing nominal fresh model still does not connect dynamic supply
  threading and protected-name extraction to every full generated execution;
  this refactor preserves rather than resolves that separate limitation.

Final implementation commit: `pending`.
