# Numeric fresh and typed plan implementation record

## Verified milestones

1. `freshText n` restricts the default-mode allocation relation, public
   `Allocated`/`AllocatedAt` witnesses, and singleton helper. `FreshId`
   site/path/occurrence, nested supply, protected-name checks, derived-text
   collision records, failure supply handling, and both legacy modes remain.
   The numeric suffix is an independent relational choice recorded in
   `Supply.assigned`; it is not the occurrence or a global counter.
2. `SpecTecPlan.Plan` defines typed sequential `choose`, call, negative,
   guard, external, and fresh steps. `Plan.Witness` stores the chosen values;
   `Plan.compile` makes a WFS rule; `Program.compiled_iff` describes membership
   in both directions; `Program.holds_cases` opens a WFS success into a plan
   alternative, witness, and typed rule fields. The small Lean fixture checks
   call-result binding, premature use rejection, local negative atoms,
   external side propositions, numeric fresh allocation, WFS introduction,
   and inversion. Generated SCC rule membership now compiles this plan instead
   of copying a separate WFS record into each constructor. Scoped signatures
   carry the rule environment for local callback references. Generated rule
   introduction proofs unfold the plan and give polymorphic type arguments.
3. Internal calls with one variable output use `call` or `callScoped` at their
   source premise, so the result enters the typed environment only for later
   steps. A fresh allocation whose output and next supply are source binders
   uses `freshBound` at that premise. The generated `$invoke` and
   `$fresh_typeId:supply` fixtures verify those shapes and compile in Lean.
   Staging is skipped when an output appears in an earlier premise or in its
   own input. The WFS plan and evaluator now share one recoverable-position
   calculation, including the `regular` fallback rule.
4. `SuccessCertificate` stores the chosen WFS rule with its plan witness,
   proof-backed opaque side and negative premises, and untrusted child
   certificates. `checkSuccess` and `checkSuccessWith` validate the complete
   positive-child list, reject missing or wrong children, and return the rule
   head only after validation. Both have generic soundness proofs by fuel
   induction and WFS rule introduction. The comparison-oracle version only
   trusts a Boolean `true` when accompanied by an equality soundness proof;
   opaque callback atoms therefore need no global `DecidableEq` instance.
   Every generated public relation, including `Program_ok`, gets a uniform
   `checkedSuccess` theorem. A concrete certificate proves `Decl_ok` in the
   relation-local fixture.
5. Internal calls with several variable outputs now bind their whole output
   tuple at the source premise. `Plan.splitPair` flattens each pair through a
   typed `reframe` step, making every component available only to later
   premises. A minimal recursive fresh fixture emits this step and compiles
   with Lean. A direct indexed `splitPair` constructor prevented Lean from
   reducing the dependent `Plan.Witness` type, so the generic environment
   conversion is necessary.
6. `--emit-modules DIR` writes a common Core, generated support, batches of
   dependency-ordered SCC semantics and evaluators, an aggregate import, and
   case module. The relation-local fixture verifies deterministic output,
   acyclic imports, and Lean compilation of each module. The printer still
   constructs the monolithic source in memory before splitting it; generation
   RSS has not yet improved.
7. Previous-SCC relation calls with output binders now use `externalCall` at
   their source premise; known outputs use `externalKnown`, and negative calls
   use `externalNegative`. The external signature carries the public relation,
   declared input/output types and mode, and prior-SCC boundary. The minimal
   recursive fresh fixture generates all three forms plus `splitPair` and
   compiles in Lean; `relation-local-test` and the full backend alias passed.
8. In the relation-local fixture, `Decl_ok.InProgram` is proved equivalent in
   both directions to the union of its two compiled rule-plan images. The
   theorem and its axiom output are checked by Lean. This direct fixture proof
   has not yet been generated for every relation.
9. SCCs with more than 32 rule-membership constructors now use the existing
   bounded membership tree and retain `InProgram.rule_N` aliases. Their
   `cases_in_program_N` tactics have SCC-specific names. A synthetic 40-rule
   relation compiles its generated introduction theorems and uses the tactic
   to split a WFS membership proof. The giant P4 SCC formerly had 1,298
   constructors in one inductive; its single-inductive fragment was stopped
   after 7.7 minutes and over 25 GB RSS without completing.
10. Every generated public relation has a `ruleCases` theorem exposing typed
    source-rule binders and premises directly. In a large SCC, bounded leaf
    and wrapper lemmas build one `RuleCasesShape.sound` theorem; each public
    theorem reuses that shape and rewrites only the selected head.
    Inversion proofs are in `SpecTecInversionNNNN` modules imported by
    `SpecTecProofs`, outside the semantic/evaluator import chain. A 40-rule
    fixture with an extern type checks the hidden instance pattern, and the
    `Nat_ok` fixture proves a rejection using the new theorem.

## Commands and observations

- Focused aliases: `fresh-nominal-test`, `fresh-supply-test`,
  `relation-local-test`, `ordered-eval-test`, and `local-proof-support-test`
  passed after each related milestone.
- Full alias: `dune build @p4spec/test/backend-lean/backend-lean` passed after
  initializing this worktree's pinned `p4c` submodule. The first attempt
  failed solely because that submodule was absent here; the original checkout
  had it initialized.
- `#print axioms` for `Allocates.numeric` and `Allocated.numeric` returned
  `[propext]`. The plan membership and inversion theorems were checked for
  `sorryAx` in the fixture; no `sorry`, `admit`, or new axiom was added.
- The backend alias passed after plan-backed SCC membership. The ordered
  fixture's non-Core generated source grew to 87,539 bytes, so its measured
  budget changed from 87,000 to 90,000 bytes. The aggregate ordered output is
  96,405 bytes; this is source growth, not a performance improvement.
- With staged call binding, full-spec generation succeeded in 25.016 s with
  797,012 KiB child peak RSS and 60,255,238 source bytes. This is much larger
  than the interim 35 MB output and precedes the fresh-binding change.
- After staged fresh binding and the lower-cost introduction proof, a new
  full-spec generation succeeded in 24.945 s, 782,764 KiB peak RSS, and
  61,073,741 source bytes. The earlier full Lean attempt was stopped after
  the first failure: `simp_all` exceeded recursion depth in
  `$ends_with:regular`. A focused Lean compile of that SCC passed with
  `dsimp` followed by the source-premise proof; that run was superseded by the
  completed modular build below. The backend alias passed after this change.
- The certificate checker fixture verifies wrong/missing child rejection,
  target mismatch, public `Decl_ok` soundness, and axiom output without
  `sorryAx`. The ordered fixture is now 109,496 bytes total: 16,660 bytes of
  common Plan/checker Core and 92,836 bytes elsewhere. The fixture size bounds
  were updated to 18,000 and 95,000 bytes respectively to record this growth.
  The backend alias passed after this change.
- After modular output and multi-output binding, `relation-local-test` and
  the entire `backend-lean` alias passed. The new multi-output fixture checks
  that generated `splitPair` code compiles. The larger rollback fixture's
  default translation has an unrelated free generic type `X` in protected
  name generation, so its local output was not used as a Lean compile check.
- The previous-SCC Plan change raised the ordered fixture's non-Core source
  from the prior 92,836 bytes to 95,201 bytes. Its measured limit is now
  96,000 bytes; the common core is 17,190 bytes and retains its 18,000-byte
  limit. This is source growth, not a measured speed improvement.
- Modular full-P4 generation before the multi-output change produced 252 Lean
  modules in 26.155 s with 824,104 KiB child peak RSS, 65,318,464 total
  source bytes, and a 10,758,727-byte largest module. Its Lean module build
  was stopped at the unsplit giant SCC; these numbers are not proof or build
  success.
- The latest previous-SCC build with a 2 MB batching target generated 260
  modules in 27.383 s, used 851,016 KiB child peak RSS, and emitted
  68,254,258 source bytes. The largest module is still 10,786,562 bytes:
  `Expr_eval:supply` is one SCC and cannot be split by whole-SCC batching.
  The earlier full module run was stopped after this giant batch ran more than
  14 minutes and consumed over 38 GB RSS; that run provides no full-build
  success measurement. The latest whole-spec Lean build is in progress.
- Internal splitting of a larger-than-budget SCC now emits declaration-order
  `SpecTecPart` imports before its public SCC module. A forced 10 KB limit on
  the relation-local fixture generated two fragments; all 16 output modules
  compiled in Lean. On full P4, this emits 273 modules including 13 fragments
  in 27.784 s with 848,224 KiB generator peak RSS and 68,257,500 source
  bytes. The largest file is 2,001,976 bytes. Full Lean compilation remains
  outstanding; smaller files alone do not establish a build-time improvement.
- A second full-P4 generation with identical options took 27.158 s,
  843,792 KiB child peak RSS, and produced the same 273 module files byte for
  byte. The latest full backend alias passed after this change. In the active
  fragment build, the first oversized SCC's three parts compiled in 33.629,
  130.066, and 54.226 s with an observed cumulative maximum of 7,616,660 KiB
  RSS; later modules and the aggregate remain pending. The single-inductive
  version of the last giant SCC was stopped before completion.
- With hierarchical SCC membership and distinct tactic names, full-P4
  generation took 26.391 s, used 862,040 KiB child peak RSS, and emitted
  274 modules totaling 70,357,352 bytes. The largest module remains
  2,001,976 bytes. All 274 compiled, producing 1,447,797,392 `.olean` bytes.
  The source has 358,828 LoC. Build records include 84 reused modules and
  190 fresh modules compiled in two stages: 1,529.702 + 56.224 = 1,585.926 s
  of measured module wall time. A stalled Lean launcher was terminated after
  246.011 s between stages; this is not a clean-build timing. The first stage
  observed a 4,446,584 KiB cumulative child RSS peak. The former giant SCC's
  final fragment compiled in 104.214 s with the bounded representation.
- Full-P4 inversion generation with shared SCC shape proofs took 27.228 s
  and 968,168 KiB peak child RSS. It emits 18 inversion modules containing
  89,517 LoC and 16,548,792 bytes for 5,210 public `ruleCases` theorems and
  21 shared SCC shape theorems. With `SpecTecProofs`, the full generated output
  is 293 Lean files, 448,346 LoC and 86,906,172 source bytes. All 274
  semantic/evaluator files are byte-identical to the completed build above.
  This intermediate inversion build reused 9 modules and freshly compiled 10
  in 700.401 s of measured module wall time, peaking at 13,617,808 KiB RSS.
- Bounded leaf proofs and a semantic-only first inversion import regenerated
  P4 in 27.674 s with 989,788 KiB peak child RSS. The semantic/evaluator
  files remain byte-identical. The 18 inversion modules have 90,432 LoC and
  16,632,563 bytes; all 293 generated files have 449,261 LoC and 86,989,943
  bytes. The 981-case `Type_ok` proof batch dropped from 171.6 s and
  7,440,540 KiB peak RSS to 52.662 s and 4,134,620 KiB. All 19 proof modules
  then compiled from scratch in 378.860 s, with a 7,125,412 KiB peak RSS and
  957,307,224 `.olean` bytes for the 18 inversion modules. In the same tail
  module range (9–18), the intermediate version took 700.401 s versus
  262.451 s for bounded proofs. The 1,331-case `Expr_eval` batch fell from
  436.623 s and 13,617,808 KiB to 126.275 s and 7,125,412 KiB. The final
  P4 regeneration after the type-shadow fix was byte-identical in all 293
  modules. The full `backend-lean` alias passed after adjusting only its
  evaluator-source budgets to exclude separate inversion proof source.
- `#print axioms` on `Program_ok.ruleCases`, `Program_ok.checkedSuccess`, and
  the largest SCC's `RuleCasesShape.sound` reported only `propext`,
  `Classical.choice`, and `Quot.sound`; there was no `sorryAx`.
- The unchanged `RandomCases.lean` source for all seven requested goal
  propositions compiled against the final modules in 2.070 s with a
  1,691,568 KiB child RSS peak. This validates goal elaboration, not their
  proofs. The old `Case0454` proof fails because its positional inversion
  tactic expects the former WFS constructor fields. The old `Case0487` proof
  was stopped after 676.322 s without an `.olean`; no new exact case theorem
  is claimed.
- On a representative near-1 MB inversion batch, repeating SCC membership
  elimination in each relation took 146.145 s and 3,393,020 KiB observed
  peak RSS. The shared shape version took 26.215 s and 2,434,104 KiB on the
  same Lean toolchain and semantic imports. The final bounded batch took
  12.6 s and 2,278,196 KiB. These are single runs of changed proof source,
  not a clean whole-build speedup estimate.
- An interim full-spec generation before the latest plan compiler refactor
  succeeded: 10.120 s wall, 521,600 KiB peak child RSS, 35,260,654 source
  bytes. The prior reified baseline reported 10.368 s, 542,312 KiB, and
  35,254,485 bytes. This is a single run with a different source and gives
  no defensible performance improvement estimate. That monolithic run gives
  no Lean build or case-proof measurement.

## Remaining required work

- Replace the evaluator's separate `EvalRulePlan` rule-body generation with
  interpretation of the SCC Plan. Some guards and calls whose outputs are
  complex patterns still use initially chosen source binders; correct these
  before claiming a fully sequential shared representation or checker support.
- Add executable checks or proof-backed constructors for source rule identity,
  intermediate call values, and fresh records beyond the current
  proof-carrying side/member fields; give an integrated example with nested
  generated relations. Completeness remains limited to finite certificates
  and must not be asserted for arbitrary negative or recursive WFS.
- Prove membership equivalence for the replacement WFS representation, beyond
  the direct small-fixture Plan image proof.
- Measure an independent clean full-P4 build; the completed 274-module run
  reused 84 modules and was interrupted once by a stalled launcher.
- Re-run all seven requested exact case goals without weakening accepted
  universal-alpha conditions; collect the specified search/build/RSS/size
  and retry metrics with ready-signal watcher discipline.
