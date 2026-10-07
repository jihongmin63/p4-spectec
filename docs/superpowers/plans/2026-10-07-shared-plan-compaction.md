# Shared typed plan compaction

The user authorizes design, implementation, tests, measurements and local
commits without further approval. Work only on the existing diagnosis branch;
do not edit or add the untracked `docs/diagnostics/` directory.

## Design and constraints

Use the typed telescope as the single rule body. Core interprets its WFS
record, source-order premises and evaluator obligations. Prior-SCC calls keep
their selected-evaluator premise and a soundness bridge; local calls retain
their existing WFS interpretation. Fresh numeric allocation and compatibility
modes are unchanged. SCC membership is the image of allowed typed alternatives.
Generic inversion exposes the allowed alternative, its dependent witness and
ordered premises. Public relation names and argument signatures stay intact.
Internal proof representations may change; exact case propositions may not.

## Tasks

1. Preserve baseline generator; verify tracked status and backend tests. Record
   complete generated sources and a serial clean module build with Lean 4.34.1,
   `-j 2`, no reused generated oleans, wall/CPU/RSS and output sizes.
2. Add source-order Plan interpretation, WFS equivalence, and generic evaluator
   soundness in `typed_rule_plan.ml`; test all step constructors, binding,
   negative/callback boundaries, invalid certificates and fresh records.
3. Generate evaluator adapters from the same plan, preserving rule order and
   recoverable positions. Remove separately generated rule premises/proofs.
4. Generate SCC membership from allowed alternatives and use generic typed
   inversion. Reduce repeated introduction and relation API proof machinery.
5. Run all backend-lean tests, generate all P4 relations/evaluators twice and
   compile all modules cleanly. Distinguish clean and incremental runs; include
   Core, support, evaluators and inversion in total costs.
6. Recheck unchanged seven case goals and available proof attempts; report proof
   completion separately from goal elaboration and audit final theorem axioms.
7. Review the complete change, commit verified units, and record code examples,
   totals, semantic evidence and remaining limitations in a tracked report.

## Review focus

- Positive premise order must agree with source recoverable positions.
- Prior-SCC selection cannot silently become public WFS success.
- Polymorphic callbacks and extern instances must remain typed.
- A staged output/fresh witness cannot bypass guard or allocation evidence.
- Full measurements include every generated module, including proof modules.

## Execution record

- Initial HEAD `3deed878`; no tracked modifications. Only user diagnostics are
  untracked. Baseline generator copied outside the worktree.
- Baseline `opam exec --switch=spectecx -- dune build
  @p4spec/test/backend-lean/backend-lean` exited 0.
- Ruling: use the user's explicit approval throughout instead of skill approval
  handoffs. Preserve the requested worktree and local-only integration.
- Implemented a dependent lexical telescope, shared ordered premises and
  `ProgramOf` membership/inversion; removed generated per-rule evaluator bodies
  and relation-specific inversion proofs. Generic laws have exactly `[propext]`
  as their checked axiom set in the small fixture.
- Added rejection fixtures for wrong intermediate values, absent fresh records,
  nonnumeric fresh names and public success without ordered selection. Existing
  malformed certificate and choice/rollback fixtures pass after adapting their
  internal witness syntax, without changing their propositions.
- Full backend-lean alias passed after implementation and dead-code cleanup;
  shared-plan alias passed again after unused simp-argument cleanup.
- First whole-P4 candidate: 275 modules, 388,654 lines, 55,521,181 bytes.
  Full compiler validation is running separately from the baseline clean run.
  No compile-speed conclusion is drawn from these source-size figures.
- Whole-P4 preflight found a lexical shadow regression: a value binder named
  `nameIR` hid the global type used by a later initial binder. A two-argument
  shadow fixture failed before the fix and passes with accumulated binder
  scope; the complete backend-lean alias passed again.
- Added optional generic `spec_cases_allowed` / `spec_unpack_witness` proof
  helpers and verified typed inversion with them. These do not add generated
  relation-specific lemmas.
- Measurement driver smoke test compiled two modules cleanly, reused both on
  an unchanged run, and recompiled exactly one after touching the leaf.
- Full-context `$empty_typeFrame` marker-inclusive lines: semantics 35→40,
  evaluator 47→32, inversion 13→6; 95→78 combined. Body bytes 6180→5119.
  Its extra signature/Allowed data is included, not charged to a hidden file.
- Exact public signature/API comparison: 5210 relations, 1104 evaluators and
  5210 inversion wrappers in both versions; no missing or added API names.
  Generated source scans found no proof holes or axiom declarations.

- Measurement correction: the `lean` PATH entry is an elan shim. Process
  inspection caught it polling network sockets with zero compiler CPU, so the
  initial baseline timing run is discarded. Both final clean runs instead use
  the exact installed Lean 4.34.1 binary, serially on CPUs 0,1, starting from
  source-only directories. The measurement CLI now requires `--lean` and
  records its resolved path. This prevents launcher/network delay from being
  misreported as compiler cost.

- Full P4 preflight completed all 275 modules; all seven original goal
  definitions compile unchanged. This preflight includes reuse and is not the
  final clean timing comparison.
- Audited all 62,868 generated public SpecTec theorems. Their axiom union is
  exactly `[propext, Classical.choice, Quot.sound]`; no other axiom is allowed.
- A dependent-pair regression found stale tail variable IDs in the optional
  witness helper (RED). Unpacking the tail before the first field fixes it
  (GREEN). Added checked common head normalization for source-cast inversion
  with a separate RED→GREEN fixture. Full backend-lean suite passed afterward.
- Added a hand-written positive/negative WFS rule fixture proving membership
  in both directions independently of the compiler's record expression, and
  proved the callback boundary's terminal-True record equivalence.
- Case 454's exact original theorem is proved again with axiom set
  `[propext, Classical.choice, Quot.sound]`. Its preflight proof costs are
  recorded separately (including its large olean), not hidden in source totals.

- Independent final review of `3deed878..201562b6` found no Critical or
  Important issues. Deferred Minor: recognize Allowed membership declarations
  as extra module split boundaries for smaller-than-default split limits.
  Existing default full-P4 sources remain fixed for paired measurements.

- Case 487 is proved without changing its goal. Its adapted proof normalizes
  only newly obtained premises and substitutes explicit equality hypotheses,
  avoiding costly searches through unrelated judgements. Both 454 and 487
  have exactly the standard three axioms; final-source proof measurements
  remain separate from the complete generated-module benchmark.

- Final backend-lean alias forced rerun exited 0. Expanded axiom audit covers
  all 63,222 SpecTec namespace-family theorems, including shared Core, and
  rejects every axiom outside propext, Classical.choice and Quot.sound.

- Fixed-condition clean runs completed: baseline 293 fresh / 0 reused,
  3219.278 s, 4449480 KiB peak, 2405106024 olean bytes; final 275 fresh /
  0 reused, 1488.264 s, 3758696 KiB peak, 1081823296 olean bytes.
  No-op incremental runs reuse every module and are labeled separately.
- Kernel-type export confirms exact equality of 10420 public success/failure
  signatures, including implicit instances and universe parameters.

- Final-source proof replay completed: all seven unchanged goal definitions,
  both rejection theorems, and their importing axiom audit exit 0. The
  additional proof/support/audit cost is 466.153 seconds and
  622241040 olean bytes. Case 487 peaks at 11199200 KiB; this is
  reported prominently, with no unmeasured baseline comparison claim.
