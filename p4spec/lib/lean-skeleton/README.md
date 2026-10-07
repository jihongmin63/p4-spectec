# Lean Skeleton

The executable translates elaborated SpecTec IL into Lean source. Its path is:

1. `main.ml` parses CLI options, elaborates the requested spec paths, and collects diagnostics.
2. `pipeline.ml` selects strict translation or best-effort translation, then sequences the backend stages.
3. `translator.ml` lowers IL declarations into the Lean AST in `ast.ml`.
4. `order.ml` resolves declaration dependencies, groups mutual definitions, and removes invalid dependency chains in best-effort mode.
5. `relation_graph.ml` preserves edge polarity, propagates typed named callback targets, and orders relation SCCs.
6. `printer.ml` renders the ordered Lean AST as source.

## Module Responsibilities

- `ast.ml` defines the source alias and the Lean intermediate representation.
- `translator.ml` handles IL types, expressions, premises, relations, tables, and declarations. Tables become row-selector definitions paired with relation rules. `builtin.ml` provides total builtins as Lean definitions and `builtin_relation.ml` provides partial or value-comparing builtins as relations.
- `order.ml` validates and orders Lean declarations. `traversal.ml` provides recursive operations over the Lean AST used by ordering and translation.
- `printer.ml` serializes declarations and terms. By default it emits a private `Atom` and `InProgram` for each dependency SCC, direct public `Prop` judgements, and relation-local rule introduction theorems. Calls to earlier SCCs are side judgements; only same-SCC calls remain WFS atoms. `wfs_backend.ml` contains the shared Lean `Rule`, `Program`, well-founded semantics, and checked program-equivalence lemmas. `identifier.ml` escapes names for Lean syntax.
- `main.ml` owns command-line behavior; `pipeline.ml` owns the translation-to-printing flow.

Translation stops at the first translation or ordering error. `--keep-going` retains independent declarations and reports rejected declarations.

## Relation semantics

The default translation computes SCCs from positive, negative, expression, and typed callback calls. Each source rule contributes a member of its SCC-local `InProgram`. Same-SCC positive and negative premises become local atoms; calls to an earlier SCC become direct public success or `.fails` side judgements. A public relation is `SpecTecWFS.Holds` of its local atom. `.fails` is always available, while `.undetermined` is emitted only for a graph-cyclic SCC. Named callback dispatch belongs to the invoking SCC and points only at the propagated typed targets; external callbacks remain explicit boundary rules.

The generated root namespace has no program-wide `Atom`, `InProgram`, membership alias tree, or head-property tree. A component still has a small local atom, membership relation, and head-property lemma for local induction. Extern-type and P4-model variables are emitted in sections containing the declarations and components that depend on them. Dependency closure is explicit: an unrelated component does not acquire those instances merely because another source declaration uses an extern.

`SpecTecWFS.Program.Equivalent` requires bidirectional membership for every rule. Its congruence theorems transport `Holds`, `Fails`, and `Undetermined` only after that condition is proved; graph reachability alone is not presented as semantic equivalence with the former global program. `--dump-relation-graph` prints the checked SCCs, signed/callback edges, typed callback sites, and external callback boundaries used by the printer.

The old global program is retained only in explicit compatibility modes:

- `--fresh-exact-counter` selects the former program-wide `Atom`/`InProgram` and concrete counter lowering.
- `--fresh-rollback` selects the distinct rollback/alpha experiment.

Generated source begins with a mode marker. The test suite passes the exact-counter option explicitly for legacy global proofs and size/split checks; default-mode locality and legacy reproducibility are tested separately.

Each local component has a `head_property` theorem.  The optional
`SpecTecProof.lean` module provides `spec_invert` and `spec_induction`; the
component is inferred from the supplied proof, so splitting its membership
exposes only the owning relation/SCC.  `spec_check_certificate` applies a typed
checker to an evaluator certificate.  The legacy `spec_invariant` command is
retained for explicit global compatibility modes; it builds bounded closure
lemmas, preserves `SpecTecWFS.Fails` on negative premises, and rejects
unapproved axioms.

The default evaluator runs source premises left-to-right through a shared
`Prefix`.  Outcomes distinguish `success`, universal `ruleFailure`, `abort`,
`unsupported`, zero-fuel `timeout`, and SCC-local `undetermined`.  Only a
recoverable premise position may select the next source alternative.  A call
with an unknown output needs an `OutputSearchFailure` quantified over every
candidate; one failed candidate is not rejection evidence.  Generated
`success_sound`, `ruleFailure_sound`, `abort_sound`, `unsupported_sound`,
`timeout_sound`, and `undetermined_sound` theorems expose exactly the evidence
carried by each outcome.  They do not add a determinism assumption.

The default fresh interface defines tagged `FreshId`/`FreshName`, allocation
sites, branch rollback/commit, protected-name rendering certificates, and one
whole-output `FreshNominalAlphaIR` bijection.  The static audit rejects a
fresh-derived string operation when the nominal model lacks a rendering
compatibility proof.  Equality used for binding, scope, and capture avoidance
is nominal; concatenation, lexical ordering, printed control, and sorted sets
are rendering-sensitive.  The current implementation is intentionally
incomplete: dynamic evaluator supply threading and extraction of protected
names from actual inputs/contexts are not yet connected to full generated
executions.

The `--fresh-exact-counter` compatibility model reproduces the interpreter's
counter, including allocations in failed clauses. `--fresh-rollback` selects a proof abstraction:
successful calls thread an entry and exit counter, but failure predicates have
only an entry counter. Every alternative starts at the same entry counter, so
failed allocations do not connect the state of different clauses. Successful
sequential and nested calls still receive distinct IDs.

This option also generates shared `FreshRename_*` definitions and the
`FreshAlphaIR` relation for types reachable from `p4programIR`. One bijective
renaming acts on all generated names; constructors, numbers, list order,
ordinary strings, extern values and function references are preserved.
Repeated references remain consistent and different IDs cannot be collapsed.
The generated helpers and their proofs are part of the shared proof cost.

For accepted `--case` or `--manifest` entries, rollback mode replays the exact
interpreter and checks the supplied answer against its canonical `--dump-output`
term. Actual allocation identities determine which output strings may be
renamed; the `FRESH__` prefix alone is never sufficient. All input strings and
ordinary output strings are fixed, including ordinary strings whose spelling
matches an allocated ID. Text derived by concatenation or other string
operations is conservatively fixed. Cases require an accepted output and
uniqueness up to `FreshAlphaIR`; rejected cases still require nonexistence.
The interpreter is reused across cases, with its counter reset for each one.

This is an explicit abstraction, rather than an equivalence theorem for every
SpecTec program. Fresh spelling can affect comparisons, capture checks,
string-derived identifiers and ordered sets; rollback can therefore change
observable behavior in such programs. Use `--fresh-exact-counter` for those
legacy proofs. `--obligations-only --fresh-rollback` requires importing semantics
generated with the same flag. Oracle capture flags use the exact interpreter
and cannot be combined with `--fresh-rollback`.

In the legacy modes, a function with `otherwise` creates `regular inputs result`, `enabled inputs`, and the public result atom. Any regular result establishes `enabled`, even when the result is unknown. The fallback rule requires WFS failure of `enabled`, so an undetermined enabled atom does not select the fallback. In the default mode these helpers are partitioned by the same typed dependency graph; the ordered evaluator layer is responsible for source-order `Unmatch`/abort behavior.

The `$union_set`, `$unions_set`, `$diff_set`, and `$intersect_set` builtins
translate only when their key type expands to `text`. Their Lean definitions
are monomorphic over `String` and normalize every input, because SpecTec
exposes the duplicate-free `Value.compare` order of set elements as a list;
only its text ordering is reproduced exactly by Lean `String` ordering.

## P4 type-checking proof obligations

The executable also parses P4 files with the repository's P4 parser and turns
each parsed `p4program` value into a Lean term. The term is translated using the
constructor signatures of the elaborated SpecTec IL, including the parser's
internal list nodes whose runtime type annotations differ from the declared
SpecTec type. An accepted case supplies a fixed `p4programIR` answer. Its
proposition requires both `Program_ok input expected` and that every possible
`Program_ok` output equals `expected`. A rejected case requires
`¬ (∃ output : p4programIR, Program_ok input output)`. The generated definitions
contain no proofs.

`p4spec/test/backend-lean/discover_typecheck.py` inventories the repository's
SL static-semantics suites. They record 1,948 P4 cases: 1,282 expected to
pass, 550 expected to fail, and 116 excluded. The p4c boot suite covers the
same 1,918 p4c files; 34 of its negative results say `(unknown)` and therefore
cannot serve as rejection evidence. The parse-only and STF simulation suites
are outside this type-checking inventory. Run the script with `--list` for
every source path, recorded outcome, and originating suite.

The proof corpus is in `p4spec/test/backend-lean/typecheck-cases.tsv`.
It contains 1,909 targets: 1,334 accepted, 574 rejected by relation nonmatch,
and one `abort-reject` conjecture. Every accepted case has a fixed, compressed
Lean output term in `p4spec/test/backend-lean/oracles/full/`, captured from the
repository's deterministic SL interpreter running `Program_ok`. The companion
`typecheck-audit.tsv` records the original suite outcome and actual interpreter
result for all 1,948 inputs; `-` marks an empty diagnostic. The remaining 39
inputs failed parsing, so no
`p4program` value is available for a `Program_ok` proposition. The aborting
case is a negative proof target, but the interpreter did not establish its
rejection: `p4_16_errors/issue3188.p4` aborts on a V1 model version check.
Existing `.expected` files record only pass, fail, or exclude
status; the test runners discard the actual P4 IR output. The p4c `*_outputs`
files are compiler artifacts, not SpecTec `p4programIR` answers.

All 116 originally excluded cases were evaluated. Of those, 111 were
parseable. The current SpecTec interpreter rejected 59 and accepted 52.
The audit preserves both the original suite category and the observed outcome.

The manifest uses tab-separated `accept<TAB>P4<TAB>expected-Lean-term`,
`reject<TAB>P4`, or `abort-reject<TAB>P4`; paths are relative to the manifest
file. Answer files may be plain text or `.gz`. Blank lines and lines starting
with `#` are ignored. The fixed answers make output changes visible before
any Lean proof is attempted.

From the repository root, compare every answer file and recorded outcome with
the current SL interpreter:

```sh
python3 p4spec/test/backend-lean/discover_typecheck.py
python3 p4spec/test/backend-lean/verify_oracles.py \
  --exe _build/default/p4spec/lib/lean-skeleton/main.exe \
  --manifest p4spec/test/backend-lean/typecheck-cases.tsv \
  --audit p4spec/test/backend-lean/typecheck-audit.tsv \
  --spec spec --include p4c/p4include
```

Repeat the verifier with `--reverse` to check that IR answers do not depend
on the order in which cases are evaluated.

From the repository root, generate the current corpus's propositions with:

```sh
dune exec p4spec/lib/lean-skeleton/main.exe -- \
  --obligations-only -I p4c/p4include \
  --manifest p4spec/test/backend-lean/typecheck-cases.tsv spec \
  > typecheck-obligations.lean
```

The full output is about 390 MB. For proof work, `--case-range START COUNT`
generates a smaller piece while retaining each case's global `case_N` index.
For example, `--case-range 0 50` generates the first 50 propositions.
The input and answer terms for 1,908 of these targets type-check against the
translated P4 syntax with an opaque `Program_ok` declaration. The remaining
`switch_p4_16.p4` oracle expands to about 114 MB of Lean source and did not
finish Lean elaboration within the available validation time. It is still
captured, verified against the interpreter, and emitted as a proposition.

To refresh the answers after an intentional SpecTec change:

```sh
python3 p4spec/test/backend-lean/discover_typecheck.py --paths > /tmp/typecheck.paths
dune exec p4spec/lib/lean-skeleton/main.exe -- \
  --batch-cases /tmp/typecheck.paths -I p4c/p4include spec > /tmp/typecheck.scan.tsv
python3 p4spec/test/backend-lean/capture_typecheck.py --scan /tmp/typecheck.scan.tsv
```

This overwrites the answer files, audit, and manifest; review the changed
outcomes before accepting them.

Use `--case FILE EXPECTED` and `--reject-case FILE` for individual inputs.
`--dump-output FILE` prints the deterministic SL interpreter's `Program_ok`
output as a Lean term, for creating or auditing an answer file.
`--batch-cases PATHS` evaluates a newline-separated list of P4 paths in one
interpreter session. It resets the `fresh_typeId` counter before each program;
the interpreter's normal cache clear does not reset that counter, and its
generated names would otherwise depend on case order. `capture_typecheck.py`
turns a complete batch scan into the manifest, audit, and compressed oracle
files.
`--check-rejection FILE` succeeds only when `Program_ok` fails by relation
nonmatch; syntax errors and interpreter aborts fail the check. Without
`--obligations-only`, the executable appends the propositions to the translated
specification. The resulting Lean file can then be extended with proof
theorems for the generated `case_N` propositions.

At present, the default translation of the full `spec` directory stops at one
explicit rendering obligation: fresh-derived text reaches `$concat_text` in
`DirectApplicationStmt_inst` while constructing `typeId ++ "_" ++ fresh`.
The audit reports every such unproved observation; it does not silently change
string semantics or fall back to a legacy mode.  Consequently the corpus
propositions can be generated with `--obligations-only`, but cases 0, 1, and 5
have not been verified against a complete default-mode `Program_ok` module.
The measured status and reproducer are under
`experiments/cases-0-1-5/RELATION_LOCAL_RESULTS.md`.  `--keep-going` remains
disallowed with cases because it can omit `Program_ok` and produce dangling
propositions. The small
`case-obligation.watsup` fixture in `p4spec/test/backend-lean` exercises the
complete parse, translate, proposition, and Lean type-checking path.
