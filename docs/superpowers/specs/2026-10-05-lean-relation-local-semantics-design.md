# Relation-local SpecTec to Lean semantics

## Intent

Redesign the Lean backend so the default translation exposes one judgement per
source relation and does not route every rule through a global `Atom`, a global
`InProgram`, or a program-wide fresh counter.  The generated semantics must
preserve the source interpreter's ordered premise and alternative behaviour,
distinguish recoverable rule failure from abort and timeout, and make fresh
allocation branch-local while retaining name safety and alpha comparison.

The default mode is a new relation-local semantics.  The previous concrete
counter semantics remains available only as an explicitly named legacy mode.
The existing `--fresh-rollback` experiment remains a separate legacy
abstraction; neither legacy mode is evidence for the new default semantics.

## Chosen architecture

Keep the translated rule AST, because it already preserves source premise
order, input positions, typed arguments, binders, and source locations.  Add a
typed dependency analysis and print one local semantic component per strongly
connected component (SCC):

1. A singleton, non-recursive relation receives its own local atom and program.
2. Relations in a real recursion cycle share one local atom and program.
3. A call inside the same SCC is a local positive or negative WFS atom.
4. A call to an earlier SCC is a side proposition using that relation's public
   success, failure, abort, or timeout judgement.
5. Extern calls are typed boundary outcomes and never cause all unrelated
   relations to share a program.

The public surface contains direct relation names and relation-local namespaces.
There is no generated root `Atom`, `InProgram`, global membership alias tree,
or global head-property tree in the default mode.

### Typed callback dependencies

`SpecTecRelationRef` must retain input and output types and the actual named
target.  Dependency analysis propagates named targets through callback
parameters to the sites that invoke them.  A named callback adds an edge to its
actual relation; an external callback remains an explicit typed extern edge.
Unknown dynamic named targets are rejected rather than omitted.  This points-to
analysis is also used to decide which SCC owns callback dispatch rules.

Extern type and `SpecTecP4ExternModel` parameters are attached only to types,
relations, and SCCs whose signatures or rule bodies require them.  Merely having
an extern declaration elsewhere in the specification does not parameterize a
judgement.

## WFS decomposition and cycles

The dependency graph contains positive calls, negative calls, expression calls,
and resolved callback calls.  SCC construction ignores edge polarity; polarity
is retained on edges inside a component.  Only a component with a graph cycle
uses recursive WFS reasoning.  In particular, negative-cycle failure and
undetermined states cannot leak into an unrelated component.

The relation-local and former global WFS meanings correspond under these
conditions:

- every internal call target, including a callback target, occurs as a graph
  edge;
- cross-component calls refer only to an earlier component in the condensation
  DAG;
- extern outcomes are identical at the boundary;
- generated helper relations remain in the component of their public owner or
  of a dependency that creates a genuine cycle;
- a negative call asks whether the whole input call has no matching output, not
  whether one arbitrarily chosen output atom fails.

The backend emits these conditions as checked dependency metadata and reusable
decomposition lemmas.  If a callback target or helper ownership cannot be
established, translation fails with the source location.  The implementation
does not claim that an unchecked graph decomposition preserves the old global
WFS result.

## Ordered evaluation and `otherwise`

Each relation gets an ordered evaluator relation with outcomes:

- `success output`: a rule matched and all premises succeeded in source order;
- `ruleFailure`: all alternatives produced recoverable `Unmatch`;
- `abort error`: an interpreter `Err` or extern abort stopped evaluation;
- `unsupported feature`: translation or evaluation reached an IL construct for
  which the backend has no semantics;
- `timeout`: the supplied fuel was exhausted;
- `undetermined`: a local negative cycle has upper but not lower WFS evidence.

Rule input matching and premise execution are separate.  A rule's recoverable
failure certificate records the first failing premise and refers to a shared
prefix execution certificate.  It does not copy every earlier successful
premise into a fresh generated rule.  An abort is propagated immediately and
does not enable the next alternative.  The next ordinary rule is considered
only after recoverable failure.  `otherwise` is considered only after every
ordinary alternative has a recoverable failure certificate.

Calls with output positions not fixed by the caller range over matching
outputs.  Failure means there is no successful matching output.  Failure of one
candidate output never proves failure of the call.  The evaluator makes no
relation-wide determinism assumption; deterministic-mode ambiguity is a
separate abort outcome.

For every generated evaluator, `success_sound` maps one success certificate to
the public judgement.  It does not turn one success into a rejection proof,
uniqueness, or a theorem about every output.  Rejection and all-output alpha
properties require their own certificates or proofs.

## Fresh identifiers and supplies

The internal allocator uses distinct types:

```text
FreshSite = relation/SCC + rule + premise/iteration/call path
FreshId   = FreshSite + local occurrence
FreshName = ordinary String | allocated FreshId
```

A supply maps sites to their next occurrence and carries protected ordinary
names.  Entering an alternative snapshots the supply.  Recoverable failure
discards that alternative's allocations.  Success commits the returned supply,
so successful sibling, sequential, recursive, and iteration calls receive
different identifiers.  Repeated uses of one allocated value retain the same
`FreshId`.  Binder and scope operations preserve the tag, and allocation never
chooses a rendered name in the protected input/context set.

Concrete rendering is a boundary operation.  The default semantics compare
whole outputs by one bijective alpha map over `FreshId`; ordinary names are
fixed, allocated identifiers map injectively, and repeated references map
consistently.  Concrete numeric suffixes are not part of this relation.

The backend audits uses of fresh-derived text.  Equality used for binding,
scope, capture avoidance, and protected-name checks is supported nominally.
String concatenation, lexical comparison, printing that influences execution,
and sorted-set operations are observable.  A specification using such an
operation on fresh-derived data is rejected by the new default unless a
generated compatibility obligation proves that rendering preserves the
operation.  The legacy exact-counter mode remains available for those programs.
No output ordering or string semantics is changed silently.

## Proof support

`SpecTecProof.lean` supplies local tools instead of global closure generation:

- induction over one relation or recursive SCC;
- inversion for one public judgement or evaluator outcome;
- checking of generated success, failure, abort, timeout, and alpha
  certificates;
- WFS decomposition lemmas and local failure/undetermined lemmas;
- the existing post-generation axiom check, allowing only the established
  Lean axioms.

Generated membership and head lemmas are local to an SCC and emitted only when
used by its induction or inversion interface.  `Decl_ok` inversion therefore
does not require cases for constant, instantiation, function, or action rules
whose input constructors cannot match `errorDeclaration`.

## Compatibility modes

- Default: relation-local SCC semantics, ordered evaluator, branch-local nominal
  fresh supply, and alpha output obligations.
- `--fresh-exact-counter`: the previous concrete counter semantics, retained to
  audit string/order-sensitive specifications and exact interpreter output.
- `--fresh-rollback`: the previous rollback experiment, retained only for
  reproducing its recorded measurements and proofs.

Generated source records its mode.  Obligations and semantics generated in
different modes cannot be combined.

## Verification

Regression fixtures cover, in this order:

1. rules with distinct input constructors are excluded locally;
2. a same-pattern rule fails at a premise and the next rule succeeds;
3. a call with an unknown output does not fail because one output fails;
4. allocation in a failed alternative is rolled back;
5. sequential, recursive, and iterated successful allocation is distinct while
   repeated references remain equal;
6. ordinary-name collision protection and capture avoidance;
7. positive recursion, negative recursion, abort, unsupported syntax, and
   timeout have distinct outcomes;
8. typed named callbacks form dependencies and real callback recursion, while
   extern callbacks remain boundaries;
9. generated modules contain no default-mode global `Atom` or `InProgram` and
   unrelated declarations do not acquire extern contexts.

After the small suite passes, regenerate cases 0, 1, and 5 in the new default
mode.  Prove complete rejection for cases 0 and 1.  Prove complete acceptance
for case 5 and separately prove that every successful output is alpha-related
to the expected output.  A proof of only the first `ERROR` declaration or a
conditional reconstruction theorem is not completion.

Measurements are stored separately from
`experiments/cases-0-1-5/RESULTS.md` and its `--fresh-rollback` baseline.  Record
generated bytes/lines, generated theorem and certificate counts, compile wall
time, CPU time, maximum RSS, proof source length, proof-authoring and failed
check time, and `.olean` size.  Report only observed differences.

## Non-goals and explicit limits

The redesign does not infer global determinism from one evaluator run.  It does
not equate `not Holds` with WFS failure.  It does not turn an interpreter abort
into rejection.  It does not accept an untracked dynamic callback, a fresh
string observation without a compatibility proof, or an unsupported IL
construct by dropping it from generated semantics.
