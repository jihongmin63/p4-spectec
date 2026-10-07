# Numeric fresh spelling and typed rule plans

## Intent and scope

The default relation-local translation keeps `FreshId` (site, dynamic path,
occurrence), `FreshName`, protected names, allocation records, nested supply
threading, WFS, source alternatives, and public relation signatures. It
restricts allocation spellings to `freshText n = "FRESH__" ++ Nat.repr n`.
The legacy exact-counter and rollback modes retain their current behavior.
This is a deliberate restriction of the default relation, not an equivalence
claim about every derivation of the old relation.

The current `EvalRulePlan` depends on the public relation through
`publicSound`, while SCC-local `InProgram` separately stores the same rule
body. The replacement stores one typed rule plan before either public
relation or evaluator is defined. `Program_ok` is an ordinary relation.

## Fresh representation

`occurrence` remains an identity component determined by the number of used
IDs in the current supply. It is **not** the spelling number: separate sites
and dynamic paths may need different spellings, and protected `FRESH__n`
names can force gaps. An allocation chooses a natural `n`, records the pair
`(FreshId, n)` and the concrete spelling, and checks the protected and
already-rendered names. A derived string is still tracked in `rendered` for
collision checks; deriving text does not allocate an ID or require the
derived text to have fresh spelling. An admissible rendering of a used ID
uses `freshText n` and agrees with its recorded allocation number. The
spelling for one recorded ID cannot change, and distinct used IDs cannot
have equal spellings. `Allocated`, `AllocatedAt`, the singleton witness,
`allocatedAt_of_text`, the builtin, and evaluator fresh premises use this
same restriction. Where a theorem receives a string, it requires a number
and equality with `freshText` instead of accepting arbitrary text.

The relational allocator may choose any nonconflicting numeric suffix.
This design does not silently impose the interpreter's next-counter policy.
Canonical oracle outputs can still be compared with the existing alpha
condition and allocation trace. Failed branch supply handling stays as is.

## Plan representation and dependency flow

For each SCC, generated typed relation tags carry input/output signatures
and mode. A rule is a telescope of typed steps. A step consumes the values
already bound by the preceding telescope and extends its environment with
the output of a positive call, fresh allocation, or local computation. Guards,
negative calls, and side conditions consume the current environment without
extending it. The last step constructs the head output. Thus the Lean type
of a step's continuation prevents use of a value before its binding.

Tags distinguish same-SCC calls, prior-SCC calls, and external callbacks.
Each call keeps its original input/output mode. Fresh steps contain the site,
entry supply, output string, and exit supply. The plan stores the source
alternative index, source premise index, recoverable positions, and policy.
Only the existing recoverable failures select a later alternative; abort,
unsupported, timeout, and undetermined remain distinct. No Boolean decision
is assumed for arbitrary propositions or extern calls.

## Three interpretations

1. **WFS.** Interpret the telescope into one `SpecTecWFS.Rule Atom` for each
   complete assignment of its bound values. Same-SCC positive and negative
   calls become positive and negative atoms; prior-SCC and external calls
   remain side propositions. `InProgram` is membership in this image, with
   callback boundary rules included. Prove both directions of membership
   for any old/new representation comparison; dependency graph equality is
   insufficient.
2. **Success checker.** A certificate identifies the alternative and gives
   intermediate values and recursive subcertificates. A checker processes
   steps in order and recomputes the final output. Computable guards are
   checked; opaque guards and extern calls require explicit Lean evidence.
   Soundness is proved by induction on certificates and WFS rule application.
   A finite, Boolean-checkable fragment may gain a completeness theorem;
   arbitrary recursive and negative WFS does not.
3. **Public inversion.** From a public `Holds` proof, expose a rule tag and
   named, typed premise records. Hide `InProgram` constructors, head casts,
   and positional conjunction projections. Negative and earlier-SCC facts
   retain their WFS meaning. This inversion is independent of whether a
   computable success certificate exists.

## Generated module graph

`Core` holds WFS, fresh, plan, checker, and generic soundness. Generated
types/support imports Core. Each SCC module imports support and its earlier
SCC dependencies, defines tags, plans, public relations, and inversion.
Evaluator/checker modules import SCC modules, never the reverse. Case
modules import the aggregate specification and define the unchanged goals;
proof modules import cases. The aggregate entry imports every SCC and every
evaluator. File boundaries follow the checked dependency graph, keeping
mutually recursive relations together.

## Verification and measurements

First use tiny fixtures for numeric fresh exclusion, protected/rendered
collisions, ID/spelling consistency, nested supply, failure selection, plan
membership, forged certificates, soundness, and public inversion. Then
generate the full P4 specification and all evaluators, check acyclic imports
and reproducible output, and repeat the seven specified cases against the
same accepted universal-alpha or rejected nonexistence goals. New regression
goals for the restricted fresh semantics are reported separately.

Record machine and flags, cold and incremental build wall time, peak RSS,
`.olean` bytes, certificate and support source bytes, agent-search and first
exact-theorem times, final-proof compilation, Lean executions, and retries.
The watcher compiles only after an explicit candidate-ready signal; stale
candidates are discarded and child processes are reaped. Check theorem axiom
sets and reject `sorry`, `admit`, `sorryAx`, and new axioms.
