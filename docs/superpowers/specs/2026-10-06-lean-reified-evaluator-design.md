# Reified SpecTec to Lean evaluator

## Intent

Replace the Lean backend's rule-specialized evaluator scaffolding with a
generated Lean representation of ordered rule plans and one shared evaluator
that interprets those plans.  The full specification and every evaluator stay
in the default output.  The change must preserve the public WFS judgement and
all current outcome distinctions without assuming determinism or treating one
failed output candidate as failure of a whole call.

The starting point is commit `5e85ed7f`.  Its relation-local extern type
closure, separated extern/non-extern fresh helpers, separated fresh-alpha and
relation-protection shapes, removal of eager `InProgram.head_property`, and
leaf-local `SpecTecProof.spec_invariant` checks are architectural constraints,
not code to be replaced.  The case 0/1/5 proof experiment is outside this
change.

## Baseline and success criteria

The supplied baseline is:

- generated output: 38,971,279 bytes and 282,763 lines;
- evaluator output: 10,691,090 bytes and 108,435 lines;
- evaluator header: 559,425 bytes and 9,936 lines;
- rule flow: 6,704,448 bytes and 57,662 lines;
- selection flow: 1,566,585 bytes and 18,459 lines;
- certificate wrappers: 1,860,632 bytes and 22,378 lines;
- 1,104 evaluator relations and 2,621 rule flows;
- generation: 9.933 seconds wall and 588,840 KiB peak RSS;
- `lean -j 2`: 1,357.009 seconds wall, 1,569.157 seconds CPU,
  34,878,464 KiB peak RSS, and 691,505,872 bytes of `.olean` output.

The required result emits the complete default relation-local specification,
including every evaluator, in deterministic output.  A full `lean -j 2`
compile must finish in less than ten minutes; less than five minutes is the
stretch target.  Size and performance improvements are reported only from
measurements made with the same commands and inputs as the baseline.

## Chosen architecture

### Rule plans

`SpecTecEval.EvalRulePlan Input Output Public` is the only semantic unit
generated for one source rule.  It contains:

```lean
structure EvalRulePlan
    (Input : Type u₁) (Output : Type u₂)
    (Public : Input → Output → Prop) where
  Witness : Type u₃
  input : Witness → Input
  output : Witness → Output
  premises : Witness → List Prop
  recoverable : List Nat
  publicSound : ∀ witness, Prefix (premises witness) →
    Public (input witness) (output witness)
```

The exact field names may change during the Lean prototype, but these roles may
not.  Rule binders are packed into a nested dependent `Sigma`, ending in
`Unit`, so a binder type may refer to an earlier binder.  A rule plan retains
the source input and output construction, the original premise order, the
recoverable positions, and the proof that successful premises construct the
public relation.

The common definitions `EvalRulePlan.Succeeds` and `EvalRulePlan.Fails` replace
the generated `:succeeds` and `:failed` bodies.  Success existentially chooses
one witness, matches both input and output, and requires `Prefix premises`.
Failure is universal over candidate outputs and witnesses: a head mismatch or
a `RuleFailure` at a recoverable premise is required.  `RuleFailure` continues
to require successful evidence for the complete earlier prefix.

The first implementation task prototypes this dependent representation on
polymorphic and dependent-binder fixtures.  If its elaboration cost is worse
than a shallow predicate/certificate plan on those same fixtures, the stored
plan may erase `Witness` into `succeeds`, `fails`, and `sound` closures.  Such
an erasure must be constructed by one common witness-plan combinator, preserve
the same public plan-list and certificate API, and be recorded with measured
evidence.  It may not restore five specialized declarations per rule.

### Rule selection

`SpecTecEval.SelectionPolicy` has ordered and nondeterministic cases.  A shared
indexed `Selected policy plans input output` certificate recursively interprets
the plan list:

- the head rule may succeed;
- nondeterministic selection may continue without head failure;
- ordered selection may continue only with a recoverable failure certificate
  for the head rule.

`AllFailed plans input` recursively requires every plan to fail.  The generic
`Selected.sound` theorem follows the selected list member and invokes that
plan's `publicSound`.  It is proved once in `ordered_semantics.ml`; the printer
does not emit a relation-specific disjunction or a relation-specific proof by
cases.

The plan list is part of the certificate type.  Tests use a typed plan index or
the corresponding `Selected` constructor, so evidence for the wrong rule is
not silently accepted.  `RuleFailure` keeps the premise-list and recoverable
list in its type, so evidence for a wrong premise position remains rejected.

### Relation evaluator

`SpecTecEval.Evaluator Input Output Public` contains only:

- the source-ordered `List (EvalRulePlan Input Output Public)`;
- its `SelectionPolicy`;
- the relation-specific `Input → Prop` undetermined predicate.

Shared projections define selected success, all-rules failure, and the existing
`Evaluation` outcome relation.  Shared theorems define selected-success
soundness, successful-evaluation soundness, universal rule-failure soundness,
and the abort, unsupported, timeout, and undetermined certificate views.

Each generated relation retains only its input/output aliases, public success
predicate, fresh-site data, one plan per source rule, the plan list, policy,
undetermined connection, and evaluator value.  Recursive premise calls still
refer to a relation-level `evalSelected` alias.  Relation-level `EvalInput`,
`EvalOutput`, `evalSucceeds`, `evalSelected`, `allRulesFailed`,
`evalUndetermined`, `eval`, and `freshSites` remain when they are required by
generated code or existing external proofs.

Existing relation-level certificate names such as `success_sound` and
`ruleFailure_sound` are retained only if they can be expressed as cheap
one-line aliases to the shared theorems without a material full-spec compile
cost.  Otherwise the README and proof fixtures are migrated explicitly to the
generic `SpecTecEval.Evaluator` theorems.  The five rule-internal declarations
`:premises`, `:recoverable`, `:succeeds`, `:failed`, and `:sound` are replaced
by one plan declaration and a documented indexed projection API; they are not
silently left as expensive compatibility wrappers.

## Semantic preservation

### Premises, failures, and outputs

`premises` is the exact translated premise list in source order.  `Prefix`
remains the success certificate, and `Prefix.get` remains the way a plan's
`publicSound` certificate reconstructs each public premise.  A recoverable
failure at any allowed position fails that complete rule; evidence for every
earlier premise is mandatory.  Constructor mismatch is recoverable at the
rule-head boundary.

Only interpreter `Unmatch`-class evidence may advance ordered selection.
`Err`, extern abort, unsupported features, timeout, and undetermined outcomes
remain separate terminal constructors.  They cannot inhabit plan failure or
the ordered continuation constructor.

An output-search failure remains `∀ output, ¬ publicSucceeds input output`.
Neither a failed candidate nor one successful evaluator run is generalized to
the whole call.  Nondeterministic selection admits more than one successful
output, and no relation-wide determinism theorem is introduced.

### `otherwise`, recursion, and WFS soundness

The translator's existing regular/enabled/otherwise relations remain intact.
Their rules become plans like all other rules.  The regular relation's ordered
selector requires preceding rule failures; the public otherwise wrapper can
only satisfy its recoverable negative/regular premise after every regular rule
has failed.  There is no special shortcut in the common evaluator.

Non-recursive relations use `False` for the evaluator's undetermined field.
Recursive and negative-cycle relations keep their existing relation-local WFS
upper/lower evidence.  The common evaluator merely stores and exposes that
predicate; it does not reinterpret cycles.

Every plan's `publicSound` field invokes the existing generated public rule
constructor, converting evaluator premises to public premises exactly as the
current `:sound` theorem does.  Local evaluator calls are converted with the
generic selected-sound theorem.  Fresh premises are converted through
`SpecTecFresh.AllocatedAt.toAllocated`.  Consequently evaluator success proves
the existing WFS public judgement without `sorry`, new axioms, or a second
global program closure.

### Extern callbacks and fresh names

`print_eval_application` keeps its current typed callback and external-target
parameterization.  The refactor changes only the target certificate expression
from a relation-specific theorem to the shared evaluator theorem.  Relation
graph ownership, typed callback targets, and extern boundary routing do not
change.

Fresh allocation sites continue to be keyed by relation, source rule index,
and premise index.  Plans store the same `AllocatedAt` propositions, while the
relation retains the same `freshSites`.  Supply threading, rollback, nominal
alpha, protected ordinary names, and separated extern fresh helpers are not
rewritten by this change.

## Generator changes

`ordered_semantics.ml` gains the plan, selection, evaluator, and common
soundness definitions.  `printer.ml` replaces `print_eval_rule_flow` with a
plan printer and reduces `print_ordered_evaluator` to relation-specific data.
`print_eval_premise` continues to choose public versus evaluator evidence but
targets the generic certificate API.  `translator.ml`, `pipeline.ml`,
`wfs_backend.ml`, and `relation_graph.ml` change only if a typed interface
adjustment is necessary; no global Atom/InProgram closure is introduced.

The generated source remains deterministic.  Splitting generated Lean into
Core/Evaluators files is deliberately deferred: the first measured change is
semantic commoning, not file layout.

## TDD and verification

Before product code changes, the focused checker will assert the current five
rule declarations and then be changed to require one plan per rule, shared
selection, and the absence of repeated rule-flow declarations.  The RED run
must fail on `5e85ed7f` for the expected structural reason.

Focused proof fixtures cover:

1. same-pattern premise failure followed by the next rule's success;
2. `otherwise` only after all ordinary rules fail;
3. one failed candidate of an output-unknown call is not whole-call failure;
4. multiple successful outputs of a nondeterministic relation;
5. recoverable failure versus abort;
6. unsupported versus timeout;
7. recursive and negative-cycle undetermined evidence;
8. fresh premises and rollback behavior;
9. every success certificate reconstructing the public judgement;
10. rejection of wrong rule and premise-position certificates;
11. no `sorryAx` in the checked theorem set.

Existing fresh, extern, callback, relation-local, negative-cycle, proof-support,
and size regressions run unchanged or receive only the documented certificate
API migration.  `experiments/cases-0-1-5/` is not modified or run as a
completion condition.

After focused tests and `@backend-lean`, generate the full default
relation-local specification twice and byte-compare it.  Record total and
evaluator bytes/lines with the same section analysis used for the baseline.
Compile the generated source to `.olean` with `lean -j 2` under `/usr/bin/time
-v`, recording wall, user, system, peak RSS, and `.olean` bytes.  Run
`git diff --check`, verify the intended worktree status, inspect for `sorryAx`,
and commit only the verified implementation and documentation.

## Non-goals

- Do not omit evaluators, add `--core-only`, or claim a file split as the
  performance result.
- Do not work on case 0, case 1, or case 5 proofs or their tmux sessions.
- Do not restore global Atom/InProgram closure, eager head properties, or
  coupled fresh/extern dependency shapes.
- Do not infer determinism, rejection, or all-output properties from one
  evaluator success.
- Do not report an unmeasured speedup or compare measurements made under
  different modes, inputs, Lean versions, or concurrency.
