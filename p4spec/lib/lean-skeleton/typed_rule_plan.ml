let source = {lean|
set_option autoImplicit false

universe uPlan

namespace SpecTecPlan

/-- An SCC-local relation call with its declared input, output, and mode. -/
structure Signature (Atom : Type uPlan) where
  Input : Type
  Output : Type
  inputPositions : List Nat
  policy : SpecTecEval.SelectionPolicy
  atom : Input → Output → Atom

/-- A relation reference chosen by an earlier rule binder may vary with the
    current environment, while its input and output types remain fixed. -/
structure ScopedSignature (Atom : Type uPlan) (Env : Type) where
  Input : Type
  Output : Type
  inputPositions : List Nat
  policy : SpecTecEval.SelectionPolicy
  atom : Env → Input → Output → Atom

inductive Boundary where
  | priorSCC
  | callback
  | external

/-- Earlier SCCs and external callbacks remain side propositions in WFS. -/
structure ExternalSignature where
  Input : Type
  Output : Type
  inputPositions : List Nat
  policy : SpecTecEval.SelectionPolicy
  boundary : Boundary
  holds : Input → Output → Prop
  selection : Option { selected : Input → Output → Prop //
    ∀ input output, selected input output → holds input output } := none

def ExternalSignature.selected (signature : ExternalSignature) :
    signature.Input → signature.Output → Prop :=
  match signature.selection with
  | none => signature.holds
  | some selected => selected.val

theorem ExternalSignature.selected_sound (signature : ExternalSignature)
    (input : signature.Input) (output : signature.Output) :
    signature.selected input output → signature.holds input output := by
  unfold selected
  cases signature.selection with
  | none => exact id
  | some selection => exact selection.property input output

abbrev Signature.external {Atom : Type uPlan} (signature : Signature Atom)
    (program : SpecTecWFS.Program Atom) : ExternalSignature where
  Input := signature.Input
  Output := signature.Output
  inputPositions := signature.inputPositions
  policy := signature.policy
  boundary := .priorSCC
  holds := fun input output => SpecTecWFS.Holds program (signature.atom input output)

abbrev Signature.evaluated {Atom : Type uPlan} (signature : Signature Atom)
    (program : SpecTecWFS.Program Atom)
    (evaluator : SpecTecEval.Evaluator signature.Input signature.Output
      (fun input output => SpecTecWFS.Holds program (signature.atom input output))) :
    ExternalSignature :=
  { signature.external program with
    selection := some ⟨evaluator.Selected,
      fun _ _ proof => SpecTecEval.Evaluator.selected_sound (evaluator := evaluator) proof⟩ }

/-- A source rule in premise order. Each continuation receives only values
    bound by earlier steps. The `choose` step represents an existential source
    binder whose value is needed before any call can produce it. -/
inductive Plan (Atom : Type uPlan) : Type → Type (max uPlan 1) where
  | ret {Env : Type} (head : Env → Atom) : Plan Atom Env
  | at {Env : Type} (sourcePremise : Nat)
      (next : Plan Atom Env) : Plan Atom Env
  | choose {Env Value : Type} (next : Plan Atom (Env × Value)) : Plan Atom Env
  | bind {Env Value : Type} (next : Value → Plan Atom Env) : Plan Atom Env
  | bindCall {Env : Type} (signature : Signature Atom)
      (input : Env → signature.Input)
      (next : signature.Output → Plan Atom Env) : Plan Atom Env
  | bindExternal {Env : Type} (signature : ExternalSignature)
      (input : Env → signature.Input)
      (next : signature.Output → Plan Atom Env) : Plan Atom Env
  | bindFresh {Env : Type} (site : Env → SpecTecFresh.Site)
      (before : Env → SpecTecFresh.Supply)
      (next : String → SpecTecFresh.Supply → Plan Atom Env) : Plan Atom Env
  | call {Env : Type} (signature : Signature Atom)
      (input : Env → signature.Input)
      (next : Plan Atom (Env × signature.Output)) : Plan Atom Env
  | callScoped {Env : Type} (signature : ScopedSignature Atom Env)
      (input : Env → signature.Input)
      (next : Plan Atom (Env × signature.Output)) : Plan Atom Env
  | reframe {Env NextEnv : Type} (convert : Env → NextEnv)
      (next : Plan Atom NextEnv) : Plan Atom Env
  | callKnown {Env : Type} (signature : Signature Atom)
      (input : Env → signature.Input) (output : Env → signature.Output)
      (next : Plan Atom Env) : Plan Atom Env
  | callKnownScoped {Env : Type} (signature : ScopedSignature Atom Env)
      (input : Env → signature.Input) (output : Env → signature.Output)
      (next : Plan Atom Env) : Plan Atom Env
  | negative {Env : Type} (signature : Signature Atom)
      (input : Env → signature.Input) (output : Env → signature.Output)
      (next : Plan Atom Env) : Plan Atom Env
  | negativeScoped {Env : Type} (signature : ScopedSignature Atom Env)
      (input : Env → signature.Input) (output : Env → signature.Output)
      (next : Plan Atom Env) : Plan Atom Env
  | guard {Env : Type} (condition : Env → Prop)
      (next : Plan Atom Env) : Plan Atom Env
  | externalCall {Env : Type} (signature : ExternalSignature)
      (input : Env → signature.Input)
      (next : Plan Atom (Env × signature.Output)) : Plan Atom Env
  | externalKnown {Env : Type} (signature : ExternalSignature)
      (input : Env → signature.Input) (output : Env → signature.Output)
      (next : Plan Atom Env) : Plan Atom Env
  | externalNegative {Env : Type} (signature : ExternalSignature)
      (fails : signature.Input → signature.Output → Prop)
      (input : Env → signature.Input) (output : Env → signature.Output)
      (next : Plan Atom Env) : Plan Atom Env
  | fresh {Env : Type} (site : Env → SpecTecFresh.Site)
      (before : Env → SpecTecFresh.Supply)
      (next : Plan Atom (Env × (String × SpecTecFresh.Supply))) : Plan Atom Env
  | freshBound {Env : Type} (site : Env → SpecTecFresh.Site)
      (before : Env → SpecTecFresh.Supply)
      (next : Plan Atom ((Env × String) × SpecTecFresh.Supply)) : Plan Atom Env
  | freshKnown {Env : Type} (site : Env → SpecTecFresh.Site)
      (before : Env → SpecTecFresh.Supply) (output : Env → String)
      (after : Env → SpecTecFresh.Supply)
      (next : Plan Atom Env) : Plan Atom Env

/-- Flatten a pair-valued result into two binders for later premises. -/
def Plan.splitPair {Atom : Type uPlan} {Env First Second : Type}
    (next : Plan Atom ((Env × First) × Second)) :
    Plan Atom (Env × (First × Second)) :=
  .reframe (fun (env, (first, second)) => ((env, first), second)) next

/-- Source-order and recoverable-failure metadata live with the one rule. -/
structure Alternative (Atom : Type uPlan) (Input : Type) where
  sourceIndex : Nat
  recoverable : List Nat
  body : Plan Atom Input

/-- Exactly the values chosen or returned at binding steps of one plan. -/
def Plan.Witness {Atom : Type uPlan} {Env : Type} :
    Plan Atom Env → Type
  | .ret _ => Unit
  | .at _ next => next.Witness
  | .choose (Value := Value) next => Value × next.Witness
  | .bind (Value := Value) next => (value : Value) × (next value).Witness
  | .bindCall signature _ next => (value : signature.Output) × (next value).Witness
  | .bindExternal signature _ next => (value : signature.Output) × (next value).Witness
  | .bindFresh _ _ next => (output : String) ×
      (after : SpecTecFresh.Supply) × (next output after).Witness
  | .call signature _ next => signature.Output × next.Witness
  | .callScoped signature _ next => signature.Output × next.Witness
  | .reframe _ next => next.Witness
  | .callKnown _ _ _ next => next.Witness
  | .callKnownScoped _ _ _ next => next.Witness
  | .negative _ _ _ next => next.Witness
  | .negativeScoped _ _ _ next => next.Witness
  | .guard _ next => next.Witness
  | .externalCall signature _ next => signature.Output × next.Witness
  | .externalKnown _ _ _ next => next.Witness
  | .externalNegative _ _ _ _ next => next.Witness
  | .fresh _ _ next => (String × SpecTecFresh.Supply) × next.Witness
  | .freshBound _ _ next => String × SpecTecFresh.Supply × next.Witness
  | .freshKnown _ _ _ _ next => next.Witness

/-- Compile one assignment of intermediate values to its WFS rule. -/
def Plan.compile {Atom : Type uPlan} {Env : Type} :
    (plan : Plan Atom Env) → Env → plan.Witness → SpecTecWFS.Rule Atom
  | .ret head, env, _ =>
      { head := head env, positive := [], negative := [], side := True }
  | .at _ next, env, rest => compile next env rest
  | .choose (Value := Value) next, env, (value, rest) =>
      compile next (env, value) rest
  | .bind (Value := Value) next, env, ⟨value, rest⟩ =>
      compile (next value) env rest
  | .bindCall signature input next, env, ⟨value, rest⟩ =>
      let rule := compile (next value) env rest
      { rule with positive := signature.atom (input env) value :: rule.positive }
  | .bindExternal signature input next, env, ⟨value, rest⟩ =>
      let rule := compile (next value) env rest
      { rule with side := signature.holds (input env) value ∧ rule.side }
  | .bindFresh site before next, env, ⟨output, after, rest⟩ =>
      let rule := compile (next output after) env rest
      { rule with side :=
          SpecTecFresh.Allocates (site env) (before env) output after ∧ rule.side }
  | .call signature input next, env, (value, rest) =>
      let rule := compile next (env, value) rest
      { rule with positive := signature.atom (input env) value :: rule.positive }
  | .callScoped signature input next, env, (value, rest) =>
      let rule := compile next (env, value) rest
      { rule with positive :=
          signature.atom env (input env) value :: rule.positive }
  | .reframe convert next, env, rest =>
      compile next (convert env) rest
  | .callKnown signature input output next, env, rest =>
      let rule := compile next env rest
      { rule with positive :=
          signature.atom (input env) (output env) :: rule.positive }
  | .callKnownScoped signature input output next, env, rest =>
      let rule := compile next env rest
      { rule with positive :=
          signature.atom env (input env) (output env) :: rule.positive }
  | .negative signature input output next, env, rest =>
      let rule := compile next env rest
      { rule with negative :=
          signature.atom (input env) (output env) :: rule.negative }
  | .negativeScoped signature input output next, env, rest =>
      let rule := compile next env rest
      { rule with negative :=
          signature.atom env (input env) (output env) :: rule.negative }
  | .guard condition next, env, rest =>
      let rule := compile next env rest
      { rule with side := condition env ∧ rule.side }
  | .externalCall signature input next, env, (value, rest) =>
      let rule := compile next (env, value) rest
      { rule with side := signature.holds (input env) value ∧ rule.side }
  | .externalKnown signature input output next, env, rest =>
      let rule := compile next env rest
      { rule with side :=
          signature.holds (input env) (output env) ∧ rule.side }
  | .externalNegative _ failure input output next, env, rest =>
      let rule := compile next env rest
      { rule with side := failure (input env) (output env) ∧ rule.side }
  | .fresh site before next, env, ((output, after), rest) =>
      let rule := compile next (env, (output, after)) rest
      { rule with
        side := SpecTecFresh.Allocates (site env) (before env) output after ∧
          rule.side }
  | .freshBound site before next, env, (output, after, rest) =>
      let rule := compile next ((env, output), after) rest
      { rule with
        side := SpecTecFresh.Allocates (site env) (before env) output after ∧
          rule.side }
  | .freshKnown site before output after next, env, rest =>
      let rule := compile next env rest
      { rule with side :=
          (SpecTecFresh.Allocates (site env) (before env) (output env)
            (after env)) ∧ rule.side }

/-- Interpret premises in source order. Evaluation strengthens only external
    positive calls; WFS uses their public proposition. Administrative binding
    and reframing steps do not consume a recoverable premise position. -/
def Plan.premises {Atom : Type uPlan} {Env : Type}
    (evaluation : Bool) (positive negative : Atom → Prop) :
    (plan : Plan Atom Env) → Env → plan.Witness → List Prop
  | .ret _, _, _ => []
  | .at _ next, env, rest => premises evaluation positive negative next env rest
  | .choose (Value := Value) next, env, (value, rest) =>
      premises evaluation positive negative next (env, value) rest
  | .reframe convert next, env, rest =>
      premises evaluation positive negative next (convert env) rest
  | .bind (Value := Value) next, env, ⟨value, rest⟩ =>
      premises evaluation positive negative (next value) env rest
  | .bindCall signature input next, env, ⟨value, rest⟩ =>
      positive (signature.atom (input env) value) ::
        premises evaluation positive negative (next value) env rest
  | .bindExternal signature input next, env, ⟨value, rest⟩ =>
      (if evaluation then signature.selected (input env) value
        else signature.holds (input env) value) ::
        premises evaluation positive negative (next value) env rest
  | .bindFresh site before next, env, ⟨output, after, rest⟩ =>
      SpecTecFresh.Allocates (site env) (before env) output after ::
        premises evaluation positive negative (next output after) env rest
  | .call signature input next, env, (value, rest) =>
      positive (signature.atom (input env) value) ::
        premises evaluation positive negative next (env, value) rest
  | .callScoped signature input next, env, (value, rest) =>
      positive (signature.atom env (input env) value) ::
        premises evaluation positive negative next (env, value) rest
  | .callKnown signature input output next, env, rest =>
      positive (signature.atom (input env) (output env)) ::
        premises evaluation positive negative next env rest
  | .callKnownScoped signature input output next, env, rest =>
      positive (signature.atom env (input env) (output env)) ::
        premises evaluation positive negative next env rest
  | .negative signature input output next, env, rest =>
      negative (signature.atom (input env) (output env)) ::
        premises evaluation positive negative next env rest
  | .negativeScoped signature input output next, env, rest =>
      negative (signature.atom env (input env) (output env)) ::
        premises evaluation positive negative next env rest
  | .guard condition next, env, rest =>
      condition env :: premises evaluation positive negative next env rest
  | .externalCall signature input next, env, (value, rest) =>
      (if evaluation then signature.selected (input env) value
        else signature.holds (input env) value) ::
        premises evaluation positive negative next (env, value) rest
  | .externalKnown signature input output next, env, rest =>
      (if evaluation then signature.selected (input env) (output env)
        else signature.holds (input env) (output env)) ::
        premises evaluation positive negative next env rest
  | .externalNegative _ failure input output next, env, rest =>
      failure (input env) (output env) ::
        premises evaluation positive negative next env rest
  | .fresh site before next, env, ((output, after), rest) =>
      SpecTecFresh.Allocates (site env) (before env) output after ::
        premises evaluation positive negative next (env, (output, after)) rest
  | .freshBound site before next, env, (output, after, rest) =>
      SpecTecFresh.Allocates (site env) (before env) output after ::
        premises evaluation positive negative next ((env, output), after) rest
  | .freshKnown site before output after next, env, rest =>
      SpecTecFresh.Allocates (site env) (before env) (output env) (after env) ::
        premises evaluation positive negative next env rest

theorem Plan.premises_iff {Atom : Type uPlan} {Env : Type}
    (plan : Plan Atom Env) (positive negative : Atom → Prop)
    (entry : Env) (witness : plan.Witness) :
    SpecTecEval.Prefix (plan.premises false positive negative entry witness) ↔
      (plan.compile entry witness).side ∧
      SpecTecWFS.All positive (plan.compile entry witness).positive ∧
      SpecTecWFS.All negative (plan.compile entry witness).negative := by
  induction plan with
  | ret head =>
      dsimp only [Witness] at witness
      simp [premises, compile, SpecTecEval.Prefix, SpecTecWFS.All]
  | «at» position next ih =>
      dsimp only [Witness] at witness
      simp [premises, compile, ih]
  | choose next ih =>
      dsimp only [Witness] at witness
      rcases witness with ⟨value, rest⟩
      simp [premises, compile, ih]
  | bind next ih =>
      rcases witness with ⟨value, rest⟩
      exact ih value entry rest
  | bindCall signature input next ih =>
      rcases witness with ⟨value, rest⟩
      simp [premises, compile, SpecTecEval.Prefix, SpecTecWFS.All, ih,
        and_assoc, and_left_comm, and_comm]
  | bindExternal signature input next ih =>
      rcases witness with ⟨value, rest⟩
      simp [premises, compile, SpecTecEval.Prefix, ih,
        and_assoc, and_left_comm, and_comm]
  | bindFresh site before next ih =>
      rcases witness with ⟨output, after, rest⟩
      simp [premises, compile, SpecTecEval.Prefix, ih,
        and_assoc]
  | call signature input next ih =>
      dsimp only [Witness] at witness
      rcases witness with ⟨value, rest⟩
      simp [premises, compile, SpecTecEval.Prefix, SpecTecWFS.All, ih,
        and_assoc, and_left_comm, and_comm]
  | callScoped signature input next ih =>
      dsimp only [Witness] at witness
      rcases witness with ⟨value, rest⟩
      simp [premises, compile, SpecTecEval.Prefix, SpecTecWFS.All, ih,
        and_assoc, and_left_comm, and_comm]
  | reframe convert next ih =>
      dsimp only [Witness] at witness
      simp [premises, compile, ih]
  | callKnown signature input output next ih =>
      dsimp only [Witness] at witness
      simp [premises, compile, SpecTecEval.Prefix, SpecTecWFS.All, ih,
        and_assoc, and_left_comm, and_comm]
  | callKnownScoped signature input output next ih =>
      dsimp only [Witness] at witness
      simp [premises, compile, SpecTecEval.Prefix, SpecTecWFS.All, ih,
        and_assoc, and_left_comm, and_comm]
  | negative signature input output next ih =>
      dsimp only [Witness] at witness
      simp [premises, compile, SpecTecEval.Prefix, SpecTecWFS.All, ih,
        and_assoc, and_comm]
  | negativeScoped signature input output next ih =>
      dsimp only [Witness] at witness
      simp [premises, compile, SpecTecEval.Prefix, SpecTecWFS.All, ih,
        and_assoc, and_comm]
  | guard condition next ih =>
      dsimp only [Witness] at witness
      simp [premises, compile, SpecTecEval.Prefix, ih,
        and_assoc]
  | externalCall signature input next ih =>
      dsimp only [Witness] at witness
      rcases witness with ⟨value, rest⟩
      simp [premises, compile, SpecTecEval.Prefix, ih,
        and_assoc, and_left_comm, and_comm]
  | externalKnown signature input output next ih =>
      dsimp only [Witness] at witness
      simp [premises, compile, SpecTecEval.Prefix, ih,
        and_assoc, and_left_comm, and_comm]
  | externalNegative signature failure input output next ih =>
      dsimp only [Witness] at witness
      simp [premises, compile, SpecTecEval.Prefix, ih,
        and_assoc]
  | fresh site before next ih =>
      dsimp only [Witness] at witness
      rcases witness with ⟨⟨output, after⟩, rest⟩
      simp [premises, compile, SpecTecEval.Prefix, ih,
        and_assoc]
  | freshBound site before next ih =>
      dsimp only [Witness] at witness
      rcases witness with ⟨output, after, rest⟩
      simp [premises, compile, SpecTecEval.Prefix, ih,
        and_assoc]
  | freshKnown site before output after next ih =>
      dsimp only [Witness] at witness
      simp [premises, compile, SpecTecEval.Prefix, ih,
        and_assoc]

theorem Plan.eval_premises_sound {Atom : Type uPlan} {Env : Type}
    (plan : Plan Atom Env) (positive negative : Atom → Prop)
    (entry : Env) (witness : plan.Witness) :
    SpecTecEval.Prefix (plan.premises true positive negative entry witness) →
      SpecTecEval.Prefix (plan.premises false positive negative entry witness) := by
  induction plan with
  | ret head =>
      simp only [premises, SpecTecEval.Prefix]
      exact id
  | «at» position next ih =>
      simp only [premises]
      exact ih _ _
  | choose next ih =>
      rcases witness with ⟨value, rest⟩
      simp only [premises]
      exact ih _ _
  | bind next ih =>
      rcases witness with ⟨value, rest⟩
      exact ih value entry rest
  | bindCall signature input next ih =>
      rcases witness with ⟨value, rest⟩
      exact fun proof => ⟨proof.1, ih value entry rest proof.2⟩
  | bindExternal signature input next ih =>
      rcases witness with ⟨value, rest⟩
      exact fun proof => ⟨signature.selected_sound _ _ proof.1,
        ih value entry rest proof.2⟩
  | bindFresh site before next ih =>
      rcases witness with ⟨output, after, rest⟩
      exact fun proof => ⟨proof.1, ih output after entry rest proof.2⟩
  | call signature input next ih =>
      rcases witness with ⟨value, rest⟩
      simp only [premises, SpecTecEval.Prefix]
      exact fun proof => ⟨proof.1, ih _ _ proof.2⟩
  | callScoped signature input next ih =>
      rcases witness with ⟨value, rest⟩
      simp only [premises, SpecTecEval.Prefix]
      exact fun proof => ⟨proof.1, ih _ _ proof.2⟩
  | reframe convert next ih =>
      simp only [premises]
      exact ih _ _
  | callKnown signature input output next ih =>
      simp only [premises, SpecTecEval.Prefix]
      exact fun proof => ⟨proof.1, ih _ _ proof.2⟩
  | callKnownScoped signature input output next ih =>
      simp only [premises, SpecTecEval.Prefix]
      exact fun proof => ⟨proof.1, ih _ _ proof.2⟩
  | negative signature input output next ih =>
      simp only [premises, SpecTecEval.Prefix]
      exact fun proof => ⟨proof.1, ih _ _ proof.2⟩
  | negativeScoped signature input output next ih =>
      simp only [premises, SpecTecEval.Prefix]
      exact fun proof => ⟨proof.1, ih _ _ proof.2⟩
  | guard condition next ih =>
      simp only [premises, SpecTecEval.Prefix]
      exact fun proof => ⟨proof.1, ih _ _ proof.2⟩
  | externalCall signature input next ih =>
      rcases witness with ⟨value, rest⟩
      simp only [premises, SpecTecEval.Prefix, Bool.false_eq_true, ↓reduceIte]
      exact fun proof => ⟨signature.selected_sound _ _ proof.1, ih _ _ proof.2⟩
  | externalKnown signature input output next ih =>
      simp only [premises, SpecTecEval.Prefix, Bool.false_eq_true, ↓reduceIte]
      exact fun proof => ⟨signature.selected_sound _ _ proof.1, ih _ _ proof.2⟩
  | externalNegative signature failure input output next ih =>
      simp only [premises, SpecTecEval.Prefix]
      exact fun proof => ⟨proof.1, ih _ _ proof.2⟩
  | fresh site before next ih =>
      rcases witness with ⟨⟨output, after⟩, rest⟩
      simp only [premises, SpecTecEval.Prefix]
      exact fun proof => ⟨proof.1, ih _ _ proof.2⟩
  | freshBound site before next ih =>
      rcases witness with ⟨output, after, rest⟩
      simp only [premises, SpecTecEval.Prefix]
      exact fun proof => ⟨proof.1, ih _ _ proof.2⟩
  | freshKnown site before output after next ih =>
      simp only [premises, SpecTecEval.Prefix]
      exact fun proof => ⟨proof.1, ih _ _ proof.2⟩


/-- SCC membership is the image of its allowed typed alternatives. The
    predicate supports polymorphic rules without an untyped value encoding. -/
def ProgramOf {Atom : Type uPlan} {Env : Type}
    (allowed : Alternative Atom Env → Prop) (entry : Env) :
    SpecTecWFS.Program Atom :=
  fun rule => ∃ alternative, allowed alternative ∧
    ∃ witness : alternative.body.Witness,
      alternative.body.compile entry witness = rule

theorem ProgramOf.compiled_iff {Atom : Type uPlan} {Env : Type}
    {allowed : Alternative Atom Env → Prop} {entry : Env}
    {rule : SpecTecWFS.Rule Atom} :
    ProgramOf allowed entry rule ↔ ∃ alternative, allowed alternative ∧
      ∃ witness : alternative.body.Witness,
        alternative.body.compile entry witness = rule := Iff.rfl

theorem ProgramOf.compiled {Atom : Type uPlan} {Env : Type}
    {allowed : Alternative Atom Env → Prop} {entry : Env}
    {alternative : Alternative Atom Env} (member : allowed alternative)
    (witness : alternative.body.Witness) :
    ProgramOf allowed entry (alternative.body.compile entry witness) :=
  ⟨alternative, member, witness, rfl⟩

/-- The one WFS introduction bridge, shared by source APIs and evaluation. -/
theorem Plan.holds_rule {Atom : Type uPlan} {Env : Type}
    {program : SpecTecWFS.Program Atom} (plan : Plan Atom Env)
    (entry : Env) (witness : plan.Witness)
    (member : program (plan.compile entry witness))
    (premises : SpecTecEval.Prefix (plan.premises false
      (SpecTecWFS.Holds program) (SpecTecWFS.Fails program) entry witness)) :
    SpecTecWFS.Holds program (plan.compile entry witness).head := by
  obtain ⟨side, positive, negative⟩ :=
    (plan.premises_iff _ _ entry witness).mp premises
  exact SpecTecWFS.Holds.rule _ member side positive negative

/-- The evaluator reads the same typed body and reuses one soundness proof.
    It does not claim completeness for general WFS. -/
def Alternative.toEvalRule {Atom : Type uPlan} {Env : Type}
    (alternative : Alternative Atom Env) (entry : Env)
    (signature : Signature Atom) (program : SpecTecWFS.Program Atom)
    (member : ∀ witness, program (alternative.body.compile entry witness)) :
    SpecTecEval.EvalRulePlan signature.Input signature.Output
      (fun input output => SpecTecWFS.Holds program (signature.atom input output)) where
  Witness := alternative.body.Witness
  accepts := fun witness input output =>
    (alternative.body.compile entry witness).head = signature.atom input output
  premises := alternative.body.premises true
    (SpecTecWFS.Holds program) (SpecTecWFS.Fails program) entry
  recoverable := alternative.recoverable
  publicSound := by
    intro witness input output head premises
    rw [← head]
    exact alternative.body.holds_rule entry witness (member witness)
      (alternative.body.eval_premises_sound _ _ entry witness premises)

/-- Source-order alternatives and outcomes share one evaluator construction. -/
def evaluator {Atom : Type uPlan}
    (allowed : Alternative Atom Unit → Prop) (signature : Signature Atom)
    (alternatives : List {alternative : Alternative Atom Unit // allowed alternative})
    (recursive : Bool) : SpecTecEval.Evaluator signature.Input signature.Output
      (fun input output => SpecTecWFS.Holds (ProgramOf allowed ())
        (signature.atom input output)) where
  policy := signature.policy
  rules := alternatives.map (fun alternative =>
    alternative.val.toEvalRule () signature (ProgramOf allowed ())
      (ProgramOf.compiled alternative.property))
  undetermined := if recursive then fun input =>
    ∃ output, SpecTecWFS.Undetermined (ProgramOf allowed ()) (signature.atom input output)
    else fun _ => False

def Cases {Atom : Type uPlan} {Env : Type}
    (allowed : Alternative Atom Env → Prop) (entry : Env) (atom : Atom) : Prop :=
  ∃ alternative, allowed alternative ∧
    ∃ witness : alternative.body.Witness,
      (alternative.body.compile entry witness).head = atom ∧
      SpecTecEval.Prefix (alternative.body.premises false
        (SpecTecWFS.Holds (ProgramOf allowed entry))
        (SpecTecWFS.Fails (ProgramOf allowed entry)) entry witness)

/-- Membership elimination, head transport and reconstruction of source-order
    premises happen here, once for every SCC and public relation. -/
theorem ProgramOf.holds_cases {Atom : Type uPlan} {Env : Type}
    {allowed : Alternative Atom Env → Prop} {entry : Env} {atom : Atom}
    (proof : SpecTecWFS.Holds (ProgramOf allowed entry) atom) :
    Cases allowed entry atom := by
  obtain ⟨rule, ⟨alternative, member, witness, compiled⟩, head,
      side, positive, negative⟩ := SpecTecWFS.Holds.cases proof
  subst rule
  exact ⟨alternative, member, witness, head,
    (alternative.body.premises_iff _ _ entry witness).mpr
      ⟨side, positive, negative⟩⟩

/-- A typed plan denotes the WFS rules compiled from its intermediate values. -/
def Rules {Atom : Type uPlan} {Env : Type}
    (plan : Plan Atom Env) (entry : Env) : SpecTecWFS.Program Atom :=
  fun rule => ∃ witness : plan.Witness, plan.compile entry witness = rule

def Program {Atom : Type uPlan} {Env : Type}
    (alternatives : List (Alternative Atom Env)) (entry : Env) :
    SpecTecWFS.Program Atom :=
  fun rule => ∃ alternative, alternative ∈ alternatives ∧
    Rules alternative.body entry rule

theorem Program.compiled_iff {Atom : Type uPlan} {Env : Type}
    {alternatives : List (Alternative Atom Env)} {entry : Env}
    {rule : SpecTecWFS.Rule Atom} :
    Program alternatives entry rule ↔
      ∃ alternative, alternative ∈ alternatives ∧
        ∃ witness : alternative.body.Witness,
          alternative.body.compile entry witness = rule :=
  Iff.rfl

theorem Program.holds_cases {Atom : Type uPlan} {Env : Type}
    {alternatives : List (Alternative Atom Env)} {entry : Env}
    {atom : Atom} (proof : SpecTecWFS.Holds (Program alternatives entry) atom) :
    ∃ alternative, alternative ∈ alternatives ∧
      ∃ witness : alternative.body.Witness,
        let rule := alternative.body.compile entry witness
        rule.head = atom ∧ rule.side ∧
        SpecTecWFS.All (SpecTecWFS.Holds (Program alternatives entry))
          rule.positive ∧
        SpecTecWFS.All (SpecTecWFS.Fails (Program alternatives entry))
          rule.negative := by
  obtain ⟨rule, ⟨alternative, member, witness, compiled⟩, head, side,
      positive, negative⟩ := SpecTecWFS.Holds.cases proof
  subst rule
  exact ⟨alternative, member, witness, head, side, positive, negative⟩

/-- A finite success tree stores the chosen rule (and therefore its typed plan
    witness), proofs at opaque side/negative boundaries, and untrusted child
    records. The checker compares every child with its required positive atom. -/
inductive SuccessCertificate {Atom : Type uPlan}
    (program : SpecTecWFS.Program Atom) : Type (max uPlan 1) where
  | node (rule : SpecTecWFS.Rule Atom) (member : program rule)
      (side : rule.side)
      (negative : SpecTecWFS.All (SpecTecWFS.Fails program) rule.negative)
      (children : List (SuccessCertificate program)) :
      SuccessCertificate program

def childrenMatch {Atom : Type uPlan} [DecidableEq Atom]
    {program : SpecTecWFS.Program Atom}
    (lookup : SuccessCertificate program → Option Atom) :
    List (SuccessCertificate program) → List Atom → Bool
  | [], [] => true
  | child :: children, atom :: atoms =>
      if lookup child = some atom then
        childrenMatch lookup children atoms
      else false
  | _, _ => false

/-- The fuel bounds certificate depth. A wrong child, missing child, or
    mismatched child atom returns `none`. -/
def checkSuccess {Atom : Type uPlan} [DecidableEq Atom]
    {program : SpecTecWFS.Program Atom} :
    Nat → SuccessCertificate program → Option Atom
  | 0, _ => none
  | fuel + 1, .node rule _ _ _ children =>
      if childrenMatch (checkSuccess fuel) children rule.positive then
        some rule.head
      else none

theorem childrenMatch_sound {Atom : Type uPlan} [DecidableEq Atom]
    {program : SpecTecWFS.Program Atom}
    {lookup : SuccessCertificate program → Option Atom}
    (sound : ∀ certificate atom, lookup certificate = some atom →
      SpecTecWFS.Holds program atom) :
    ∀ children atoms, childrenMatch lookup children atoms = true →
      SpecTecWFS.All (SpecTecWFS.Holds program) atoms := by
  intro children
  induction children with
  | nil =>
      intro atoms accepted
      cases atoms with
      | nil => trivial
      | cons _ _ => simp [childrenMatch] at accepted
  | cons child children ih =>
      intro atoms accepted
      cases atoms with
      | nil => simp [childrenMatch] at accepted
      | cons atom atoms =>
          by_cases matched : lookup child = some atom
          · simp [childrenMatch, matched] at accepted
            exact ⟨sound child atom matched, ih atoms accepted⟩
          · simp [childrenMatch, matched] at accepted

theorem checkSuccess_sound {Atom : Type uPlan} [DecidableEq Atom]
    {program : SpecTecWFS.Program Atom} (fuel : Nat) :
    ∀ (certificate : SuccessCertificate program) (atom : Atom),
      checkSuccess fuel certificate = some atom →
      SpecTecWFS.Holds program atom := by
  induction fuel with
  | zero =>
      intro certificate atom accepted
      simp [checkSuccess] at accepted
  | succ fuel ih =>
      intro certificate atom accepted
      cases certificate with
      | node rule member side negative children =>
          by_cases matched :
              childrenMatch (checkSuccess fuel) children rule.positive = true
          · simp [checkSuccess, matched] at accepted
            subst atom
            exact SpecTecWFS.Holds.rule rule member side
              (childrenMatch_sound ih children rule.positive matched) negative
          · simp [checkSuccess, matched] at accepted

/-- A partial comparison is sufficient: `false` may mean unknown, while
    `true` must be backed by equality. This permits atoms with opaque extern
    function fields that have no `DecidableEq` instance. -/
def childrenMatchWith {Atom : Type uPlan}
    {program : SpecTecWFS.Program Atom}
    (same : Atom → Atom → Bool)
    (lookup : SuccessCertificate program → Option Atom) :
    List (SuccessCertificate program) → List Atom → Bool
  | [], [] => true
  | child :: children, atom :: atoms =>
      match lookup child with
      | none => false
      | some output =>
          if same output atom then
            childrenMatchWith same lookup children atoms
          else false
  | _, _ => false

def checkSuccessWith {Atom : Type uPlan}
    {program : SpecTecWFS.Program Atom} (same : Atom → Atom → Bool) :
    Nat → SuccessCertificate program → Option Atom
  | 0, _ => none
  | fuel + 1, .node rule _ _ _ children =>
      if childrenMatchWith same (checkSuccessWith same fuel)
          children rule.positive then
        some rule.head
      else none

theorem childrenMatchWith_sound {Atom : Type uPlan}
    {program : SpecTecWFS.Program Atom}
    {same : Atom → Atom → Bool}
    (sameSound : ∀ left right, same left right = true → left = right)
    {lookup : SuccessCertificate program → Option Atom}
    (lookupSound : ∀ certificate atom, lookup certificate = some atom →
      SpecTecWFS.Holds program atom) :
    ∀ children atoms,
      childrenMatchWith same lookup children atoms = true →
        SpecTecWFS.All (SpecTecWFS.Holds program) atoms := by
  intro children
  induction children with
  | nil =>
      intro atoms accepted
      cases atoms with
      | nil => trivial
      | cons _ _ => simp [childrenMatchWith] at accepted
  | cons child children ih =>
      intro atoms accepted
      cases atoms with
      | nil => simp [childrenMatchWith] at accepted
      | cons atom atoms =>
          cases found : lookup child with
          | none => simp [childrenMatchWith, found] at accepted
          | some output =>
              by_cases matched : same output atom = true
              · simp [childrenMatchWith, found, matched] at accepted
                have equal := sameSound output atom matched
                subst atom
                exact ⟨lookupSound child output found, ih atoms accepted⟩
              · simp [childrenMatchWith, found, matched] at accepted

theorem checkSuccessWith_sound {Atom : Type uPlan}
    {program : SpecTecWFS.Program Atom}
    (same : Atom → Atom → Bool)
    (sameSound : ∀ left right, same left right = true → left = right)
    (fuel : Nat) :
    ∀ (certificate : SuccessCertificate program) (atom : Atom),
      checkSuccessWith same fuel certificate = some atom →
        SpecTecWFS.Holds program atom := by
  induction fuel with
  | zero =>
      intro certificate atom accepted
      simp [checkSuccessWith] at accepted
  | succ fuel ih =>
      intro certificate atom accepted
      cases certificate with
      | node rule member side negative children =>
          by_cases matched : childrenMatchWith same
              (checkSuccessWith same fuel) children rule.positive = true
          · simp [checkSuccessWith, matched] at accepted
            subst atom
            exact SpecTecWFS.Holds.rule rule member side
              (childrenMatchWith_sound sameSound ih children
                rule.positive matched) negative
          · simp [checkSuccessWith, matched] at accepted

end SpecTecPlan
|lean}
