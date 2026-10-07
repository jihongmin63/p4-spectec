let source = {lean|
set_option autoImplicit false

universe u₁ u₂ u₃ u₄ u₅

namespace SpecTecEval

inductive Outcome (Output : Type u₁) (Error : Type u₂) (Feature : Type u₃) where
  | success : Output → Outcome Output Error Feature
  | ruleFailure : Outcome Output Error Feature
  | abort : Error → Outcome Output Error Feature
  | unsupported : Feature → Outcome Output Error Feature
  | timeout : Outcome Output Error Feature
  | undetermined : Outcome Output Error Feature

/-- Successful premises in their original left-to-right order. -/
def Prefix : List Prop → Prop
  | [] => True
  | premise :: rest => premise ∧ Prefix rest

theorem Prefix.get {premises : List Prop} (proof : Prefix premises)
    {position : Nat} {premise : Prop}
    (atPosition : premises[position]? = some premise) : premise := by
  induction premises generalizing position with
  | nil => simp at atPosition
  | cons head tail induction =>
      cases position with
      | zero =>
          cases Option.some.inj atPosition
          exact proof.1
      | succ position =>
          exact induction proof.2 (by simpa using atPosition)

/-- The first recoverable failure of one rule.  Earlier successes are shared
    through `prefix`; they are not copied into a constructor for every failure
    position. -/
inductive RuleFailure (premises : List Prop) (recoverable : List Nat) : Prop where
  | at (position : Nat) (failed : Prop)
      (atPosition : premises[position]? = some failed)
      (mayContinue : position ∈ recoverable)
      (priorSuccess : Prefix (premises.take position))
      (refuted : failed → False) : RuleFailure premises recoverable

inductive SelectionPolicy where
  | ordered
  | nondeterministic

/-- The relation-specific data and public soundness certificate for one source
    rule.  Dependent rule binders are hidden in `Witness`. -/
structure EvalRulePlan (Input : Type u₁) (Output : Type u₂)
    (Public : Input → Output → Prop) where
  Witness : Type u₃
  accepts : Witness → Input → Output → Prop
  premises : Witness → List Prop
  recoverable : List Nat
  publicSound : ∀ witness input output, accepts witness input output →
    Prefix (premises witness) → Public input output

def EvalRulePlan.Succeeds {Input : Type u₁} {Output : Type u₂}
    {Public : Input → Output → Prop}
    (plan : EvalRulePlan Input Output Public)
    (evalInput : Input) (evalOutput : Output) : Prop :=
  ∃ witness, plan.accepts witness evalInput evalOutput ∧
    Prefix (plan.premises witness)

def EvalRulePlan.Fails {Input : Type u₁} {Output : Type u₂}
    {Public : Input → Output → Prop}
    (plan : EvalRulePlan Input Output Public) (evalInput : Input) : Prop :=
  ∀ (evalOutput : Output) (witness : plan.Witness),
    ¬ plan.accepts witness evalInput evalOutput ∨
      RuleFailure (plan.premises witness) plan.recoverable

theorem EvalRulePlan.Succeeds.sound {Input : Type u₁} {Output : Type u₂}
    {Public : Input → Output → Prop}
    {plan : EvalRulePlan Input Output Public} {evalInput : Input}
    {evalOutput : Output} (proof : plan.Succeeds evalInput evalOutput) :
    Public evalInput evalOutput := by
  rcases proof with ⟨witness, matched, premises⟩
  exact plan.publicSound witness evalInput evalOutput matched premises

/-- A certificate selecting one rule from a source-ordered plan list. -/
inductive Selected {Input : Type u₁} {Output : Type u₂}
    {Public : Input → Output → Prop} :
    SelectionPolicy → List (EvalRulePlan Input Output Public) →
      Input → Output → Prop where
  | here {policy plan rest input output} :
      plan.Succeeds input output →
      Selected policy (plan :: rest) input output
  | laterNondeterministic {plan rest input output} :
      Selected .nondeterministic rest input output →
      Selected .nondeterministic (plan :: rest) input output
  | laterOrdered {plan rest input output} :
      plan.Fails input → Selected .ordered rest input output →
      Selected .ordered (plan :: rest) input output

theorem Selected.sound {Input : Type u₁} {Output : Type u₂}
    {Public : Input → Output → Prop} {policy plans input output}
    (proof : @Selected Input Output Public policy plans input output) :
    Public input output := by
  induction proof with
  | here success => exact success.sound
  | laterNondeterministic _ sound => exact sound
  | laterOrdered _ _ sound => exact sound

/-- Every rule has a recoverable failure certificate for this input. -/
inductive AllFailed {Input : Type u₁} {Output : Type u₂}
    {Public : Input → Output → Prop} :
    List (EvalRulePlan Input Output Public) → Input → Prop where
  | nil (input) : AllFailed [] input
  | cons {plan rest input} :
      plan.Fails input → AllFailed rest input → AllFailed (plan :: rest) input

/-- Relation-specific rule data interpreted by the common evaluator. -/
structure Evaluator (Input : Type u₁) (Output : Type u₂)
    (Public : Input → Output → Prop) where
  policy : SelectionPolicy
  rules : List (EvalRulePlan.{u₁, u₂, u₃} Input Output Public)
  undetermined : Input → Prop

def Evaluator.Selected {Input : Type u₁} {Output : Type u₂}
    {Public : Input → Output → Prop}
    (evaluator : Evaluator Input Output Public) : Input → Output → Prop :=
  SpecTecEval.Selected evaluator.policy evaluator.rules

def Evaluator.AllFailed {Input : Type u₁} {Output : Type u₂}
    {Public : Input → Output → Prop}
    (evaluator : Evaluator Input Output Public) : Input → Prop :=
  SpecTecEval.AllFailed evaluator.rules

theorem Evaluator.selected_sound {Input : Type u₁} {Output : Type u₂}
    {Public : Input → Output → Prop}
    {evaluator : Evaluator Input Output Public} {input output}
    (proof : evaluator.Selected input output) : Public input output :=
  proof.sound

/-- Failure of a call whose output was not fixed is universal over candidates. -/
structure OutputSearchFailure (Output : Type u₁) (succeeds : Output → Prop) where
  noSuccess : ∀ output, ¬ succeeds output

class Boundary (Input : Type u₁) (Error : Type u₂) (Feature : Type u₃) where
  aborts : Input → Error → Prop
  unsupported : Input → Feature → Prop

inductive AlternativeResult (Output : Type u₁) (Error : Type u₂)
    (Feature : Type u₃) where
  | success : Output → AlternativeResult Output Error Feature
  | recoverableFailure : AlternativeResult Output Error Feature
  | abort : Error → AlternativeResult Output Error Feature
  | unsupported : Feature → AlternativeResult Output Error Feature
  | timeout : AlternativeResult Output Error Feature
  | undetermined : AlternativeResult Output Error Feature

/-- Only interpreter `Unmatch` permits the next source alternative. -/
def MayContinue {Output : Type u₁} {Error : Type u₂} {Feature : Type u₃} :
    AlternativeResult Output Error Feature → Prop
  | .recoverableFailure => True
  | _ => False

theorem abort_stops {Output : Type u₁} {Error : Type u₂} {Feature : Type u₃}
    (error : Error) :
    ¬ MayContinue (AlternativeResult.abort error :
      AlternativeResult Output Error Feature) := by
  intro proof
  exact proof

theorem unsupported_stops {Output : Type u₁} {Error : Type u₂} {Feature : Type u₃}
    (feature : Feature) :
    ¬ MayContinue (AlternativeResult.unsupported feature :
      AlternativeResult Output Error Feature) := by
  intro proof
  exact proof

theorem timeout_stops {Output : Type u₁} {Error : Type u₂} {Feature : Type u₃} :
    ¬ MayContinue (AlternativeResult.timeout :
      AlternativeResult Output Error Feature) := by
  intro proof
  exact proof

inductive Evaluation {Input : Type u₁} {Output : Type u₂}
    {Error : Type u₃} {Feature : Type u₄}
    (selectedSucceeds : Input → Output → Prop)
    (publicSucceeds : Input → Output → Prop)
    (allRulesFailed : Input → Prop)
    (isUndetermined : Input → Prop)
    [boundary : Boundary Input Error Feature] :
    Nat → Input → Outcome Output Error Feature → Prop where
  | success {fuel input output} :
      selectedSucceeds input output →
      Evaluation selectedSucceeds publicSucceeds allRulesFailed isUndetermined
        (fuel + 1) input (.success output)
  | ruleFailure {fuel input} :
      allRulesFailed input →
      OutputSearchFailure Output (publicSucceeds input) →
      Evaluation selectedSucceeds publicSucceeds allRulesFailed isUndetermined
        (fuel + 1) input .ruleFailure
  | abort {fuel input error} :
      boundary.aborts input error →
      Evaluation selectedSucceeds publicSucceeds allRulesFailed isUndetermined
        (fuel + 1) input (.abort error)
  | unsupported {fuel input feature} :
      boundary.unsupported input feature →
      Evaluation selectedSucceeds publicSucceeds allRulesFailed isUndetermined
        (fuel + 1) input (.unsupported feature)
  | timeout (input : Input) :
      Evaluation selectedSucceeds publicSucceeds allRulesFailed isUndetermined 0 input .timeout
  | undetermined {fuel input} :
      isUndetermined input →
      Evaluation selectedSucceeds publicSucceeds allRulesFailed isUndetermined
        (fuel + 1) input .undetermined

abbrev Evaluator.Evaluation {Input : Type u₁} {Output : Type u₂}
    {Public : Input → Output → Prop} {Error : Type u₄} {Feature : Type u₅}
    (evaluator : Evaluator Input Output Public)
    [Boundary Input Error Feature] :
    Nat → Input → Outcome Output Error Feature → Prop :=
  SpecTecEval.Evaluation evaluator.Selected Public evaluator.AllFailed
    evaluator.undetermined

theorem Evaluator.success_sound {Input : Type u₁} {Output : Type u₂}
    {Public : Input → Output → Prop} {Error : Type u₄} {Feature : Type u₅}
    {evaluator : Evaluator Input Output Public} [Boundary Input Error Feature]
    {fuel input output}
    (proof : evaluator.Evaluation fuel input
      (.success output : Outcome Output Error Feature)) :
    Public input output := by
  cases proof with
  | success selected => exact selected.sound

theorem Evaluator.ruleFailure_sound {Input : Type u₁} {Output : Type u₂}
    {Public : Input → Output → Prop} {Error : Type u₄} {Feature : Type u₅}
    {evaluator : Evaluator Input Output Public} [Boundary Input Error Feature]
    {fuel input}
    (proof : evaluator.Evaluation fuel input
      (.ruleFailure : Outcome Output Error Feature)) :
    ∀ output, ¬ Public input output := by
  cases proof with
  | ruleFailure _ search => exact search.noSuccess

theorem Evaluator.timeout {Input : Type u₁} {Output : Type u₂}
    {Public : Input → Output → Prop} {Error : Type u₄} {Feature : Type u₅}
    (evaluator : Evaluator Input Output Public) [Boundary Input Error Feature]
    (input : Input) :
    evaluator.Evaluation 0 input (.timeout : Outcome Output Error Feature) :=
  SpecTecEval.Evaluation.timeout input

theorem Evaluation.success_sound {Input : Type u₁} {Output : Type u₂}
    {Error : Type u₃} {Feature : Type u₄}
    {selectedSucceeds publicSucceeds : Input → Output → Prop}
    {allRulesFailed : Input → Prop}
    {isUndetermined : Input → Prop} [Boundary Input Error Feature]
    {fuel input output}
    (proof : Evaluation selectedSucceeds publicSucceeds allRulesFailed isUndetermined
      fuel input (.success output : Outcome Output Error Feature)) :
    selectedSucceeds input output := by
  cases proof with
  | success sound => exact sound

/-- Rejection is available only from an explicit universal output-search
    certificate, never from one successful or failed candidate. -/
theorem Evaluation.ruleFailure_sound {Input : Type u₁} {Output : Type u₂}
    {Error : Type u₃} {Feature : Type u₄}
    {selectedSucceeds publicSucceeds : Input → Output → Prop}
    {allRulesFailed : Input → Prop}
    {isUndetermined : Input → Prop} [Boundary Input Error Feature]
    {fuel input}
    (proof : Evaluation selectedSucceeds publicSucceeds allRulesFailed isUndetermined
      fuel input (.ruleFailure : Outcome Output Error Feature)) :
    ∀ output, ¬ publicSucceeds input output := by
  cases proof with
  | ruleFailure _ search => exact search.noSuccess

theorem Evaluation.abort_sound {Input : Type u₁} {Output : Type u₂}
    {Error : Type u₃} {Feature : Type u₄}
    {selectedSucceeds publicSucceeds : Input → Output → Prop}
    {allRulesFailed isUndetermined : Input → Prop}
    [boundary : Boundary Input Error Feature]
    {fuel input error}
    (proof : Evaluation selectedSucceeds publicSucceeds allRulesFailed
      isUndetermined fuel input (.abort error : Outcome Output Error Feature)) :
    boundary.aborts input error := by
  cases proof with
  | abort boundaryProof => exact boundaryProof

theorem Evaluation.unsupported_sound {Input : Type u₁} {Output : Type u₂}
    {Error : Type u₃} {Feature : Type u₄}
    {selectedSucceeds publicSucceeds : Input → Output → Prop}
    {allRulesFailed isUndetermined : Input → Prop}
    [boundary : Boundary Input Error Feature]
    {fuel input feature}
    (proof : Evaluation selectedSucceeds publicSucceeds allRulesFailed
      isUndetermined fuel input
        (.unsupported feature : Outcome Output Error Feature)) :
    boundary.unsupported input feature := by
  cases proof with
  | unsupported boundaryProof => exact boundaryProof

theorem Evaluation.timeout_fuel {Input : Type u₁} {Output : Type u₂}
    {Error : Type u₃} {Feature : Type u₄}
    {selectedSucceeds publicSucceeds : Input → Output → Prop}
    {allRulesFailed isUndetermined : Input → Prop}
    [Boundary Input Error Feature]
    {fuel input}
    (proof : Evaluation selectedSucceeds publicSucceeds allRulesFailed
      isUndetermined fuel input (.timeout : Outcome Output Error Feature)) :
    fuel = 0 := by
  cases proof
  rfl

theorem Evaluation.undetermined_sound {Input : Type u₁} {Output : Type u₂}
    {Error : Type u₃} {Feature : Type u₄}
    {selectedSucceeds publicSucceeds : Input → Output → Prop}
    {allRulesFailed isUndetermined : Input → Prop}
    [Boundary Input Error Feature]
    {fuel input}
    (proof : Evaluation selectedSucceeds publicSucceeds allRulesFailed
      isUndetermined fuel input (.undetermined : Outcome Output Error Feature)) :
    isUndetermined input := by
  cases proof with
  | undetermined evidence => exact evidence

end SpecTecEval
|lean}
