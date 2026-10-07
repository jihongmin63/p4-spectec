let source = {lean|
set_option autoImplicit false

universe u₁ u₂ u₃ u₄

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

end SpecTecEval
|lean}
