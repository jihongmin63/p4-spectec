/- Typed, executable refinement of SpecTecExecution. Embedded after that library. -/
set_option autoImplicit false

namespace SpecTecExecution

universe u

def Outcome.pack {α : Type} : Outcome α → Outcome Value
  | .success value => .success (.of value)
  | .unmatch => .unmatch
  | .abort message => .abort message

/-- Keeping the output index makes bind executable without dynamic casts. -/
inductive ExecutableAction (Call : Type → Type u) : Type → Type (max u 1) where
  | pure {α : Type} (value : α) : ExecutableAction Call α
  | unmatch {α : Type} : ExecutableAction Call α
  | abort {α : Type} (message : String) : ExecutableAction Call α
  | freshId : ExecutableAction Call String
  | call {α : Type} (request : Call α) : ExecutableAction Call α
  | choose (α : Type) (allowed : α → Prop) : ExecutableAction Call α
  | guard (condition : Prop) [Decidable condition] : ExecutableAction Call Unit
  | bind {α β : Type} (plan : ExecutableAction Call α)
      (next : α → ExecutableAction Call β) : ExecutableAction Call β
  | orElse {α : Type} (plan : ExecutableAction Call α)
      (next : Unit → ExecutableAction Call α) : ExecutableAction Call α
  | notHold {α : Type} (plan : ExecutableAction Call α) : ExecutableAction Call Unit

def ExecutableAction.erase {Call : Type → Type u} {α : Type} :
    ExecutableAction Call α → Action (Sigma Call)
  | .pure value => .pure value
  | .unmatch => .unmatch
  | .abort message => .abort message
  | .freshId => .freshId
  | .call request => .call ⟨_, request⟩
  | .choose α allowed => .choose α allowed
  | @ExecutableAction.guard _ condition _ => .guard condition
  | .bind plan next => .bind plan.erase (fun value => (next value).erase)
  | .orElse plan next => .orElse plan.erase (fun arg => (next arg).erase)
  | .notHold plan => .notHold plan.erase

def ExecutableAction.require {Call : Type → Type u} (condition : Prop)
    [Decidable condition] (message : String) : ExecutableAction Call Unit :=
  .orElse (.guard condition) (fun () => .abort message)

def ExecutableAction.tryClauses {Call : Type → Type u} {α : Type}
    (clauses : List (ExecutableAction Call α)) : ExecutableAction Call α :=
  match clauses with
  | [] => .unmatch
  | clause :: rest => .orElse clause (fun () => tryClauses rest)

structure ExecutableProgram (Call : Type → Type u) where
  body : {α : Type} → Call α → ExecutableAction Call α

def ExecutableProgram.erase {Call : Type → Type u} (program : ExecutableProgram Call) :
    Sigma Call → Action (Sigma Call) :=
  fun request => (program.body request.2).erase

/-- Only `done` describes a semantic outcome. Neither incomplete result is unmatch. -/
inductive RunResult (α : Type) where
  | done (outcome : Outcome α) (supply : Nat)
  | outOfFuel
  | unsupportedChoice
  deriving DecidableEq, Repr

/-- Fuel bounds derivation height. Each recursive child receives one less fuel. -/
def runEval {Call : Type → Type u} (program : ExecutableProgram Call) :
    Nat → {α : Type} → ExecutableAction Call α → Nat → RunResult α
  | 0, _, _, _ => .outOfFuel
  | fuel + 1, _, plan, supply =>
    match plan with
    | .pure value => .done (.success value) supply
    | .unmatch => .done .unmatch supply
    | .abort message => .done (.abort message) supply
    | .freshId => .done (.success (freshName supply)) (supply + 1)
    | .call request => runEval program fuel (program.body request) supply
    | .choose _ _ => .unsupportedChoice
    | @ExecutableAction.guard _ condition dec =>
      letI := dec
      if condition then .done (.success ()) supply else .done .unmatch supply
    | .bind plan next => match runEval program fuel plan supply with
      | .done (.success value) middle => runEval program fuel (next value) middle
      | .done .unmatch final => .done .unmatch final
      | .done (.abort message) final => .done (.abort message) final
      | .outOfFuel => .outOfFuel
      | .unsupportedChoice => .unsupportedChoice
    | .orElse plan next => match runEval program fuel plan supply with
      | .done .unmatch final => runEval program fuel (next ()) final
      | .done (.success value) final => .done (.success value) final
      | .done (.abort message) final => .done (.abort message) final
      | .outOfFuel => .outOfFuel
      | .unsupportedChoice => .unsupportedChoice
    | .notHold plan => match runEval program fuel plan supply with
      | .done .unmatch final => .done (.success ()) final
      | .done (.success _) final => .done .unmatch final
      | .done (.abort message) final => .done (.abort message) final
      | .outOfFuel => .outOfFuel
      | .unsupportedChoice => .unsupportedChoice

theorem runEval_sound {Call : Type → Type u} (program : ExecutableProgram Call)
    (fuel : Nat) {α : Type}
    (plan : ExecutableAction Call α) (start : Nat) (outcome : Outcome α) (final : Nat)
    (h : runEval program fuel plan start = .done outcome final) :
    Eval program.erase plan.erase start outcome.pack final := by
  induction fuel generalizing α plan start outcome final with
  | zero => cases h
  | succ fuel ih =>
    cases plan with
    | pure value => cases h; exact .pure value
    | unmatch => cases h; exact .unmatch
    | abort message => cases h; exact .abort message
    | freshId => cases h; exact .freshId
    | call request => exact .call (ih _ _ _ _ h)
    | choose α allowed => cases h
    | guard condition =>
      simp only [runEval] at h
      split at h
      · cases h; exact .guard_true ‹condition›
      · cases h; exact .guard_false ‹¬ condition›
    | bind plan next =>
      simp only [runEval] at h
      cases hr : runEval program fuel plan start with
      | outOfFuel => simp [hr] at h
      | unsupportedChoice => simp [hr] at h
      | done first middle =>
        cases first with
        | success value =>
          simp only [hr] at h
          exact .bind_success (ih _ _ _ _ hr) (ih _ _ _ _ h)
        | unmatch =>
          simp only [hr] at h; cases h
          exact .bind_unmatch (ih _ _ _ _ hr)
        | abort message =>
          simp only [hr] at h; cases h
          exact .bind_abort (ih _ _ _ _ hr)
    | orElse plan next =>
      simp only [runEval] at h
      cases hr : runEval program fuel plan start with
      | outOfFuel => simp [hr] at h
      | unsupportedChoice => simp [hr] at h
      | done first middle =>
        cases first with
        | success value =>
          simp only [hr] at h; cases h
          exact .orElse_success (ih _ _ _ _ hr)
        | unmatch =>
          simp only [hr] at h
          exact .orElse_unmatch (ih _ _ _ _ hr) (ih _ _ _ _ h)
        | abort message =>
          simp only [hr] at h; cases h
          exact .orElse_abort (ih _ _ _ _ hr)
    | notHold plan =>
      simp only [runEval] at h
      cases hr : runEval program fuel plan start with
      | outOfFuel => simp [hr] at h
      | unsupportedChoice => simp [hr] at h
      | done first middle =>
        cases first with
        | success value =>
          simp only [hr] at h; cases h
          exact .notHold_unmatch (ih _ _ _ _ hr)
        | unmatch =>
          simp only [hr] at h; cases h
          exact .notHold_success (ih _ _ _ _ hr)
        | abort message =>
          simp only [hr] at h; cases h
          exact .notHold_abort (ih _ _ _ _ hr)

/-- A completed computation is unchanged by increasing its fuel. -/
theorem runEval_mono {Call : Type → Type u} (program : ExecutableProgram Call)
    {fuel more : Nat} (le : fuel ≤ more)
    {α : Type} (plan : ExecutableAction Call α) (start : Nat)
    (outcome : Outcome α) (final : Nat)
    (h : runEval program fuel plan start = .done outcome final) :
    runEval program more plan start = .done outcome final := by
  induction fuel generalizing more α plan start outcome final with
  | zero => cases h
  | succ fuel ih =>
    cases more with
    | zero => cases le
    | succ more =>
      have le' := Nat.le_of_succ_le_succ le
      cases plan with
      | pure value | unmatch | abort message | freshId | choose α allowed | guard condition =>
        exact h
      | call request => exact ih le' _ _ _ _ h
      | bind plan next =>
        simp only [runEval] at h ⊢
        cases hr : runEval program fuel plan start with
        | outOfFuel => simp [hr] at h
        | unsupportedChoice => simp [hr] at h
        | done first middle =>
          rw [ih le' _ _ _ _ hr]
          cases first with
          | success value => exact ih le' _ _ _ _ (by simpa only [hr] using h)
          | unmatch | abort message => simpa only [hr] using h
      | orElse plan next =>
        simp only [runEval] at h ⊢
        cases hr : runEval program fuel plan start with
        | outOfFuel => simp [hr] at h
        | unsupportedChoice => simp [hr] at h
        | done first middle =>
          rw [ih le' _ _ _ _ hr]
          cases first with
          | unmatch => exact ih le' _ _ _ _ (by simpa only [hr] using h)
          | success value | abort message => simpa only [hr] using h
      | notHold plan =>
        simp only [runEval] at h ⊢
        cases hr : runEval program fuel plan start with
        | outOfFuel => simp [hr] at h
        | unsupportedChoice => simp [hr] at h
        | done first middle =>
          rw [ih le' _ _ _ _ hr]
          simpa only [hr] using h

end SpecTecExecution
