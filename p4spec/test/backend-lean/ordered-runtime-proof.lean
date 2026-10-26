namespace SpecTecExecution

def testProgram : Nat → Action Nat := fun _ => .unmatch

def testClauses (n : Nat) : List (Action Nat) :=
  [.unmatch, .pure (n + 1), .abort "late"]

example : Eval testProgram (tryClauses (testClauses 6)) 0 (.success (.of (7 : Nat))) 0 := by
  apply tryClauses_cons_unmatch Eval.unmatch
  apply tryClauses_cons_success
  exact Eval.pure 7

example : ¬ Eval testProgram (tryClauses (testClauses 6)) 0 (.success (.of (8 : Nat))) 0 := by
  intro h
  obtain ⟨_, known⟩ : ∃ a : Eval testProgram (tryClauses (testClauses 6)) 0
      (.success (.of (7 : Nat))) 0, Functional testProgram a :=
    ⟨tryClauses_cons_unmatch Eval.unmatch (tryClauses_cons_success (Eval.pure 7)),
      .orElse_unmatch .unmatch (.orElse_success (.pure 7))⟩
  have eq := eval_deterministic known h
  cases eq.1

example : Eval testProgram
    (tryClauses [.pure (none : Option Nat)]) 0
    (.success (.of (none : Option Nat))) 0 := tryClauses_cons_success (Eval.pure none)

example : Eval testProgram
    (tryClauses [.abort "stop", .pure 1]) 0
    (.abort "stop") 0 := tryClauses_cons_abort (Eval.abort "stop")

example : Eval testProgram (tryClauses ([] : List (Action Nat))) 0
    .unmatch 0 := Eval.unmatch

end SpecTecExecution

namespace SpecTecExecution

def loopProgram : Unit → Action Unit := fun _ => .call ()

theorem loop_has_no_finite_execution {plan : Action Unit} {outcome : Outcome Value}
    {start final : Nat} (h : Eval loopProgram plan start outcome final) : plan = .call () → False := by
  induction h with
  | call _ ih => intro e; cases e; exact ih rfl
  | _ => intro e; cases e

-- Divergence supplies neither a successful result nor an unmatch derivation.
example : ¬ Eval loopProgram
    (tryClauses [.call (), .pure (9 : Nat)]) 0
    (.success (.of (9 : Nat))) 0 := by
  intro h
  cases h with
  | orElse_success h => exact loop_has_no_finite_execution h rfl
  | orElse_unmatch h _ => exact loop_has_no_finite_execution h rfl

inductive DataResult where | FAIL
example : Eval testProgram (.pure DataResult.FAIL) 0 (.success (.of DataResult.FAIL)) 0 := .pure _
example : Eval testProgram (.pure false) 0 (.success (.of false)) 0 := .pure _

example : Eval testProgram
    (tryClauses [.guard False, .unmatch]) 0 .unmatch 0 :=
  (tryClauses_unmatch_iff _ _ _).mpr
    (.cons (.guard_false (fun h => h)) (.cons .unmatch .nil))

end SpecTecExecution
