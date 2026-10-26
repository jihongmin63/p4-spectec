namespace SpecTecExecution.RunEvalTests
open SpecTecExecution

inductive Request : Type → Type where
  | countdown (n : Nat) : Request Nat
  | loop : Request Nat
  | external : Request Nat

def program : ExecutableProgram Request where
  body := fun request => match request with
    | .countdown 0 => .pure 0
    | .countdown (n + 1) => .bind (.call (.countdown n)) (fun x => .pure (x + 1))
    | .loop => .call .loop
    | .external => .choose Nat (fun n => n = 42)

def freshPair : ExecutableAction Request (String × String) :=
  .bind .freshId (fun a => .bind .freshId (fun b => .pure (a, b)))

def failedFresh : ExecutableAction Request String :=
  .bind .freshId (fun _ => .unmatch)

def retryFresh : ExecutableAction Request String :=
  .orElse failedFresh (fun () => .freshId)

def allFailedFresh : ExecutableAction Request String :=
  .tryClauses [failedFresh, failedFresh]

def abortFresh : ExecutableAction Request String :=
  .orElse (.bind .freshId (fun _ => .abort "stop")) (fun () => .pure "wrong")

-- Native evaluation covers plans without extern choices.
#guard (runEval program 0 (.pure (7 : Nat)) 3 == .outOfFuel)
#guard (runEval program 1 (.pure (7 : Nat)) 3 == .done (.success 7) 3)
#guard (runEval program 8 freshPair 4 == .done (.success ("FRESH__4", "FRESH__5")) 6)
#guard (runEval program 8 retryFresh 4 == .done (.success "FRESH__5") 6)
#guard (runEval program 8 allFailedFresh 4 == .done .unmatch 6)
#guard (runEval program 12 (.orElse allFailedFresh (fun () => .freshId)) 4 ==
  .done (.success "FRESH__6") 7)
#guard (runEval program 8 abortFresh 4 == .done (.abort "stop") 5)
#guard (runEval program 8 (.notHold failedFresh) 4 == .done (.success ()) 5)
#guard (runEval program 8 (.notHold freshPair) 4 == .done .unmatch 6)
#guard (runEval program 8 (.notHold abortFresh) 4 == .done (.abort "stop") 5)
#guard (runEval program 30 (.call (.countdown 5)) 4 == .done (.success 5) 4)
#guard (runEval program 1 (.call (.countdown 0)) 4 == .outOfFuel)
#guard (runEval program 2 (.call (.countdown 0)) 4 == .done (.success 0) 4)
#guard (runEval program 30 (.call .external) 4 == .unsupportedChoice)
#guard (runEval program 30 (.orElse (.call .loop) (fun () => .pure 9)) 4 == .outOfFuel)
#guard (runEval program 4 (.pure false) 0 == .done (.success false) 0)
#guard (runEval program 4 (.pure (none : Option Nat)) 0 == .done (.success none) 0)
#guard (runEval program 4 (.notHold (.pure false)) 0 == .done .unmatch 0)
#guard (runEval program 4 (.notHold (.pure (none : Option Nat))) 0 == .done .unmatch 0)
#guard (runEval program 4 (.guard (1 < 2)) 0 == .done (.success ()) 0)
#guard (runEval program 4 (.guard (2 < 1)) 0 == .done .unmatch 0)
#guard (runEval program 8
  (.orElse (.choose Nat (fun n => n = 42)) (fun () => .pure 9)) 0 == .unsupportedChoice)
#guard (runEval program 8
  (.notHold (.choose Nat (fun n => n = 42))) 0 == .unsupportedChoice)
#guard (runEval program 8
  (.bind (.choose Nat (fun n => n = 42)) (fun n => .pure (n + 1))) 0 == .unsupportedChoice)
#guard (runEval program 1
  (.bind (.pure (7 : Nat)) (fun n => .pure (n + 1))) 0 == .outOfFuel)

/-- info: true -/
#guard_msgs in
#eval runEval program 8 retryFresh 4 == .done (.success "FRESH__5") 6

-- Results can also be displayed directly, without a test-specific projection.
/-- info: SpecTecExecution.RunResult.done (SpecTecExecution.Outcome.success "FRESH__5") 6 -/
#guard_msgs in
#eval runEval program 8 retryFresh 4

-- Kernel reduction supplies the premise; the library theorem supplies Eval.
theorem pure_by_execution :
    Eval program.erase (.pure (7 : Nat)) 3 (.success (.of (7 : Nat))) 3 :=
  runEval_sound program 1 (.pure (7 : Nat)) 3 (.success 7) 3 rfl

theorem recursion_by_execution :
    Eval program.erase (.call ⟨Nat, .countdown 5⟩) 4 (.success (.of (5 : Nat))) 4 :=
  runEval_sound program 30 (.call (.countdown 5)) 4 (.success 5) 4 rfl

theorem fresh_fallback_by_execution :
    Eval program.erase retryFresh.erase 4 (.success (.of "FRESH__5")) 6 :=
  runEval_sound program 8 retryFresh 4 (.success "FRESH__5") 6 rfl

theorem unmatch_by_execution : Eval program.erase allFailedFresh.erase 4 .unmatch 6 :=
  runEval_sound program 8 allFailedFresh 4 .unmatch 6 rfl

theorem abort_by_execution : Eval program.erase abortFresh.erase 4 (.abort "stop") 5 :=
  runEval_sound program 8 abortFresh 4 (.abort "stop") 5 rfl

example : runEval program 20 retryFresh 4 = .done (.success "FRESH__5") 6 :=
  runEval_mono program (by decide : 8 ≤ 20) retryFresh 4
    (.success "FRESH__5") 6 rfl

example (fuel start : Nat) :
    runEval program fuel (.call .loop) start = .outOfFuel := by
  induction fuel with
  | zero => rfl
  | succ fuel ih => exact ih

end SpecTecExecution.RunEvalTests
