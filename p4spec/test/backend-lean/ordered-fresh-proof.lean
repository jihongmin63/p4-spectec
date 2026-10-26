namespace SpecTec
open SpecTecExecution

syntax "prove_fresh_execution" : tactic
macro_rules
  | `(tactic| prove_fresh_execution) => `(tactic|
      first
        | exact Eval.pure _
        | exact Eval.freshId
        | exact Eval.unmatch
        | exact Eval.abort _
        | apply Eval.guard_true; decide
        | apply Eval.guard_false; decide
        | apply Eval.call; prove_fresh_execution
        | apply Eval.orElse_success; prove_fresh_execution
        | apply Eval.orElse_unmatch; prove_fresh_execution; prove_fresh_execution
        | apply Eval.orElse_abort; prove_fresh_execution
        | apply Eval.bind_success; prove_fresh_execution; prove_fresh_execution
        | apply Eval.bind_unmatch; prove_fresh_execution
        | apply Eval.bind_abort; prove_fresh_execution
        | apply Eval.notHold_success; prove_fresh_execution
        | apply Eval.notHold_unmatch; prove_fresh_execution
        | apply Eval.notHold_abort; prove_fresh_execution)

-- Internal execution composes at an arbitrary supply without public wrappers.
theorem freshOne_at (n supply : Nat) :
    Eval Body (.call ⟨typeId, Call.FreshOne n⟩) supply
      (.success (.of (freshName supply))) (supply + 1) := by
  apply Eval.call
  apply Eval.orElse_success
  exact .bind_success (.call .freshId) (.pure _)

example : FreshOne 7 "FRESH__0" := ⟨1, freshOne_at 7 0⟩
example : «$fresh_typeId» "FRESH__0" := ⟨1, .call .freshId⟩
example : FreshPair 7 "FRESH__0" "FRESH__1" := by
  refine ⟨2, ?_⟩; prove_fresh_execution
example : FreshMismatch 7 "FRESH__1" := by
  refine ⟨2, ?_⟩; prove_fresh_execution
example : FailedCaller 7 "FRESH__1" := by
  refine ⟨2, ?_⟩; prove_fresh_execution
example : NegatedFailure 7 "FRESH__1" := by
  refine ⟨2, ?_⟩; prove_fresh_execution
example : NegatedSuccess 7 "FRESH__1" := by
  refine ⟨2, ?_⟩; prove_fresh_execution
example : «$pair» ("FRESH__0", "FRESH__1") := by
  refine ⟨2, ?_⟩; prove_fresh_execution
example : «$callback_pair» ("FRESH__0", "FRESH__1") := by
  refine ⟨2, ?_⟩; prove_fresh_execution
example : «$fresh_typeIds» 0 [] := by
  refine ⟨0, ?_⟩; prove_fresh_execution
example : «$fresh_typeIds» 3 ["FRESH__0", "FRESH__1", "FRESH__2"] := by
  refine ⟨3, ?_⟩; prove_fresh_execution
example : «$many» [4, 4, 4] ["FRESH__0", "FRESH__1", "FRESH__2"] := by
  refine ⟨3, ?_⟩; prove_fresh_execution
example : «$debug_fresh» "FRESH__1" := by
  refine ⟨2, ?_⟩; prove_fresh_execution
example : «$debug_iter» [7, 7] "FRESH__2" := by
  refine ⟨3, ?_⟩; prove_fresh_execution
example : «$debug_failure» "FRESH__1" := by
  refine ⟨2, ?_⟩; prove_fresh_execution

example : Eval Body
    (.call ⟨Int, Call.«$fresh_then_abort»⟩) 0
    (.abort "builtin $text_to_int failed") 1 := by prove_fresh_execution
example : Eval Body
    (.call ⟨typeId, Call.«$debug_abort»⟩) 0
    (.abort "builtin $text_to_int failed") 1 := by prove_fresh_execution

syntax "prove_fresh_functional" : tactic
macro_rules
  | `(tactic| prove_fresh_functional) => `(tactic|
      first
        | exact Functional.pure _
        | exact Functional.freshId
        | exact Functional.unmatch
        | exact Functional.abort _
        | apply Functional.guard_true; decide
        | apply Functional.guard_false; decide
        | apply Functional.call; prove_fresh_functional
        | apply Functional.orElse_success; prove_fresh_functional
        | apply Functional.orElse_unmatch; prove_fresh_functional; prove_fresh_functional
        | apply Functional.orElse_abort; prove_fresh_functional
        | apply Functional.bind_success; prove_fresh_functional; prove_fresh_functional
        | apply Functional.bind_unmatch; prove_fresh_functional
        | apply Functional.bind_abort; prove_fresh_functional
        | apply Functional.notHold_success; prove_fresh_functional
        | apply Functional.notHold_unmatch; prove_fresh_functional
        | apply Functional.notHold_abort; prove_fresh_functional)

example : ¬ FreshOne 7 "FRESH__1" := by
  rintro ⟨final, h⟩
  have eq : freshName 0 = "FRESH__1" := by
    simpa only [Outcome.success.injEq, Value.of.injEq, heq_eq_eq, true_and] using
      (eval_deterministic (a := freshOne_at 7 0) (by prove_fresh_functional) h).1
  exact (by decide : freshName 0 ≠ "FRESH__1") eq

theorem freshMismatch_exec : Eval Body
    (.call ⟨typeId, Call.FreshMismatch 7⟩) 0
    (.success (.of "FRESH__1")) 2 := by prove_fresh_execution

example : ∃ index, Selected Body (FreshMismatch_clauses 7)
    0 index (.of "FRESH__1") 2 :=
  (tryClauses_success_iff _ _ _ _).mp (eval_call_iff.mp freshMismatch_exec)

-- No extra supply argument appears in any request or public API.
example : Nat → Call typeId := Call.FreshOne
example : Nat → typeId → Prop := FreshOne
example : Nonempty (Nat → Action Request) := ⟨«FreshOne:clause:0»⟩
example : Call typeId := Call.«$fresh_typeId»

end SpecTec
