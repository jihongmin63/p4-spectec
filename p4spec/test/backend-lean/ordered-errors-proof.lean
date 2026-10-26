namespace SpecTec
open SpecTecExecution
syntax "prove_error_execution" : tactic
macro_rules
  | `(tactic| prove_error_execution) => `(tactic|
      first
        | refine ⟨0, ?_⟩; prove_error_execution
        | exact Eval.pure _
        | exact Eval.unmatch
        | exact Eval.abort _
        | apply Eval.guard_true; decide
        | apply Eval.guard_false; decide
        | apply Eval.call; prove_error_execution
        | apply Eval.orElse_success; prove_error_execution
        | apply Eval.orElse_unmatch; prove_error_execution; prove_error_execution
        | apply Eval.orElse_abort; prove_error_execution
        | apply Eval.bind_success; prove_error_execution; prove_error_execution
        | apply Eval.bind_unmatch; prove_error_execution
        | apply Eval.bind_abort; prove_error_execution)

example : Eval Body (.call ⟨String, Call.«$slice_text» "a" 0 2⟩) 0
    (.abort "slice out of bounds") 0 := by prove_error_execution
example : Eval Body (.call ⟨String, Call.«$update_text» "a" 0 "xx"⟩) 0
    (.abort "text update requires one byte") 0 := by prove_error_execution
example : Eval Body (.call ⟨String, Call.«$update_text» "a" 1 "x"⟩) 0
    (.abort "update index out of bounds") 0 := by prove_error_execution
example : Eval Body (.call ⟨List Nat, Call.«$slice_list» [1] 0 2⟩) 0
    (.abort "slice out of bounds") 0 := by prove_error_execution
example : Eval Body (.call ⟨List Nat, Call.«$update_list» [1] 1 3⟩) 0
    (.abort "update index out of bounds") 0 := by prove_error_execution
example : Eval Body (.call ⟨Nat, Call.«$divide_nat» 1 0⟩) 0
    (.abort "division by zero") 0 := by prove_error_execution

-- In-bounds source byte operations succeed with an unrepresentable text.
-- The Lean adapter blocks them explicitly instead of inventing unmatch.
example : Eval Body (.call ⟨String, Call.«$index_text» "é" 0⟩) 0
    (.abort "text result is not valid UTF-8") 0 := by prove_error_execution
example : Eval Body (.call ⟨String, Call.«$slice_text» "é" 0 1⟩) 0
    (.abort "text result is not valid UTF-8") 0 := by prove_error_execution
example : Eval Body (.call ⟨String, Call.«$update_text» "é" 0 "a"⟩) 0
    (.abort "text result is not valid UTF-8") 0 := by prove_error_execution

example : «$slice_text» "abcd" 1 2 "bc" := by prove_error_execution
example : «$slice_text» "é" 0 2 "é" := by prove_error_execution
example : «$update_text» "abc" 1 "x" "axc" := by prove_error_execution
example : «$slice_list» [1, 2, 3] 1 2 [2, 3] := by prove_error_execution
example : «$update_list» [1, 2] 1 3 [1, 3] := by prove_error_execution
example : «$divide_nat» 6 2 3 := by prove_error_execution

-- AL's inserted indexing sidecondition is an ordinary failed guard.
example : «$index_text» "a" 1 "fallback" := by prove_error_execution

syntax "prove_error_functional" : tactic
macro_rules
  | `(tactic| prove_error_functional) => `(tactic|
      first
        | exact Functional.pure _
        | exact Functional.freshId
        | exact Functional.unmatch
        | exact Functional.abort _
        | apply Functional.guard_true; decide
        | apply Functional.guard_false; decide
        | apply Functional.call; prove_error_functional
        | apply Functional.orElse_success; prove_error_functional
        | apply Functional.orElse_unmatch; prove_error_functional; prove_error_functional
        | apply Functional.orElse_abort; prove_error_functional
        | apply Functional.bind_success; prove_error_functional; prove_error_functional
        | apply Functional.bind_unmatch; prove_error_functional
        | apply Functional.bind_abort; prove_error_functional
        | apply Functional.notHold_success; prove_error_functional
        | apply Functional.notHold_unmatch; prove_error_functional
        | apply Functional.notHold_abort; prove_error_functional)
example : ¬ «$slice_text» "a" 0 2 "fallback" := by
  rintro ⟨final, h⟩
  obtain ⟨_, failure⟩ : ∃ a : Eval Body (.call ⟨String, Call.«$slice_text» "a" 0 2⟩) 0
      (.abort "slice out of bounds") 0,
      Functional Body a := ⟨_, by prove_error_functional⟩
  cases (eval_deterministic failure h).1
example : ¬ «$index_text» "é" 0 "fallback" := by
  rintro ⟨final, h⟩
  obtain ⟨_, failure⟩ : ∃ a : Eval Body (.call ⟨String, Call.«$index_text» "é" 0⟩) 0
      (.abort "text result is not valid UTF-8") 0,
      Functional Body a := ⟨_, by prove_error_functional⟩
  cases (eval_deterministic failure h).1
end SpecTec
