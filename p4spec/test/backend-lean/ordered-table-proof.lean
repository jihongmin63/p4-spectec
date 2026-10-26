namespace SpecTec
open SpecTecExecution
syntax "prove_table_execution" : tactic
macro_rules
  | `(tactic| prove_table_execution) => `(tactic|
      first
        | refine ⟨0, ?_⟩; prove_table_execution
        | exact Eval.pure _
        | exact Eval.unmatch
        | exact Eval.abort _
        | apply Eval.guard_true; decide
        | apply Eval.guard_false; decide
        | apply Eval.call; prove_table_execution
        | apply Eval.orElse_success; prove_table_execution
        | apply Eval.orElse_unmatch; prove_table_execution; prove_table_execution
        | apply Eval.orElse_abort; prove_table_execution
        | apply Eval.bind_success; prove_table_execution; prove_table_execution
        | apply Eval.bind_unmatch; prove_table_execution
        | apply Eval.bind_abort; prove_table_execution)

-- As in the SL interpreter, a table without an applicable row aborts.
example : Eval Body (.call ⟨Bool, Call.«$is_red» color.GREEN⟩) 0
    (.abort "table $is_red did not return a value") 0 := by prove_table_execution
example : Eval Body (.call ⟨Bool, Call.«$never»⟩) 0
    (.abort "table $never did not return a value") 0 := by prove_table_execution

example : «$is_red» color.RED true := by prove_table_execution
example : «$is_warm» color.BLUE false := by prove_table_execution
example : «$guarded» color.RED true := by prove_table_execution

-- The abort reaches the caller instead of selecting its otherwise clause.
syntax "prove_table_functional" : tactic
macro_rules
  | `(tactic| prove_table_functional) => `(tactic|
      first
        | exact Functional.pure _
        | exact Functional.freshId
        | exact Functional.unmatch
        | exact Functional.abort _
        | apply Functional.guard_true; decide
        | apply Functional.guard_false; decide
        | apply Functional.call; prove_table_functional
        | apply Functional.orElse_success; prove_table_functional
        | apply Functional.orElse_unmatch; prove_table_functional; prove_table_functional
        | apply Functional.orElse_abort; prove_table_functional
        | apply Functional.bind_success; prove_table_functional; prove_table_functional
        | apply Functional.bind_unmatch; prove_table_functional
        | apply Functional.bind_abort; prove_table_functional
        | apply Functional.notHold_success; prove_table_functional
        | apply Functional.notHold_unmatch; prove_table_functional
        | apply Functional.notHold_abort; prove_table_functional)
theorem guarded_green_aborts : ∃ a : Eval Body
    (.call ⟨Bool, Call.«$guarded» color.GREEN⟩) 0
    (.abort "table $is_red did not return a value") 0, Functional Body a :=
  ⟨_, by prove_table_functional⟩
example : ¬ «$guarded» color.GREEN false := by
  rintro ⟨final, h⟩
  obtain ⟨_, known⟩ := guarded_green_aborts
  cases (eval_deterministic known h).1
end SpecTec
