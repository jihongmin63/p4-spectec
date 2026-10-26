namespace SpecTec
open SpecTecExecution
syntax "prove_downcast_execution" : tactic
macro_rules
  | `(tactic| prove_downcast_execution) => `(tactic|
      first
        | refine ⟨0, ?_⟩; prove_downcast_execution
        | exact Eval.pure _
        | exact Eval.unmatch
        | apply Eval.guard_true; decide
        | apply Eval.guard_false; decide
        | apply Eval.call; prove_downcast_execution
        | apply Eval.orElse_success; prove_downcast_execution
        | apply Eval.orElse_unmatch; prove_downcast_execution; prove_downcast_execution
        | apply Eval.bind_success; prove_downcast_execution; prove_downcast_execution
        | apply Eval.bind_unmatch; prove_downcast_execution)

-- A result of 0 comes from otherwise: a component lies outside the subtype,
-- except for `SingleDog 1`, whose list has two elements.
example : TupleDog 0 5 := by prove_downcast_execution
example : TupleDog 1 0 := by prove_downcast_execution
example : TripleDogs 0 6 := by prove_downcast_execution
example : TripleDogs 1 0 := by prove_downcast_execution
example : ListDogs 0 2 := by prove_downcast_execution
example : ListDogs 1 0 := by prove_downcast_execution
example : SingleDog 0 7 := by prove_downcast_execution
example : SingleDog 1 0 := by prove_downcast_execution
example : SingleDog 2 0 := by prove_downcast_execution
example : OptionDog 0 3 := by prove_downcast_execution
example : OptionDog 1 4 := by prove_downcast_execution
example : OptionDog 2 0 := by prove_downcast_execution
example : NatPair 2 3 := by prove_downcast_execution
example : NatPair (-2) 0 := by prove_downcast_execution
example : PairDogs 0 2 := by prove_downcast_execution
example : PairDogs 1 0 := by prove_downcast_execution
end SpecTec
