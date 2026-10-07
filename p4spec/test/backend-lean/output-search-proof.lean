namespace SpecTec

private instance natBoundary :
    SpecTecEval.Boundary Nat String String where
  aborts := fun _ _ => False
  unsupported := fun _ _ => False

private theorem candidate_zero : Candidate.evalSelected 7 0 := by
  left
  exact ⟨7, rfl, rfl, trivial⟩

private theorem candidate_one : Candidate.evalSelected 7 1 := by
  right
  exact ⟨7, rfl, rfl, trivial⟩

/-- Candidate 0 reaches the second Search premise and fails there.  This is a
    candidate-local failure, not failure of the Candidate call. -/
theorem candidate_zero_fails_later_premise :
    SpecTecEval.RuleFailure («Search:eval:rule:0:premises» 7 0)
      «Search:eval:rule:0:recoverable» := by
  apply SpecTecEval.RuleFailure.at 1 (0 = 1)
  · rfl
  · simp [«Search:eval:rule:0:recoverable»]
  · exact ⟨candidate_zero, trivial⟩
  · intro impossible
    cases impossible

theorem search_selects_other_output : Search.evalSelected 7 1 := by
  exact ⟨7, 1, rfl, rfl, candidate_one, rfl, trivial⟩

theorem search_success_evaluates : Search.eval 1 7 (.success 1) := by
  exact SpecTecEval.Evaluation.success search_selects_other_output

example : Search 7 1 := Search.success_sound search_success_evaluates

/-- A rule-failure outcome is strong enough to reject every public output;
    it cannot be built from the failed candidate 0 while candidate 1 succeeds. -/
theorem search_failure_is_universal {fuel : Nat}
    (failed : Search.eval fuel 7 (.ruleFailure)) : ∀ output, ¬ Search 7 output := by
  simpa only [Search.evalSucceeds] using Search.ruleFailure_sound failed

example {fuel : Nat} (failed : Search.eval fuel 7 (.ruleFailure)) : False := by
  exact search_failure_is_universal failed 1
    (Search.success_sound search_success_evaluates)

end SpecTec
