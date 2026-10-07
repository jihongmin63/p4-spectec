namespace SpecTec
private abbrev «Search:eval:rule:0:plan» := (Search.evalRules[0]'(by decide))

attribute [local simp] SpecTecPlan.evaluator SpecTecPlan.Alternative.toEvalRule SpecTecPlan.Plan.compile SpecTecPlan.Plan.premises SpecTecPlan.Plan.Witness SpecTecPlan.ExternalSignature.selected «Candidate:Semantics».rule_0_plan «Candidate:Semantics».rule_1_plan «Search:Semantics».rule_0_plan Candidate.evaluator Search.evaluator Candidate.evalRules Search.evalRules

private instance natBoundary :
    SpecTecEval.Boundary Nat String String where
  aborts := fun _ _ => False
  unsupported := fun _ _ => False

private theorem candidate_zero : Candidate.evalSelected 7 0 := by
  apply SpecTecEval.Selected.here
  exact ⟨⟨7, ()⟩, by rfl, trivial⟩

private theorem candidate_one : Candidate.evalSelected 7 1 := by
  apply SpecTecEval.Selected.laterNondeterministic
  apply SpecTecEval.Selected.here
  exact ⟨⟨7, ()⟩, by rfl, trivial⟩

/-- Candidate 0 reaches the second Search premise and fails there.  This is a
    candidate-local failure, not failure of the Candidate call. -/
theorem candidate_zero_fails_later_premise :
    SpecTecEval.RuleFailure
      («Search:eval:rule:0:plan».premises ⟨7, ⟨0, ()⟩⟩)
      «Search:eval:rule:0:plan».recoverable := by
  apply SpecTecEval.RuleFailure.at 1 (0 = 1)
  · rfl
  · decide
  · exact ⟨candidate_zero, trivial⟩
  · intro impossible
    cases impossible

theorem search_selects_other_output : Search.evalSelected 7 1 := by
  apply SpecTecEval.Selected.here
  exact ⟨⟨7, ⟨1, ()⟩⟩, by rfl,
    ⟨candidate_one, rfl, trivial⟩⟩

theorem search_success_evaluates : Search.eval 1 7 (.success 1) := by
  exact SpecTecEval.Evaluation.success search_selects_other_output

example : Search 7 1 :=
  SpecTecEval.Evaluator.success_sound
    (evaluator := Search.evaluator) search_success_evaluates

/-- A rule-failure outcome is strong enough to reject every public output;
    it cannot be built from the failed candidate 0 while candidate 1 succeeds. -/
theorem search_failure_is_universal {fuel : Nat}
    (failed : Search.eval fuel 7 (.ruleFailure)) : ∀ output, ¬ Search 7 output := by
  simpa only [Search.evalSucceeds] using
    (SpecTecEval.Evaluator.ruleFailure_sound
      (evaluator := Search.evaluator) failed)

example {fuel : Nat} (failed : Search.eval fuel 7 (.ruleFailure)) : False := by
  exact search_failure_is_universal failed 1
    (SpecTecEval.Evaluator.success_sound
      (evaluator := Search.evaluator) search_success_evaluates)

end SpecTec
