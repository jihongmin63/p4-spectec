namespace SpecTec

private instance valueBoundary :
    SpecTecEval.Boundary value String String where
  aborts := fun _ error => error = "abort"
  unsupported := fun _ feature => feature = "unsupported"

private theorem regular_rule0_mismatch :
    «$ordered:regular:eval:rule:0:plan».Fails (.WRAP .ZERO) := by
  simp [SpecTecEval.EvalRulePlan.Fails,
    «$ordered:regular:eval:rule:0:plan»]

private theorem gate_one_refuted : ¬ Gate.evalSelected .ONE () := by
  intro selected
  cases selected with
  | here succeeded =>
      simp [SpecTecEval.EvalRulePlan.Succeeds,
        «Gate:eval:rule:0:plan»] at succeeded
  | laterNondeterministic remaining => cases remaining

private theorem regular_rule1_recoverable :
    «$ordered:regular:eval:rule:1:plan».Fails
      (value.WRAP value.ZERO) := by
  simp only [SpecTecEval.EvalRulePlan.Fails,
    «$ordered:regular:eval:rule:1:plan»]
  intro output witness
  rcases witness with ⟨v, _⟩
  by_cases matched :
      (value.WRAP value.ZERO = value.WRAP v ∧ output = value.ZERO)
  · right
    exact SpecTecEval.RuleFailure.at 0 (Gate.evalSelected .ONE ())
      (by rfl) (by simp [«$ordered:regular:eval:rule:1:plan»])
      (by trivial) gate_one_refuted
  · exact Or.inl matched

/-- The first same-pattern clause reaches its premise and recovers; only then
    may the following clause produce ONE. -/
theorem ordered_same_pattern_success :
    «$ordered:regular».evalSelected (.WRAP .ZERO) .ONE := by
  apply SpecTecEval.Selected.laterOrdered regular_rule0_mismatch
  apply SpecTecEval.Selected.laterOrdered regular_rule1_recoverable
  apply SpecTecEval.Selected.here
  exact ⟨⟨.ZERO, ()⟩, by rfl, by rfl, trivial⟩

theorem ordered_success_evaluates :
    «$ordered:regular».eval 1 (.WRAP .ZERO) (.success .ONE) := by
  exact SpecTecEval.Evaluation.success ordered_same_pattern_success

example : «$ordered:regular» (.WRAP .ZERO) .ONE := by
  exact SpecTecEval.Evaluator.success_sound
    (evaluator := «$ordered:regular».evaluator) ordered_success_evaluates

private theorem regular_one_has_no_output :
    ∀ output, ¬ «$ordered:regular».evalSelected .ONE output := by
  intro output selected
  cases selected with
  | here first =>
      simp [SpecTecEval.EvalRulePlan.Succeeds,
        «$ordered:regular:eval:rule:0:plan»] at first
  | laterOrdered _ remaining =>
      cases remaining with
      | here second =>
          simp [SpecTecEval.EvalRulePlan.Succeeds,
            «$ordered:regular:eval:rule:1:plan»] at second
      | laterOrdered _ remaining =>
          cases remaining with
          | here third =>
              simp [SpecTecEval.EvalRulePlan.Succeeds,
                «$ordered:regular:eval:rule:2:plan»] at third
          | laterOrdered _ impossible => cases impossible

private theorem public_regular_rule_failed :
    «$ordered:eval:rule:0:plan».Fails .ONE := by
  simp only [SpecTecEval.EvalRulePlan.Fails,
    «$ordered:eval:rule:0:plan»]
  intro output witness
  rcases witness with ⟨argumentInput, ⟨argumentOutput, _⟩⟩
  by_cases matched : (.ONE = argumentInput ∧ output = argumentOutput)
  · right
    rcases matched with ⟨inputEq, outputEq⟩
    subst argumentInput
    subst argumentOutput
    exact SpecTecEval.RuleFailure.at 0
      («$ordered:regular».evalSelected .ONE output)
      (by rfl) (by simp [«$ordered:eval:rule:0:plan»])
      (by trivial) (regular_one_has_no_output output)
  · exact Or.inl matched

private theorem enabled_one_fails : «$ordered:enabled».fails .ONE := by
  intro upper
  obtain ⟨rule, member, head, side, positive, negative⟩ :=
    SpecTecWFS.Derives.cases upper
  cases member <;> cases head

/-- The otherwise branch is selected only after the ordinary wrapper has a
    universal recoverable-failure certificate for the input. -/
theorem otherwise_after_all_regular_fail :
    «$ordered».evalSelected .ONE .ONE := by
  apply SpecTecEval.Selected.laterOrdered public_regular_rule_failed
  apply SpecTecEval.Selected.here
  exact ⟨⟨.ONE, ()⟩, by rfl, by rfl,
    ⟨enabled_one_fails, trivial⟩⟩

example : «$ordered» .ONE .ONE :=
  «$ordered».selected_sound otherwise_after_all_regular_fail

example : Gate.eval 1 .ZERO (.abort "abort") := by
  apply SpecTecEval.Evaluation.abort
  rfl

example : Gate.eval 1 .ZERO (.unsupported "unsupported") := by
  apply SpecTecEval.Evaluation.unsupported
  rfl

example : Gate.eval 0 .ZERO (.timeout) :=
  SpecTecEval.Evaluator.timeout Gate.evaluator .ZERO

example : ¬ SpecTecEval.MayContinue
    (SpecTecEval.AlternativeResult.abort "abort" :
      SpecTecEval.AlternativeResult value String String) :=
  SpecTecEval.abort_stops "abort"

example : ¬ SpecTecEval.MayContinue
    (SpecTecEval.AlternativeResult.unsupported "unsupported" :
      SpecTecEval.AlternativeResult value String String) :=
  SpecTecEval.unsupported_stops "unsupported"

private theorem negative_loop_lower_absent :
    ¬ SpecTecWFS.lower «NegativeLoop:Semantics».InProgram
      («NegativeLoop:Semantics».Atom.NegativeLoop .ZERO) := by
  let interpretation : «NegativeLoop:Semantics».Atom → Prop := fun atom =>
    match atom with
    | .NegativeLoop .ZERO => False
    | _ => True
  have gammaSelf : SpecTecWFS.gamma «NegativeLoop:Semantics».InProgram
      interpretation («NegativeLoop:Semantics».Atom.NegativeLoop .ZERO) :=
    SpecTecWFS.Derives.rule _ «NegativeLoop:Semantics».InProgram.rule_0
      trivial trivial ⟨by simp [interpretation], trivial⟩
  have closed : ∀ rule, «NegativeLoop:Semantics».InProgram rule → rule.side →
      SpecTecWFS.All interpretation rule.positive →
      SpecTecWFS.All
        (fun atom => ¬ SpecTecWFS.gamma
          «NegativeLoop:Semantics».InProgram interpretation atom)
        rule.negative → interpretation rule.head := by
    intro rule member side positive negative
    cases member <;> simp_all [interpretation, SpecTecWFS.All]
  have prefixed : ∀ atom,
      SpecTecWFS.alternating «NegativeLoop:Semantics».InProgram
        interpretation atom → interpretation atom := by
    intro atom derived
    exact derived interpretation closed
  intro proof
  exact proof interpretation prefixed

private theorem negative_loop_upper :
    SpecTecWFS.upper «NegativeLoop:Semantics».InProgram
      («NegativeLoop:Semantics».Atom.NegativeLoop .ZERO) :=
  SpecTecWFS.Derives.rule _ «NegativeLoop:Semantics».InProgram.rule_0
    trivial trivial ⟨negative_loop_lower_absent, trivial⟩

private theorem negative_loop_undetermined : NegativeLoop.undetermined .ZERO :=
  ⟨negative_loop_upper, negative_loop_lower_absent⟩

example : NegativeLoop.eval 1 .ZERO (.undetermined) := by
  apply SpecTecEval.Evaluation.undetermined
  exact ⟨(), negative_loop_undetermined⟩

end SpecTec
