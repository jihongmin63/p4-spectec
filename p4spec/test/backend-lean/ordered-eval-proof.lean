namespace SpecTec

private instance valueBoundary :
    SpecTecEval.Boundary value String String where
  aborts := fun _ error => error = "abort"
  unsupported := fun _ feature => feature = "unsupported"

private theorem regular_rule0_mismatch :
    «$ordered:regular:eval:rule:0:failed» (.WRAP .ZERO) := by
  intro output
  left
  intro matched
  cases matched.1

private theorem gate_one_refuted : ¬ Gate.evalSelected .ONE () := by
  intro selected
  simp only [Gate.evalSelected, «Gate:eval:rule:0:succeeds»] at selected
  cases selected.1

private theorem regular_rule1_recoverable :
    «$ordered:regular:eval:rule:1:failed» (value.WRAP value.ZERO) := by
  intro output v
  by_cases matched :
      (value.WRAP value.ZERO = value.WRAP v ∧ output = value.ZERO)
  · right
    exact SpecTecEval.RuleFailure.at 0 (Gate.evalSelected .ONE ())
      (by rfl) (by simp [«$ordered:regular:eval:rule:1:recoverable»])
      (by trivial) gate_one_refuted
  · exact Or.inl matched

/-- The first same-pattern clause reaches its premise and recovers; only then
    may the following clause produce ONE. -/
theorem ordered_same_pattern_success :
    «$ordered:regular».evalSelected (.WRAP .ZERO) .ONE := by
  right
  right
  constructor
  · exact ⟨regular_rule0_mismatch, regular_rule1_recoverable, trivial⟩
  · exact ⟨.ZERO, rfl, rfl, trivial⟩

theorem ordered_success_evaluates :
    «$ordered:regular».eval 1 (.WRAP .ZERO) (.success .ONE) := by
  exact SpecTecEval.Evaluation.success ordered_same_pattern_success

example : «$ordered:regular» (.WRAP .ZERO) .ONE := by
  exact «$ordered:regular».success_sound ordered_success_evaluates

private theorem regular_one_has_no_output :
    ∀ output, ¬ «$ordered:regular».evalSelected .ONE output := by
  intro output selected
  simp only [«$ordered:regular».evalSelected] at selected
  rcases selected with first | second | third
  · simp [«$ordered:regular:eval:rule:0:succeeds»] at first
  · simp [«$ordered:regular:eval:rule:1:succeeds»] at second
  · simp [«$ordered:regular:eval:rule:2:succeeds»] at third

private theorem public_regular_rule_failed :
    «$ordered:eval:rule:0:failed» .ONE := by
  intro output argumentInput argumentOutput
  by_cases matched : (.ONE = argumentInput ∧ output = argumentOutput)
  · right
    rcases matched with ⟨inputEq, outputEq⟩
    subst argumentInput
    subst argumentOutput
    exact SpecTecEval.RuleFailure.at 0
      («$ordered:regular».evalSelected .ONE output)
      (by rfl) (by simp [«$ordered:eval:rule:0:recoverable»])
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
  right
  constructor
  · exact ⟨public_regular_rule_failed, trivial⟩
  · exact ⟨.ONE, rfl, rfl, enabled_one_fails, trivial⟩

example : «$ordered» .ONE .ONE :=
  «$ordered».selected_sound otherwise_after_all_regular_fail

example : Gate.eval 1 .ZERO (.abort "abort") := by
  apply SpecTecEval.Evaluation.abort
  rfl

example : Gate.eval 1 .ZERO (.unsupported "unsupported") := by
  apply SpecTecEval.Evaluation.unsupported
  rfl

example : Gate.eval 0 .ZERO (.timeout) := Gate.timeout .ZERO

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
