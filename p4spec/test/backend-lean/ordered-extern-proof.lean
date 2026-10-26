namespace SpecTec
open SpecTecExecution

-- External syntax is a singleton without a supplied type model.
example (state : archState) : state = .mk := by cases state; rfl
example : «$init_archState» archState.mk := .allowed _
example (state : archState) : «$init_archState» state := .allowed state
example : «$read_or_default» archState.mk 1 := by
  refine ⟨0, ?_⟩
  exact .call (.orElse_success (.bind_success
    (.call (.choose archState.mk (.allowed archState.mk)))
    (.bind_success (.guard_true rfl) (.pure 1))))

-- Externs over a type with multiple values still admit every output.
example : «$arbitrary_nat» (7 : Nat) := .allowed (7 : Nat)
example : «$arbitrary_nat» (8 : Nat) := .allowed (8 : Nat)

-- The extern succeeds in both derivations. Its caller's guard determines
-- whether the first clause succeeds or the next clause is tried.
example : «$read_nat_or_default» (7 : Nat) 1 := by
  refine ⟨0, ?_⟩
  exact .call (.orElse_success (.bind_success
    (.call (.choose (7 : Nat) (.allowed (7 : Nat))))
    (.bind_success (.guard_true rfl) (.pure 1))))

example : «$read_nat_or_default» (7 : Nat) 9 := by
  refine ⟨0, ?_⟩
  exact .call (.orElse_unmatch (.bind_success
    (.call (.choose (8 : Nat) (.allowed (8 : Nat))))
    (.bind_unmatch (.guard_false (by decide))))
    (.orElse_success (.pure 9)))

-- An extern itself cannot provide failure or abort evidence.
example : ¬ Eval Body (.call ⟨archState, Call.«$init_archState»⟩) 0 .unmatch 0 := by
  intro h
  cases h with
  | call h => cases h

example (message : String) :
    ¬ Eval Body (.call ⟨archState, Call.«$init_archState»⟩) 0 (.abort message) 0 := by
  intro h
  cases h with
  | call h => cases h

theorem read_known : ∃ a : Eval Body
    (.call ⟨Nat, Call.«$read_or_default» archState.mk⟩) 0 (.success (.of (1 : Nat))) 0,
    Functional Body a :=
  ⟨_, .call (.orElse_success (.bind_success
    (.call (.choose (ok := .allowed archState.mk) (by intro x y _ _; cases x; cases y; rfl)))
    (.bind_success (.guard_true (h := rfl)) (.pure (1 : Nat)))))⟩

example (n : Nat) (h : «$read_or_default» archState.mk n) : n = 1 := by
  obtain ⟨final, h⟩ := h
  obtain ⟨_, known⟩ := read_known
  simpa [Value.of.injEq] using ((eval_deterministic known h).1).symm

end SpecTec
