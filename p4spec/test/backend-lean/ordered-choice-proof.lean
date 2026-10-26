namespace SpecTec
open SpecTecExecution

theorem choose_first_exec (n supply : Nat) :
    Eval Body (.call ⟨Nat, Call.Choose n⟩) supply
      (.success (.of (1 : Nat))) supply :=
  .call (.orElse_success (.pure 1))

theorem choose_first_functional (n supply : Nat) :
    Functional Body (choose_first_exec n supply) :=
  .call (.orElse_success (.pure 1))

theorem choose_first (n : Nat) : Choose n 1 := ⟨0, choose_first_exec n 0⟩

-- The former unordered rule union admits every clause's result.
inductive OldChoose : Nat → Nat → Prop where
  | first (n) : OldChoose n 1
  | second (n) : OldChoose n 2
  | fallback (n) : OldChoose n 9

theorem choose_sound (n output : Nat) (h : Choose n output) : OldChoose n output := by
  obtain ⟨final, h⟩ := h
  have equal : output = 1 := by
    simpa [Value.of.injEq] using (eval_deterministic (choose_first_functional n 0) h).1.symm
  subst output
  exact .first n

example (n : Nat) : ¬ Choose n 2 := by
  rintro ⟨final, h⟩
  have e := (eval_deterministic (choose_first_functional n 0) h).1
  cases e

example (n : Nat) : ¬ Choose n 9 := by
  rintro ⟨final, h⟩
  cases (eval_deterministic (choose_first_functional n 0) h).1

-- Output mismatch fails the caller's clause; the callee never retries output 2.
example (n : Nat) : Caller n 30 := by
  refine ⟨0, ?_⟩
  exact .call (.orElse_unmatch
    (.bind_success (choose_first_exec n 0) (.bind_unmatch (.guard_false (by decide))))
    (.orElse_success (.pure 30)))

example : Guarded 0 10 := by
  refine ⟨0, ?_⟩
  exact .call (.orElse_success (.bind_success (.guard_true rfl) (.pure 10)))
example : Guarded 1 11 := by
  refine ⟨0, ?_⟩
  exact .call (.orElse_unmatch (.bind_unmatch (.guard_false (by decide)))
    (.orElse_success (.pure 11)))
example (n : Nat) : Copy n n := by
  refine ⟨0, ?_⟩
  exact .call (.orElse_success (.pure n))
end SpecTec
