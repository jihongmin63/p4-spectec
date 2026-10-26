namespace SpecTec
open SpecTecExecution

example (n : Nat) : FailureValue n result.FAIL := by
  refine ⟨0, ?_⟩
  exact .call (.orElse_success (.pure _))
example : Multi 3 7 4 12 := by
  refine ⟨0, ?_⟩
  exact .call (.orElse_success (.pure _))
example : EqualPair 2 2 true := by
  refine ⟨0, ?_⟩
  exact .call (.orElse_success (.bind_success (.guard_true rfl) (.pure true)))
example : EqualPair 2 3 false := by
  refine ⟨0, ?_⟩
  exact .call (.orElse_unmatch (.bind_unmatch (.guard_false (by decide)))
    (.orElse_success (.pure false)))
example : Nonzero 0 false := by
  refine ⟨0, ?_⟩
  exact .call (.orElse_unmatch
    (.bind_unmatch (.notHold_unmatch
      (.call (.orElse_success (.bind_success (.guard_true rfl) (.pure ()))))))
    (.orElse_success (.pure false)))
example : Nonzero 1 true := by
  refine ⟨0, ?_⟩
  exact .call (.orElse_success (.bind_success
    (.notHold_success (.call (.orElse_unmatch
      (.bind_unmatch (.guard_false (by decide))) .unmatch))) (.pure true)))

theorem count_zero_exec (supply : Nat) :
    Eval Body (.call ⟨Nat, Call.Count 0⟩) supply
      (.success (.of (0 : Nat))) supply :=
  .call (.orElse_success (.bind_success (.guard_true rfl) (.pure 0)))
theorem count_zero : Count 0 0 := ⟨0, count_zero_exec 0⟩
theorem count_one_exec (supply : Nat) :
    Eval Body (.call ⟨Nat, Call.Count 1⟩) supply
      (.success (.of (1 : Nat))) supply :=
  .call (.orElse_unmatch (.bind_unmatch (.guard_false (by decide)))
    (.orElse_success (.bind_success (.guard_true (by decide))
      (.bind_success (.guard_true (by decide))
        (.bind_success (.guard_true (by decide))
          (.bind_success (count_zero_exec supply) (.pure 1)))))))
theorem count_one : Count 1 1 := ⟨0, count_one_exec 0⟩

example : ∃ index, Selected Body (Count_clauses 1) 0 index (.of (1 : Nat)) 0 :=
  (tryClauses_success_iff _ _ _ _).mp (eval_call_iff.mp (count_one_exec 0))

example (n : Nat) : «$before_output» n 1 := by
  refine ⟨0, ?_⟩
  exact .call (.orElse_success (.bind_success
    (.call (.orElse_success (.pure 1))) (.pure 1)))
example : «$max_or_default» [] 99 := by
  refine ⟨0, ?_⟩
  exact .call (.orElse_unmatch
    (.bind_unmatch (.call (.orElse_unmatch .unmatch .unmatch)))
    (.orElse_success (.pure 99)))
example : «$max_or_default» [3, 5, 4] 5 := by
  refine ⟨0, ?_⟩
  exact .call (.orElse_success (.bind_success
    (.call (.orElse_success (.pure 5))) (.pure 5)))
example : Eval Body (.call ⟨Int, Call.«$parse_or_default» "bad"⟩) 0
    (.abort "builtin $text_to_int failed") 0 := by
  exact .call (.orElse_abort (.bind_abort (.call
    (.orElse_unmatch .unmatch (.orElse_abort (.abort _))))))
example : «$parse_or_default» "42" 42 := by
  refine ⟨0, ?_⟩
  exact .call (.orElse_success (.bind_success
    (.call (.orElse_success (.pure 42))) (.pure 42)))
end SpecTec

namespace SpecTec
open SpecTecExecution

theorem left_zero_exec (supply : Nat) :
    Eval Body (.call ⟨Nat, Call.«$left» 0⟩) supply
      (.success (.of (0 : Nat))) supply :=
  .call (.orElse_success (.bind_success (.guard_true rfl) (.pure 0)))
theorem left_zero : «$left» 0 0 := ⟨0, left_zero_exec 0⟩
theorem right_zero_exec (supply : Nat) :
    Eval Body (.call ⟨Nat, Call.«$right» 0⟩) supply
      (.success (.of (0 : Nat))) supply :=
  .call (.orElse_success (.bind_success (left_zero_exec supply) (.pure 0)))
theorem right_zero : «$right» 0 0 := ⟨0, right_zero_exec 0⟩
example : «$left» 1 0 := by
  refine ⟨0, ?_⟩
  exact .call (.orElse_unmatch (.bind_unmatch (.guard_false (by decide)))
    (.orElse_success (.bind_success (.guard_true (by decide))
      (.bind_success (.guard_true (by decide))
        (.bind_success (.guard_true (by decide))
          (.bind_success (right_zero_exec 0) (.pure 0)))))))
example : «$via_apply» 7 7 := by
  refine ⟨0, ?_⟩
  exact .call (.orElse_success (.bind_success
    (.call (.orElse_success (.bind_success
      (.call (.orElse_success (.pure 7))) (.pure 7)))) (.pure 7)))

example : «$dom_map» Nat Bool (.«`{ % `}» [.«% ':' %» 7 true]) (.«`{ % `}» [7]) := by
  refine ⟨0, ?_⟩
  exact .call (.orElse_success (.bind_success
    (.call (.orElse_unmatch .unmatch (.orElse_success (.bind_success
      (.call (.orElse_success (.pure (([], []) : List Nat × List Bool))))
      (.pure (([7], [true]) : List Nat × List Bool)))))) (.pure _)))

example : «$strip_or_default» "abcd" "ab" "cd" := by
  refine ⟨0, ?_⟩
  exact .call (.orElse_success (.bind_success
    (.call (.orElse_success (.bind_success (.guard_true (by decide))
      (.bind_success (.guard_true rfl) (.pure "cd"))))) (.pure "cd")))
example : Eval Body (.call ⟨String, Call.«$strip_or_default» "abcd" "xyz"⟩) 0
    (.abort "builtin $strip_prefix failed") 0 := by
  exact .call (.orElse_abort (.bind_abort (.call (.orElse_unmatch
    (.bind_success (.guard_true (by decide)) (.bind_unmatch (.guard_false (by decide))))
    (.orElse_abort (.abort _))))))

-- A callback with Bool output cannot inhabit the Nat callback signature.
example : Nat → Call Nat := Call.«$identity»
end SpecTec

namespace SpecTec
open SpecTecExecution
example : Eval Body
    (.call ⟨Nat, Call.«$partition_result» [] 4611686018427387904⟩) 0
    (.abort "builtin $partition_ failed") 0 := by
  exact .call (.orElse_abort (.bind_abort (.call (.orElse_unmatch
    (.bind_unmatch (.guard_false (by decide))) (.orElse_abort (.abort _))))))
end SpecTec

namespace SpecTec
open SpecTecExecution
example : «$table_fallback» color.RED false := by
  refine ⟨0, ?_⟩
  exact .call (.orElse_unmatch (.bind_success (.guard_true rfl)
    (.bind_unmatch (.call (.orElse_unmatch (.bind_unmatch
      (.call (.orElse_unmatch .unmatch .unmatch))) .unmatch))))
    (.orElse_success (.bind_success (.guard_true rfl) (.pure false))))
end SpecTec
