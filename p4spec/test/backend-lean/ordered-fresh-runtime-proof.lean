namespace SpecTecExecution

def freshTestProgram : Unit → Action Unit :=
  fun _ => .bind .freshId (fun (name : String) => .pure name)

def freshPair : Action Unit :=
  .bind .freshId (fun (a : String) =>
    .bind (.call ()) (fun (b : String) => .pure (a, b)))

theorem freshPairRuns : Eval freshTestProgram freshPair 4
    (.success (.of ("FRESH__4", "FRESH__5"))) 6 :=
  .bind_success .freshId (.bind_success
    (.call (.bind_success .freshId (.pure _))) (.pure _))

theorem freshPairFunctional : Functional freshTestProgram freshPairRuns :=
  .bind_success .freshId (.bind_success
    (.call (.bind_success .freshId (.pure _))) (.pure _))

example {outcome : Outcome Value} {final : Nat}
    (h : Eval freshTestProgram freshPair 4 outcome final) :
    outcome = .success (.of ("FRESH__4", "FRESH__5")) ∧ final = 6 :=
  ⟨(eval_deterministic freshPairFunctional h).1.symm,
    (eval_deterministic freshPairFunctional h).2.symm⟩

def discardedFresh : Action Unit :=
  .bind .freshId (fun (_ : String) => .unmatch)

def freshFallback : List (Action Unit) :=
  [discardedFresh, .freshId]

example : Eval freshTestProgram (tryClauses freshFallback) 0
    (.success (.of "FRESH__1")) 2 :=
  .orElse_unmatch (.bind_success .freshId .unmatch)
    (.orElse_success .freshId)

example : Eval freshTestProgram
    (.bind (.notHold discardedFresh) (fun (_ : Unit) => .freshId)) 0
    (.success (.of "FRESH__1")) 2 :=
  .bind_success (.notHold_success (.bind_success .freshId .unmatch)) .freshId

example : Eval freshTestProgram
    (.orElse (.notHold (.call ())) (fun _ => .freshId)) 0
    (.success (.of "FRESH__1")) 2 :=
  .orElse_unmatch
    (.notHold_unmatch (.call (.bind_success .freshId (.pure _)))) .freshId

example : Eval freshTestProgram
    (.orElse (.bind .freshId (fun (_ : String) => .abort "stop"))
      (fun _ => .freshId)) 9 (.abort "stop") 10 :=
  .orElse_abort (.bind_success .freshId (.abort _))

example : Eval freshTestProgram (tryClauses freshFallback) 3 .unmatch 5 → False := by
  intro h
  obtain ⟨_, known⟩ : ∃ a : Eval freshTestProgram (tryClauses freshFallback) 3
      (.success (.of "FRESH__4")) 5, Functional freshTestProgram a :=
    ⟨.orElse_unmatch (.bind_success .freshId .unmatch) (.orElse_success .freshId),
      .orElse_unmatch (.bind_success .freshId .unmatch) (.orElse_success .freshId)⟩
  cases (eval_deterministic known h).1

example : AllUnmatch freshTestProgram
    [discardedFresh, .guard False] 0 1 :=
  .cons (.bind_success .freshId .unmatch)
    (.cons (.guard_false (fun h => h)) .nil)

-- Even exhausting every clause retains allocations made by failed attempts.
theorem twoFailedFresh (start : Nat) :
    Eval freshTestProgram (tryClauses [discardedFresh, discardedFresh])
      start .unmatch (start + 2) :=
  .orElse_unmatch (.bind_success .freshId .unmatch)
    (.orElse_unmatch (.bind_success .freshId .unmatch) .unmatch)

example (start : Nat) : AllUnmatch freshTestProgram
    [discardedFresh, discardedFresh] start (start + 2) :=
  (tryClauses_unmatch_iff _ _ _).mp (twoFailedFresh start)

-- Appending a successful clause continues after all earlier allocations.
example : Eval freshTestProgram
    (tryClauses ([discardedFresh, discardedFresh] ++ [.freshId])) 4
    (.success (.of "FRESH__6")) 7 :=
  tryClauses_append_of_unmatch (twoFailedFresh 4) (.orElse_success .freshId)

example : Selected freshTestProgram [discardedFresh, discardedFresh, .freshId]
    4 2 (.of "FRESH__6") 7 :=
  .next (.bind_success .freshId .unmatch)
    (.next (.bind_success .freshId .unmatch) (.here .freshId))

example {plan : Action Unit} {start final : Nat} {outcome : Outcome Value}
    (h : Eval freshTestProgram plan start outcome final) : start ≤ final :=
  supply_monotone h

end SpecTecExecution
