namespace SpecTec
open SpecTecExecution

#guard (runEval specTecExecutableProgram 20
  (.call (Call.Choose 7)) 0 == .done (.success 1) 0)
#guard (runEval specTecExecutableProgram 20
  (.call (Call.Caller 7)) 0 == .done (.success 30) 0)
#guard (runEval specTecExecutableProgram 20
  (.call (Call.Guarded 0)) 0 == .done (.success 10) 0)
#guard (runEval specTecExecutableProgram 20
  (.call (Call.Guarded 2)) 0 == .done (.success 11) 0)

/-- info: true -/
#guard_msgs in
#eval runEval specTecExecutableProgram 20
  (.call (Call.Caller 7)) 0 == .done (.success 30) 0

theorem caller_by_execution : Caller 7 30 :=
  ⟨0, runEval_sound specTecExecutableProgram 20
    (.call (Call.Caller 7)) 0 (.success 30) 0 rfl⟩

theorem choice_by_execution : Choose 7 1 :=
  ⟨0, runEval_sound specTecExecutableProgram 20
    (.call (Call.Choose 7)) 0 (.success 1) 0 rfl⟩

theorem guarded_first_by_execution : Guarded 0 10 :=
  ⟨0, runEval_sound specTecExecutableProgram 20
    (.call (Call.Guarded 0)) 0 (.success 10) 0 rfl⟩

theorem guarded_fallback_by_execution : Guarded 2 11 :=
  ⟨0, runEval_sound specTecExecutableProgram 20
    (.call (Call.Guarded 2)) 0 (.success 11) 0 rfl⟩

end SpecTec
