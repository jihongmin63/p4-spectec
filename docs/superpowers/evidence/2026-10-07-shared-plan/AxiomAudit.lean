import Lean
import SpecTecProofs
#print axioms SpecTecPlan.ProgramOf.compiled_iff
#print axioms SpecTecPlan.Plan.premises_iff
#print axioms SpecTecPlan.Plan.eval_premises_sound
#print axioms SpecTecPlan.Alternative.toEvalRule
#print axioms SpecTecPlan.ProgramOf.holds_cases
#print axioms SpecTecPlan.checkSuccessWith_sound
#print axioms SpecTec.Program_ok.selected_sound
#print axioms SpecTec.Program_ok.ruleCases
#print axioms SpecTec.«$empty_typeFrame».selected_sound
#print axioms SpecTec.«$empty_typeFrame».ruleCases
#print axioms SpecTec.«Decl_ok:supply».ruleCases

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  let mut union : NameSet := {}
  for (name, info) in env.constants.toList do
    if name.toString.startsWith "SpecTec" && info.isTheorem then
      let axioms ← collectAxioms name
      for axiomName in axioms do
        unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
          throwError "unapproved axiom {axiomName} in {name}"
        union := union.insert axiomName
      count := count + 1
  logInfo m!"Audited all {count} SpecTec namespace-family theorems; axiom union: {union.toArray.qsort Name.lt}"
