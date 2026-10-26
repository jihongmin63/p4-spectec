/- Checked against the complete supported output of the repository spec.
   This is distinct from the reduced ordered-choice fixture. -/
namespace SpecTec
open SpecTecExecution

syntax "prove_execution" : tactic
macro_rules
  | `(tactic| prove_execution) => `(tactic|
      first
        | refine ⟨0, ?_⟩; prove_execution
        | exact Eval.pure _
        | exact Eval.unmatch
        | apply Eval.guard_true; decide
        | apply Eval.guard_false; decide
        | apply Eval.call; prove_execution
        | apply Eval.orElse_success; prove_execution
        | apply Eval.orElse_unmatch; prove_execution; prove_execution
        | apply Eval.bind_success; prove_execution; prove_execution
        | apply Eval.bind_unmatch; prove_execution)

example : Cast_expl_neq typeIR.BOOL (typeIR.«BIT `< % `>» 1)
    (castResult.OK [typeIR.«BIT `< % `>» 1]) := by prove_execution
example : Cast_expl_neq typeIR.BOOL typeIR.STRING castResult.FAIL := by prove_execution
example : «$join_flow» flow.RET flow.RET flow.RET := by prove_execution
example : «$join_flow» flow.RET flow.CONT flow.CONT := by prove_execution
example : «$join_flow» flow.CONT flow.RET flow.CONT := by prove_execution
example : «$join_flow» flow.CONT flow.CONT flow.CONT := by prove_execution
end SpecTec
