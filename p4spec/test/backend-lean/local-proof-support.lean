namespace SpecTec
open SpecTecProof

/-- Inversion is inferred from `Decl_ok`'s own SCC.  There are no handlers for
    constant, instantiation, function, or action declaration relations. -/
theorem decl_error_inversion_local (n : Nat)
    (proof : Decl_ok (.ERRORDECLARATION n)) : ∃ m, n = m := by
  spec_invert proof with rule member head side positive negative
  rcases member with ⟨alternative, member, witness, rfl⟩
  cases member with
  | rule_0 =>
      rcases witness with ⟨m, rest⟩
      cases rest
      simp [«Decl_ok:Semantics».rule_0_plan, SpecTecPlan.Plan.compile] at head
  | rule_1 =>
      rcases witness with ⟨m, rest⟩
      cases rest
      simp [«Decl_ok:Semantics».rule_1_plan, SpecTecPlan.Plan.compile] at head
      exact ⟨m, head.symm⟩

/-- The induction principle is likewise selected by the supplied judgement,
    rather than by a program-wide membership registry. -/
private def declComponentProperty : «Decl_ok:Semantics».Atom → Prop
  | .Decl_ok _ => True
  | _ => True

theorem decl_local_induction (atom : «Decl_ok:Semantics».Atom)
    (proof : SpecTecWFS.Holds «Decl_ok:Semantics».InProgram atom) :
    declComponentProperty atom := by
  spec_induction proof with rule member side positive negative
  rcases member with ⟨alternative, member, witness, rfl⟩
  cases member <;> rcases witness with ⟨m, rest⟩ <;> cases rest <;> simp [declComponentProperty,
    «Decl_ok:Semantics».rule_0_plan, «Decl_ok:Semantics».rule_1_plan,
    SpecTecPlan.Plan.compile]

#print axioms decl_error_inversion_local
#print axioms decl_local_induction
end SpecTec

namespace SpecTec
open SpecTecProof

theorem typed_plan_inversion (n : Nat)
    (proof : Decl_ok (.ERRORDECLARATION n)) : ∃ m, n = m := by
  obtain ⟨alternative, member, witness, head, premises⟩ := Decl_ok.ruleCases _ proof
  spec_cases_allowed member <;> spec_unpack_witness witness <;> cases head
  exact ⟨n, rfl⟩

#print axioms typed_plan_inversion
end SpecTec

-- Destructing the first field rewrites the dependent tail's free variables.
-- The helper must not subsequently use their stale identifiers.
example (w : Sigma fun pair : Nat × Nat => Fin (pair.1 + 1) × Unit) :
    w.2.1.val < w.1.1 + 1 := by
  spec_unpack_witness w
  exact Fin.isLt _

namespace HeadNormalization
inductive Source where
  | value : Nat → Source
  | other
inductive Target where
  | value : Nat → Target
  | other
def cast : Source → Target
  | .value n => .value n
  | .other => .other
def delayed (input : Source) : SpecTecWFS.Rule Target :=
  (SpecTecPlan.Plan.ret (fun _ : Unit => cast input)).compile () ()

example (input : Source) (head : (delayed input).head = .value 0) :
    input = .value 0 := by
  spec_reduce_head head
  (repeat' split at head) <;> cases head
  rfl
end HeadNormalization
