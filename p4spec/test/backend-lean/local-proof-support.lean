namespace SpecTec
open SpecTecProof

/-- Inversion is inferred from `Decl_ok`'s own SCC.  There are no handlers for
    constant, instantiation, function, or action declaration relations. -/
theorem decl_error_inversion_local (n : Nat)
    (proof : Decl_ok (.ERRORDECLARATION n)) : ∃ m, n = m := by
  spec_invert proof with rule member head side positive negative
  cases member with
  | rule_0 m => simp at head
  | rule_1 m =>
      simp at head
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
  cases member <;> simp [declComponentProperty]

#print axioms decl_error_inversion_local
#print axioms decl_local_induction
end SpecTec
