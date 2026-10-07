namespace SpecTec

variable [SpecTecExternTypes]

example : Decl_ok (.ERRORDECLARATION 3) := Decl_ok.error 3

example (atom : Atom) :
    SpecTecWFS.Holds InProgram atom ↔ SpecTecWFS.Holds InProgram atom := by
  apply SpecTecWFS.Holds.program_congr
  intro rule
  rfl

end SpecTec
