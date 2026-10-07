example :
    SpecTec.«$update_nested»
      (SpecTec.outerRecord.mk (SpecTec.innerRecord.mk 1 2) 3)
      (SpecTec.outerRecord.mk (SpecTec.innerRecord.mk 1 9) 3) := by
  exact SpecTec.«$update_nested».case_1 _

example :
    ¬ SpecTec.«$update_nested»
      (SpecTec.outerRecord.mk (SpecTec.innerRecord.mk 1 2) 3)
      (SpecTec.outerRecord.mk (SpecTec.innerRecord.mk 1 9) 4) := by
  intro h
  have impossible := SpecTecWFS.Holds.not_of_rules (program := SpecTec.InProgram)
    (SpecTec.Atom.«$update_nested»
      (SpecTec.outerRecord.mk (SpecTec.innerRecord.mk 1 2) 3)
      (SpecTec.outerRecord.mk (SpecTec.innerRecord.mk 1 9) 4))
    (by
      intro rule inProgram side positive negative
      cases inProgram <;> simp_all [SpecTecWFS.All])
  exact impossible h

example :
    ¬ SpecTec.«$update_nested»
      (SpecTec.outerRecord.mk (SpecTec.innerRecord.mk 1 2) 3)
      (SpecTec.outerRecord.mk (SpecTec.innerRecord.mk 4 9) 3) := by
  intro h
  have impossible := SpecTecWFS.Holds.not_of_rules (program := SpecTec.InProgram)
    (SpecTec.Atom.«$update_nested»
      (SpecTec.outerRecord.mk (SpecTec.innerRecord.mk 1 2) 3)
      (SpecTec.outerRecord.mk (SpecTec.innerRecord.mk 4 9) 3))
    (by
      intro rule inProgram side positive negative
      cases inProgram <;> simp_all [SpecTecWFS.All])
  exact impossible h

example : SpecTec.«$update_list» [1, 2, 3] 1 9 [1, 9, 3] := by
  apply SpecTec.«$update_list».case_1
  decide

example : ¬ SpecTec.«$update_list» [1, 2, 3] 3 9 [1, 2, 3] := by
  intro h
  let interpretation : SpecTec.Atom → Prop := fun atom =>
    match atom with
    | .«$update_list» ns idx _ _ => idx < ns.length
    | _ => True
  have valid := SpecTecWFS.Holds.sound (interpretation := interpretation) h (by
    intro rule inProgram side positive negative
    cases inProgram <;> simp_all [interpretation, SpecTecWFS.All])
  exact (by decide : ¬ (3 < ([1, 2, 3] : List Nat).length)) valid

example : SpecTec.«$update_text» "abc" 1 "x" "axc" := by
  exact SpecTec.«$update_text».case_1 "abc" 1 "x" "a" "c" "b"
    (by decide) (by decide) (by decide) (by decide)

example : ¬ SpecTec.«$update_text» "abc" 3 "x" "abc" := by
  apply SpecTecWFS.Holds.not_of_rules
  intro rule inProgram side positive negative
  cases inProgram <;> simp_all [SpecTecWFS.All]
  intro hwhole hidx hc hresult
  have size := congrArg String.utf8ByteSize hwhole
  simp only [String.utf8ByteSize_append] at size
  have literal_size : ("abc").utf8ByteSize = 3 := by decide
  omega

example : ¬ SpecTec.«$update_text» "abc" 1 "xy" "axyc" := by
  apply SpecTecWFS.Holds.not_of_rules
  intro rule inProgram side positive negative
  cases inProgram <;> simp_all [SpecTecWFS.All]
  intro hwhole hidx hc hresult
  have literal_size : ("xy").utf8ByteSize = 2 := by decide
  have size := congrArg String.utf8ByteSize hc
  omega
