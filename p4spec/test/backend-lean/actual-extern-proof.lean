namespace SpecTec

variable [SpecTecExternTypes] [SpecTecP4ExternModel]

private def actualExternAllowed : Atom → Prop
  | .«$init_archState» state => SpecTecExternTypes.validArchState state
  | .«$init_objectState» _ _ _ _ state => SpecTecExternTypes.validObjectState state
  | .ExternFunctionCall_eval_lctk ctx name args result =>
      externStaticAllowed ctx name args result
  | .ExternFunctionCall_eval ctx₀ arch₀ name args ctx₁ arch₁ result =>
      externFunctionAllowed ctx₀ arch₀ name args ctx₁ arch₁ result
  | .ExternMethodCall_eval ctx₀ arch₀ object name args ctx₁ arch₁ result =>
      externMethodAllowed ctx₀ arch₀ object name args ctx₁ arch₁ result
  | .relation_call _ _ _ => True

private theorem actual_extern_sound (atom : Atom)
    (proof : SpecTecWFS.Holds InProgram atom) : actualExternAllowed atom := by
  apply SpecTecWFS.Holds.sound (interpretation := actualExternAllowed) proof
  intro rule inProgram side positive negative
  cases inProgram <;> simp_all [actualExternAllowed, SpecTecWFS.All]

example (state : archState) :
    «$init_archState» state ↔ SpecTecExternTypes.validArchState state := by
  constructor
  · intro proof; exact actual_extern_sound _ proof
  · intro valid; exact «$init_archState».allowed state valid

example (name : nameIR) (types : List typeIR) (ids : List id)
    (values : List value) (state : objectState) :
    «$init_objectState» name types ids values state ↔
      SpecTecExternTypes.validObjectState state := by
  constructor
  · intro proof; exact actual_extern_sound _ proof
  · intro valid
    exact «$init_objectState».allowed name types ids values state valid

example (ctx : typingContext) (name : nameIR) (args : List nameIR)
    (result : value) :
    ExternFunctionCall_eval_lctk ctx name args result ↔
      externStaticAllowed ctx name args result := by
  constructor
  · intro proof; exact actual_extern_sound _ proof
  · intro valid
    exact ExternFunctionCall_eval_lctk.allowed ctx name args result valid

example (ctx₀ ctx₁ : evalContext) (arch₀ arch₁ : arch)
    (name : nameIR) (args : List nameIR) (result : callResult) :
    ExternFunctionCall_eval ctx₀ arch₀ name args ctx₁ arch₁ result ↔
      externFunctionAllowed ctx₀ arch₀ name args ctx₁ arch₁ result := by
  constructor
  · intro proof; exact actual_extern_sound _ proof
  · intro valid
    exact ExternFunctionCall_eval.allowed ctx₀ arch₀ name args ctx₁ arch₁ result valid

example (ctx₀ ctx₁ : evalContext) (arch₀ arch₁ : arch)
    (object : objectId) (name : nameIR) (args : List nameIR)
    (result : callResult) :
    ExternMethodCall_eval ctx₀ arch₀ object name args ctx₁ arch₁ result ↔
      externMethodAllowed ctx₀ arch₀ object name args ctx₁ arch₁ result := by
  constructor
  · intro proof; exact actual_extern_sound _ proof
  · intro valid
    exact ExternMethodCall_eval.allowed ctx₀ arch₀ object name args ctx₁ arch₁ result valid

end SpecTec
