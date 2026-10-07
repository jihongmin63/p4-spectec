namespace SpecTec

variable [SpecTecExternTypes] [SpecTecP4ExternModel]

private def externAllowed : Atom → Prop
  | .«$init_archState» state => SpecTecExternTypes.validArchState state
  | .«$init_objectState» _ _ _ _ state => SpecTecExternTypes.validObjectState state
  | .Call_extern_func _ _ _ _ => True
  | .Call_builtin_func _ _ _ _ => True
  | .Call_extern_rel _ _ _ => True
  | .ExternFunctionCall_eval_lctk ctx name args result =>
      externStaticAllowed ctx name args result
  | .ExternFunctionCall_eval ctx₀ arch₀ name args ctx₁ arch₁ result =>
      externFunctionAllowed ctx₀ arch₀ name args ctx₁ arch₁ result
  | .ExternMethodCall_eval ctx₀ arch₀ object name args ctx₁ arch₁ result =>
      externMethodAllowed ctx₀ arch₀ object name args ctx₁ arch₁ result
  | .relation_call _ _ _ => True

private theorem extern_sound (atom : Atom) (proof : SpecTecWFS.Holds InProgram atom) :
    externAllowed atom := by
  apply SpecTecWFS.Holds.sound (interpretation := externAllowed) proof
  intro rule inProgram side positive negative
  cases inProgram <;> simp_all [externAllowed, SpecTecWFS.All]

example (state : archState) :
    «$init_archState» state ↔ SpecTecExternTypes.validArchState state := by
  constructor
  · intro proof
    exact extern_sound _ proof
  · intro valid
    exact «$init_archState».allowed state valid

example (name : nameIR) (types : List typeIR) (ids : List id)
    (values : List value) (state : objectState) :
    «$init_objectState» name types ids values state ↔
      SpecTecExternTypes.validObjectState state := by
  constructor
  · intro proof
    exact extern_sound _ proof
  · intro valid
    exact «$init_objectState».allowed name types ids values state valid

example (name : id) (types : List typ) (args : List val) (result : res val) :
    Call_extern_func name types args result ↔ True := by
  constructor
  · intro _; trivial
  · intro _; exact Call_extern_func.allowed name types args result

example (name : id) (types : List typ) (args : List val) (result : res val) :
    Call_builtin_func name types args result ↔ True := by
  constructor
  · intro _; trivial
  · intro _; exact Call_builtin_func.allowed name types args result

example (name : id) (args : List val) (result : res (List val)) :
    Call_extern_rel name args result ↔ True := by
  constructor
  · intro _; trivial
  · intro _; exact Call_extern_rel.allowed name args result

example (expected : typeIR) (v : value) :
    externCallResultValid expected (.RETURN (some v)) ↔
      SpecTecP4ExternModel.valueHasType expected v := Iff.rfl

example (expected : typeIR) :
    externCallResultValid expected (.RETURN none) ↔
      SpecTecP4ExternModel.voidReturnType expected := Iff.rfl

example (state : archState) (invalid : ¬ SpecTecExternTypes.validArchState state) :
    ¬ «$init_archState» state := by
  intro proof
  exact invalid (extern_sound _ proof)

example (ctx₀ ctx₁ : evalContext) (arch₀ arch₁ : arch)
    (name : nameIR) (args : List nameIR) (result : callResult)
    (invalid : ¬ SpecTecExternTypes.validArchState arch₀.STATE) :
    ¬ ExternFunctionCall_eval ctx₀ arch₀ name args ctx₁ arch₁ result := by
  intro proof
  obtain ⟨_, _, _, _, valid, _⟩ := extern_sound _ proof
  exact invalid valid

example (ctx₀ ctx₁ : evalContext) (arch₀ arch₁ : arch)
    (object : objectId) (name : nameIR) (args : List nameIR)
    (result : callResult)
    (invalid : ¬ SpecTecP4ExternModel.validObject arch₀ object) :
    ¬ ExternMethodCall_eval ctx₀ arch₀ object name args ctx₁ arch₁ result := by
  intro proof
  obtain ⟨_, _, _, _, _, _, valid, _⟩ := extern_sound _ proof
  exact invalid valid

example (ctx₀ ctx₁ : evalContext) (arch₀ arch₁ : arch)
    (name : nameIR) (args : List nameIR) (value : value)
    (notTyped : ∀ expected,
      SpecTecP4ExternModel.functionReturnType ctx₀ arch₀ name args expected →
      ¬ SpecTecP4ExternModel.valueHasType expected value) :
    ¬ ExternFunctionCall_eval ctx₀ arch₀ name args ctx₁ arch₁
        (.RETURN (some value)) := by
  intro proof
  obtain ⟨_, _, _, _, _, _, expected, expectedType, resultType⟩ :=
    extern_sound _ proof
  exact notTyped expected expectedType resultType

example (ctx : typingContext) (args : List nameIR) (value : value)
    (allowed : externStaticAllowed ctx (.NAME "static_assert") args value) :
    ExternFunctionCall_eval_lctk ctx (.NAME "static_assert") args value := by
  exact ExternFunctionCall_eval_lctk.allowed ctx _ args value allowed

example (ctx : typingContext) (name : nameIR) (args : List nameIR)
    (result : value) :
    ExternFunctionCall_eval_lctk ctx name args result ↔
      externStaticAllowed ctx name args result := by
  constructor
  · intro proof
    exact extern_sound _ proof
  · intro allowed
    exact ExternFunctionCall_eval_lctk.allowed ctx name args result allowed

example (ctx₀ ctx₁ : evalContext) (arch₀ arch₁ : arch)
    (name : nameIR) (args : List nameIR) (result : callResult) :
    ExternFunctionCall_eval ctx₀ arch₀ name args ctx₁ arch₁ result ↔
      externFunctionAllowed ctx₀ arch₀ name args ctx₁ arch₁ result := by
  constructor
  · intro proof
    exact extern_sound _ proof
  · intro allowed
    exact ExternFunctionCall_eval.allowed ctx₀ arch₀ name args ctx₁ arch₁ result allowed

example (ctx₀ ctx₁ : evalContext) (arch₀ arch₁ : arch)
    (object : objectId) (name : nameIR) (args : List nameIR)
    (result : callResult) :
    ExternMethodCall_eval ctx₀ arch₀ object name args ctx₁ arch₁ result ↔
      externMethodAllowed ctx₀ arch₀ object name args ctx₁ arch₁ result := by
  constructor
  · intro proof
    exact extern_sound _ proof
  · intro allowed
    exact ExternMethodCall_eval.allowed ctx₀ arch₀ object name args ctx₁ arch₁ result allowed

end SpecTec
