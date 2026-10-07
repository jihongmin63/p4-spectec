-- Selector premises of concrete rows close by `rfl`.
example : SpecTec.«$is_small» (SpecTec.ty.WRAP "w" (SpecTec.ty.S2 3)) true :=
  .row_1 _ _ _ rfl (.row_0 _ rfl)

example : SpecTec.«$is_small» (SpecTec.ty.LIST []) true :=
  .row_2 [] true [] rfl .nil .case_1

-- Overlapping rows: (WRAP, WRAP) selects the earlier row, as the interpreter does.
example :
    SpecTec.«$compat:row» (SpecTec.ty.WRAP "a" SpecTec.ty.A)
      (SpecTec.ty.WRAP "b" SpecTec.ty.A) = 2 := rfl

example :
    SpecTec.«$compat» (SpecTec.ty.WRAP "a" SpecTec.ty.A)
      (SpecTec.ty.WRAP "b" SpecTec.ty.A) true :=
  .row_2 _ _ _ _ rfl (.row_3 _ _ _ _ rfl (.row_0 rfl))

-- The selector makes the relation functional.
private theorem bool_result_unique {predicate : Bool → Prop} {left right : Bool}
    (false_case : predicate false → left = false)
    (true_case : predicate true → left = true)
    (actual : predicate right) : left = right := by
  cases right with
  | false => exact false_case actual
  | true => exact true_case actual

theorem compat_deterministic {l r : SpecTec.ty} {b₁ b₂ : Bool}
    (h₁ : SpecTec.«$compat» l r b₁) (h₂ : SpecTec.«$compat» l r b₂) : b₁ = b₂ := by
  let interpretation : SpecTec.Atom → Prop := fun atom =>
    match atom with
    | .«$compat» left right result =>
        ∀ other, SpecTec.«$compat» left right other → result = other
    | _ => True
  have deterministic := SpecTecWFS.Holds.sound
    (interpretation := interpretation) h₁ (by
      intro rule inProgram side positive negative
      cases inProgram <;> dsimp [interpretation, SpecTecWFS.All] at *
      all_goals
        intro other derived
        obtain ⟨nextRule, nextInProgram, head, nextSide, nextPositive, nextNegative⟩ :=
          SpecTecWFS.Holds.cases derived
        cases nextInProgram <;>
          simp_all [SpecTecWFS.All, SpecTec.«$compat:row»]
        all_goals
          rcases head with ⟨left, right, result⟩
          try simp_all
          try subst_vars
          try (cases other <;> simp_all [SpecTec.«$compat:row»])
          try (cases ty_l <;> simp_all [SpecTec.«$compat:row»])
      all_goals try simp_all [SpecTec.«$compat»]
      all_goals try (simp_all [SpecTec.«$compat:row»])
      case rule_10.rule_10 =>
        exact bool_result_unique
          (predicate := fun b => SpecTecWFS.Holds SpecTec.InProgram
            (SpecTec.Atom.«$compat» _ _ b))
          positive.1 positive.2 nextPositive
      case rule_11.rule_11 =>
        exact bool_result_unique
          (predicate := fun b => SpecTecWFS.Holds SpecTec.InProgram
            (SpecTec.Atom.«$compat» _ _ b))
          positive.1 positive.2 nextPositive)
  exact deterministic b₂ h₂

-- Inversion works on the subtype row: its conclusion has no coercion.
example : ¬ SpecTec.«$is_small» SpecTec.ty.A true := by
  apply SpecTecWFS.Holds.not_of_rules
  intro rule inProgram side positive negative
  cases inProgram <;> simp_all [SpecTecWFS.All, SpecTec.«$is_small:row»]
  case rule_2 small =>
    cases small <;> simp_all

-- Exhaustive rows without a catch-all row.
example : SpecTec.«$is_warm» SpecTec.color.BLUE false := .row_2 rfl

-- A partial table has no derivation outside its rows.
example : ¬ ∃ b, SpecTec.«$is_red» SpecTec.color.GREEN b := by
  rintro ⟨b, h⟩
  have impossible := SpecTecWFS.Holds.not_of_rules
    (program := SpecTec.InProgram) (SpecTec.Atom.«$is_red» .GREEN b)
    (by
      intro rule inProgram side positive negative
      cases inProgram <;> simp_all [SpecTecWFS.All])
  exact impossible h

-- A parameterless table has a constant fallback selector.
example : SpecTec.«$never:row» = 0 := rfl

example : ¬ ∃ b, SpecTec.«$never» b := by
  rintro ⟨b, h⟩
  have impossible := SpecTecWFS.Holds.not_of_rules
    (program := SpecTec.InProgram) (SpecTec.Atom.«$never» b)
    (by
      intro rule inProgram side positive negative
      cases inProgram <;> simp_all [SpecTecWFS.All])
  exact impossible h

-- Callers: a premise and a function argument.
example : SpecTec.Small_ok SpecTec.ty.S1 := .table _ _ (.row_0 _ rfl) rfl

example : SpecTec.«$wrapped_small» SpecTec.ty.S1 true :=
  .case_1 _ _
    (SpecTec.«$apply_check».case_1 _ _ _
      (SpecTec.«$is_small».dispatch _ _
        (SpecTec.«$is_small».row_1 _ _ _ rfl
          (SpecTec.«$is_small».row_0 _ rfl))))
