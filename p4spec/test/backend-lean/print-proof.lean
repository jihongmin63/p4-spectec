def printDefault : SpecTec.defaultCase :=
  .SHOW true (-7) none [] (1, (2, 3)) (1, (2, 3))

@[instance_reducible] def flatTriplePrinter : SpecTecPrint (Nat × (Nat × Nat)) :=
  { print? := fun value => match value with
    | (x0, (x1, x2)) => do
        let s0 ← SpecTecPrint.print? x0
        let s1 ← SpecTecPrint.print? x1
        let s2 ← SpecTecPrint.print? x2
        return "(" ++ ", ".intercalate [s0, s1, s2] ++ ")" }

@[instance_reducible] def wrapperTriplePrinter :
    SpecTecPrint (SpecTec.wrapper (Nat × (Nat × Nat))) :=
  { print? := @SpecTec.print_wrapper (Nat × (Nat × Nat)) flatTriplePrinter }

example :
    SpecTecPrint.print? printDefault =
      some "show true -7   (1, 2, 3) (1, (2, 3))" := by
  rfl

example :
    SpecTecPrint.print? (SpecTec.defaultCase._TAG "visible") =
      some "visible" := by
  rfl

example :
    SpecTecPrint.print? (SpecTec.hinted.CUR "first" "second") =
      some "second first" := by
  rfl

example :
    SpecTecPrint.print? (SpecTec.hinted.FUSE "x") =
      some "prexpost" := by
  rfl

example :
    SpecTecPrint.print? (SpecTec.hinted.BRACK "x") =
      some "( x )" := by
  rfl

example :
    SpecTecPrint.print? (SpecTec.hinted.EMPTY "x") =
      some " x " := by
  rfl

example :
    SpecTecPrint.print? (SpecTec.parent.CHILD "x") =
      some "child:x" := by
  rfl

example :
    SpecTecPrint.print? (SpecTec.wrapper.WRAP "x") =
      some "wrap x" := by
  rfl

example :
    SpecTecPrint.print? (SpecTec.wrapper.WRAP (SpecTec.leaf.LEAF "x")) =
      some "wrap leaf:x" := by
  rfl

def printRecursive : SpecTec.recA :=
  .A [.B (some (.A []))]

example :
    SpecTecPrint.print? printRecursive = some "a b a " := by
  rfl

example :
    SpecTecPrint.print? (-42 : Int) = some "-42" := by
  rfl

example :
    SpecTecPrint.print? (none : Option String) = some "" := by
  rfl

example :
    SpecTecPrint.print? ([] : List String) = some "" := by
  rfl

example :
    SpecTecPrint.print? "\"\\\n\t\r\u0008é" =
      some "\\\"\\\\\\n\\t\\r\\b\\195\\169" := by
  rfl

example :
    SpecTec.«$print_» printDefault
      "show true -7   (1, 2, 3) (1, (2, 3))" := by
  exact SpecTec.«$print_».success printDefault _ rfl

example :
    SpecTec.«$print_» (SpecTec.wrapper.WRAP (SpecTec.leaf.LEAF "x"))
      "wrap leaf:x" := by
  exact SpecTec.«$print_».success _ _ rfl

example : ∀ result, ¬ SpecTec.«$print_» (SpecTec.bad.mk 1) result := by
  intro result
  apply SpecTecWFS.Holds.not_of_rules
  intro rule inProgram side positive negative
  cases inProgram <;> simp_all [SpecTecWFS.All]
  intro hType hValue hResult
  cases hType
  cases hValue
  change (none : Option String) = some _ at side
  cases side

example : ∀ result,
    ¬ SpecTec.«$print_» (SpecTec.badWrapper.BAD (SpecTec.bad.mk 1)) result := by
  intro result
  apply SpecTecWFS.Holds.not_of_rules
  intro rule inProgram side positive negative
  cases inProgram <;> simp_all [SpecTecWFS.All]
  intro hType hValue hResult
  cases hType
  cases hValue
  change (none : Option String) = some _ at side
  cases side

example :
    SpecTecPrint.print? (SpecTec.skipsBad.SKIP (SpecTec.bad.mk 1)) =
      some "ok" := by
  rfl

example :
    SpecTec.«$print_» (SpecTec.skipsBad.SKIP (SpecTec.bad.mk 1)) "ok" := by
  exact SpecTec.«$print_».success _ _ rfl

example : SpecTec.«$render_flat_triple» (1, (2, 3)) "(1, 2, 3)" := by
  apply SpecTec.«$render_flat_triple».case_1
  exact @SpecTec.«$print_».success _ flatTriplePrinter _ _ rfl

example :
    SpecTec.«$render_wrapper_triple» (SpecTec.wrapper.WRAP (1, (2, 3)))
      "wrap (1, 2, 3)" := by
  apply SpecTec.«$render_wrapper_triple».case_1
  exact @SpecTec.«$print_».success _ wrapperTriplePrinter _ _ rfl

example :
    SpecTec.«$render_forwarded» (SpecTec.forwarded.FORWARDED "x")
      "forwarded x" := by
  apply SpecTec.«$render_forwarded».case_1
  apply SpecTec.«$render».case_1
  exact SpecTec.«$print_».success _ _ rfl

example :
    SpecTec.«$render_flat_triple_alias» (1, (2, 3)) "(1, 2, 3)" := by
  apply SpecTec.«$render_flat_triple_alias».case_1
  exact @SpecTec.«$print_».success _ flatTriplePrinter _ _ rfl

example :
    SpecTecPrint.print? (SpecTec.firstPrint.FIRST_PRINT ["a"]) =
      some "first_print a" := by
  rfl

example :
    SpecTecPrint.print? (SpecTec.secondPrint.SECOND_PRINT ["b"]) =
      some "second_print b" := by
  rfl

def nestedPrintTree : SpecTec.printTree :=
  .PRINT_NODE (.PRINT_BOX .PRINT_LEAF)

example : SpecTecPrint.print? nestedPrintTree =
    some "print_node print_box print_leaf" := by
  rfl

example :
    SpecTecPrint.print?
        (SpecTec.tripleHolder.TRIPLE_HOLD (SpecTec.wrapper.WRAP (1, (2, 3)))) =
      some "triple_hold wrap (1, 2, 3)" := by
  rfl

example :
    SpecTec.«$render_triple_holder»
      (SpecTec.tripleHolder.TRIPLE_HOLD (SpecTec.wrapper.WRAP (1, (2, 3))))
      "triple_hold wrap (1, 2, 3)" := by
  apply SpecTec.«$render_triple_holder».case_1
  exact SpecTec.«$print_».success _ _ rfl
