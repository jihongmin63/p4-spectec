example : DecidableEq SpecTec.color := inferInstance

example : decide (SpecTec.color.RED = SpecTec.color.RED) = true := by decide

example : decide (SpecTec.color.RED = SpecTec.color.BLUE) = false := by decide

def nestedLeft : SpecTec.node :=
  .MANY [.BRANCH (.PAIRED (.BRANCH (.LEAF 1), .BRANCH (.LEAF 2)))]

def nestedRight : SpecTec.node :=
  .MANY [.BRANCH (.PAIRED (.BRANCH (.LEAF 1), .BRANCH (.LEAF 3)))]

example : decide (nestedLeft = nestedLeft) = true := by decide

example : decide (nestedLeft = nestedRight) = false := by decide

def tripleFirst : SpecTec.node :=
  .TRIPLE (.BRANCH (.LEAF 1), .BRANCH (.LEAF 2), .BRANCH (.LEAF 3))

def tripleSecondDiff : SpecTec.node :=
  .TRIPLE (.BRANCH (.LEAF 1), .BRANCH (.LEAF 4), .BRANCH (.LEAF 3))

def tripleThirdDiff : SpecTec.node :=
  .TRIPLE (.BRANCH (.LEAF 1), .BRANCH (.LEAF 2), .BRANCH (.LEAF 4))

example : decide (tripleFirst = tripleSecondDiff) = false := by decide

example : decide (tripleFirst = tripleThirdDiff) = false := by decide

example : decide (SpecTec.node.MAYBE none = SpecTec.node.MAYBE none) = true := by
  decide

example :
    decide
      (SpecTec.node.BOXED (.BOX (.BRANCH (.LEAF 1))) =
       SpecTec.node.BOXED (.BOX (.BRANCH (.LEAF 2)))) = false := by
  decide

example :
    decide
      (SpecTec.node.ALIASED [.BRANCH (.LEAF 1)] =
       SpecTec.node.ALIASED [.BRANCH (.LEAF 2)]) = false := by
  decide

example :
    SpecTec.«$eq_color» SpecTec.color.RED SpecTec.color.RED true := by
  exact SpecTec.«$eq_color».case_1 SpecTec.color.RED SpecTec.color.RED

example :
    SpecTec.«$eq_color» SpecTec.color.RED SpecTec.color.BLUE false := by
  exact SpecTec.«$eq_color».case_1 SpecTec.color.RED SpecTec.color.BLUE

example :
    SpecTec.«$ne_color» SpecTec.color.RED SpecTec.color.BLUE true := by
  exact SpecTec.«$ne_color».case_1 SpecTec.color.RED SpecTec.color.BLUE

example :
    SpecTec.«$ne_color» SpecTec.color.RED SpecTec.color.RED false := by
  exact SpecTec.«$ne_color».case_1 SpecTec.color.RED SpecTec.color.RED

example :
    SpecTec.«$in_set» SpecTec.color.RED
      (SpecTec.set.«`{ % `}» [SpecTec.color.RED]) true := by
  exact SpecTec.«$in_set».case_1 SpecTec.color.RED [SpecTec.color.RED]

example :
    SpecTec.«$in_set» SpecTec.color.RED
      (SpecTec.set.«`{ % `}» [SpecTec.color.BLUE]) false := by
  exact SpecTec.«$in_set».case_1 SpecTec.color.RED [SpecTec.color.BLUE]

example :
    SpecTec.«$in_set_via» SpecTec.color.RED
      (SpecTec.set.«`{ % `}» [SpecTec.color.RED]) true := by
  apply SpecTec.«$in_set_via».case_1
  exact SpecTec.«$in_set».case_1 SpecTec.color.RED [SpecTec.color.RED]

inductive NoEq where
  | value

example : SpecTec.«$is_empty» ([] : List NoEq) true := by
  exact SpecTec.«$is_empty».case_1 ([] : List NoEq)

example : SpecTec.«$is_empty» ([.value] : List NoEq) false := by
  exact SpecTec.«$is_empty».case_1 ([.value] : List NoEq)

example : SpecTec.«$is_nonempty» ([] : List NoEq) false := by
  exact SpecTec.«$is_nonempty».case_1 ([] : List NoEq)

example : SpecTec.«$is_nonempty» ([.value] : List NoEq) true := by
  exact SpecTec.«$is_nonempty».case_1 ([.value] : List NoEq)

example : SpecTec.«$is_none» (none : Option NoEq) true := by
  exact SpecTec.«$is_none».case_1 (none : Option NoEq)

example : SpecTec.«$is_none» (some .value : Option NoEq) false := by
  exact SpecTec.«$is_none».case_1 (some .value : Option NoEq)

example : SpecTec.«$is_some» (none : Option NoEq) false := by
  exact SpecTec.«$is_some».case_1 (none : Option NoEq)

example : SpecTec.«$is_some» (some .value : Option NoEq) true := by
  exact SpecTec.«$is_some».case_1 (some .value : Option NoEq)
