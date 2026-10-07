namespace SpecTec

example :
    open Notation.A in
    notationType.NOTATION_TYPE -> notationType.NOTATION_TYPE
      : notationResult.NOTATION_RESULT := by
  exact A.base

example :
    open Notation.B in
    notationType.NOTATION_TYPE -> notationType.NOTATION_TYPE
      : notationResult.NOTATION_RESULT := by
  exact B.base

example :
    (open Notation.A in
      notationType.NOTATION_TYPE -> notationType.NOTATION_TYPE
        : notationResult.NOTATION_RESULT) ∧
    (open Notation.B in
      notationType.NOTATION_TYPE -> notationType.NOTATION_TYPE
        : notationResult.NOTATION_RESULT) := by
  exact ⟨A.base, B.base⟩

example :
    open Notation.Apply in
    notationType.NOTATION_TYPE -> notationType.NOTATION_TYPE
      : castResult.OK [] := by
  exact Apply.base

example :
    open Notation.Delimited in
    notationType.NOTATION_TYPE
      |- notationType.NOTATION_TYPE (notationType.NOTATION_TYPE)
      ~> notationResult.NOTATION_RESULT := by
  exact Delimited.base

example :
    open Notation.At in
    notationType.NOTATION_TYPE @ notationType.NOTATION_TYPE
      : notationResult.NOTATION_RESULT := by
  exact At.base

example :
    open Notation.AtTwice in
    notationType.NOTATION_TYPE
      |- notationType.NOTATION_TYPE @ notationType.NOTATION_TYPE
      : notationType.NOTATION_TYPE,
        notationType.NOTATION_TYPE @ notationResult.NOTATION_RESULT := by
  exact AtTwice.base

example :
    open Notation.Dot in
    notationType.NOTATION_TYPE . notationType.NOTATION_TYPE
      : notationResult.NOTATION_RESULT := by
  exact Dot.base

example :
    open Notation.DotCall in
    notationType.NOTATION_TYPE notationType.NOTATION_TYPE
      |- notationType.NOTATION_TYPE . notationType.NOTATION_TYPE
      (notationType.NOTATION_TYPE)
      : notationType.NOTATION_TYPE notationType.NOTATION_TYPE
        notationResult.NOTATION_RESULT := by
  exact DotCall.base

example :
    open Notation.Adjacent in
    cursor.CURSOR typingContext.TYPING_CONTEXT
      |- expression.EXPRESSION : notationType.NOTATION_TYPE := by
  exact Adjacent.base

example :
    A notationType.NOTATION_TYPE notationType.NOTATION_TYPE
      notationResult.NOTATION_RESULT := by
  exact A.base

open Notation.Adjacent in
example :
    cursor.CURSOR typingContext.TYPING_CONTEXT
      |- expression.EXPRESSION : notationType.NOTATION_TYPE ↔
    (Adjacent cursor.CURSOR typingContext.TYPING_CONTEXT
      expression.EXPRESSION notationType.NOTATION_TYPE) := Iff.rfl

open Notation.AdjacentOther in
example :
    cursor.CURSOR typingContext.TYPING_CONTEXT
      |- expression.EXPRESSION : notationType.NOTATION_TYPE ↔
    (AdjacentOther cursor.CURSOR typingContext.TYPING_CONTEXT
      expression.EXPRESSION notationType.NOTATION_TYPE) := Iff.rfl

/--
info: notationType.NOTATION_TYPE -> notationType.NOTATION_TYPE : notationResult.NOTATION_RESULT : Prop
-/
#guard_msgs in
open Notation.A in
#check A notationType.NOTATION_TYPE notationType.NOTATION_TYPE
  notationResult.NOTATION_RESULT

/--
info: cursor.CURSOR typingContext.TYPING_CONTEXT |- expression.EXPRESSION : notationType.NOTATION_TYPE : Prop
-/
#guard_msgs in
open Notation.Adjacent in
#check Adjacent cursor.CURSOR typingContext.TYPING_CONTEXT
  expression.EXPRESSION notationType.NOTATION_TYPE

end SpecTec
