namespace SpecTec
example : Check .EXP true := Check.after .EXP (Check.expression .EXP)
example : Check .EXP false := Check.expression .EXP
example : Check .EXP true := Check.guard .EXP true rfl
end SpecTec
