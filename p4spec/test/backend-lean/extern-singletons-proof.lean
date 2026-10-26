namespace SpecTec
example : json := .mk
example : archState := .mk
example : objectState := .mk
example : packetState := .mk
example (x y : json) : x = y := by cases x; cases y; rfl
example (x y : archState) : x = y := by cases x; cases y; rfl
example (x y : objectState) : x = y := by cases x; cases y; rfl
example (x y : packetState) : x = y := by cases x; cases y; rfl
example : DecidableEq packetState := inferInstance
#guard (packetState.mk == packetState.mk)
example : «$init_archState» archState.mk := .allowed _
end SpecTec
