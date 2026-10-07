import Lean
import SpecTecAll

open Lean in
private def eraseBinderNames : Expr → Expr
  | .forallE _ domain body info => .forallE .anonymous (eraseBinderNames domain) (eraseBinderNames body) info
  | .lam _ domain body info => .lam .anonymous (eraseBinderNames domain) (eraseBinderNames body) info
  | .letE _ type value body nondep => .letE .anonymous (eraseBinderNames type) (eraseBinderNames value) (eraseBinderNames body) nondep
  | .app fn arg => .app (eraseBinderNames fn) (eraseBinderNames arg)
  | .mdata _ body => eraseBinderNames body
  | .proj name index body => .proj name index (eraseBinderNames body)
  | expr => expr

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut types : Array Json := #[]
  let mut relations : Nat := 0
  for (name, _) in env.constants.toList do
    if let .str parent "fails" := name then
      if parent.getPrefix == `SpecTec then
        relations := relations + 1
        for exported in #[parent, name] do
          let some info := env.find? exported | throwError "missing public relation {exported}"
          types := types.push <| Json.arr #[Json.str exported.toString,
            Json.str (reprStr info.levelParams), Json.str (reprStr (eraseBinderNames info.type))]
  let some output ← IO.getEnv "P4_PUBLIC_TYPES_OUTPUT" | throwError "set P4_PUBLIC_TYPES_OUTPUT"
  IO.FS.writeFile output (Json.arr types |>.compress)
  logInfo m!"Exported kernel types for {relations} public relations and their Fails predicates"
