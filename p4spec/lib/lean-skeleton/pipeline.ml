module S = Ast.SpecTec

let ( let* ) = Result.bind

let print ?(fresh_rollback = false) program =
  try Ok (Printer.print ~fresh_rollback program)
  with Fresh_alpha.Unsupported message ->
    Error (Diagnostic.error ~source:"lean" Util.Source.no_region
      ("fresh abstraction: " ^ message))

let transpile ?(fresh_rollback = false) (input : S.spec) :
    (string, Diagnostic.t) result =
  let* lean_ast = Translator.translate ~fresh_rollback input in
  let* ordered = Order.order lean_ast in
  print ~fresh_rollback ordered

let transpile_all ?(fresh_rollback = false) (input : S.spec) : string * Diagnostic.t list =
  let (lean_ast, diagnostics) :
      Ast.Lean.located_declaration list * Diagnostic.t list =
    Translator.translate_all ~fresh_rollback input
  in
  let (ordered, ordering_diagnostics) :
      Ast.Lean.program * Diagnostic.t list = Order.order_all lean_ast
  in
  match print ~fresh_rollback ordered with
  | Ok source -> source, diagnostics @ ordering_diagnostics
  | Error diagnostic -> "", diagnostics @ ordering_diagnostics @ [diagnostic]
