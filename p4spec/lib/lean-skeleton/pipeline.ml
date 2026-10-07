module S = Ast.SpecTec

let ( let* ) = Result.bind

type mode = RelationLocal | FreshExactCounter | FreshRollback

let print ?(mode = RelationLocal) program =
  let fresh_rollback = mode = FreshRollback in
  try
    let* analysis = match mode with
      | RelationLocal -> Relation_graph.analyze program |> Result.map Option.some
      | FreshExactCounter | FreshRollback -> Ok None
    in
    Ok (Printer.print ~fresh_rollback
      ~relation_local:(mode = RelationLocal) ?analysis program)
  with Fresh_alpha.Unsupported message ->
    Error (Diagnostic.error ~source:"lean" Util.Source.no_region
      ("fresh abstraction: " ^ message))

let transpile ?(mode = RelationLocal) (input : S.spec) :
    (string, Diagnostic.t) result =
  let fresh_counter = mode <> RelationLocal in
  let fresh_rollback = mode = FreshRollback in
  let* lean_ast = Translator.translate ~fresh_counter ~fresh_rollback input in
  let* ordered = Order.order lean_ast in
  print ~mode ordered

let transpile_all ?(mode = RelationLocal) (input : S.spec) : string * Diagnostic.t list =
  let fresh_counter = mode <> RelationLocal in
  let fresh_rollback = mode = FreshRollback in
  let (lean_ast, diagnostics) :
      Ast.Lean.located_declaration list * Diagnostic.t list =
    Translator.translate_all ~fresh_counter ~fresh_rollback input
  in
  let (ordered, ordering_diagnostics) :
      Ast.Lean.program * Diagnostic.t list = Order.order_all lean_ast
  in
  match print ~mode ordered with
  | Ok source -> source, diagnostics @ ordering_diagnostics
  | Error diagnostic -> "", diagnostics @ ordering_diagnostics @ [diagnostic]

let relation_graph (input : S.spec) : (string, Diagnostic.t) result =
  let* lean_ast = Translator.translate input in
  let* ordered = Order.order lean_ast in
  let* analysis = Relation_graph.analyze ordered in
  Ok (Relation_graph.render analysis)
