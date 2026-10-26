module S = Ast.SpecTec

let ( let* ) = Result.bind

let transpile ?(ordered = true) ?(executable = false) (input : S.spec) :
    (string, Diagnostic.t) result =
  if ordered then Execution_translate.transpile ~executable input else
  let* lean_ast = Translator.translate input in
  let* ordered = Order.order lean_ast in
  Ok (Printer.print ordered)

let transpile_all ?(ordered = true) ?(executable = false) (input : S.spec) : string * Diagnostic.t list =
  if ordered then Execution_translate.transpile_all ~executable input else
  let (lean_ast, diagnostics) :
      Ast.Lean.located_declaration list * Diagnostic.t list =
    Translator.translate_all input
  in
  let (ordered, ordering_diagnostics) :
      Ast.Lean.program * Diagnostic.t list = Order.order_all lean_ast
  in
  (Printer.print ordered, diagnostics @ ordering_diagnostics)
