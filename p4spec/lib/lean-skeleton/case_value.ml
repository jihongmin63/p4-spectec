(** Translate runtime trees against declared field types, not runtime notes. *)
module L = Ast.Lean
module V = Runtime.Value
module T = Translator
open Util.Source

let unsupported value message = T.unsupported value.at ("test case value " ^ message)

let field_name atom = match atom.it with
  | Domain.Atom.Keyword name -> name
  | Domain.Atom.Tag name -> "_" ^ name
  | atom -> Domain.Atom.string_of_atom atom

let rec translate env typ (value : V.t) =
  let shape = T.expand_expression_type env value.at typ in
  let recurse = translate env in
  match value.it, shape with
  | BoolV boolean, _ -> L.Boolean boolean
  | TextV text, _ -> L.Text text
  | NumV number, _ ->
      let text = Lang.Xl.Num.string_of_num number in
      let text = if String.starts_with ~prefix:"+" text then
          String.sub text 1 (String.length text - 1) else text in
      L.Number (text, typ)
  | ListV values, L.BuiltinType ("List", [element]) ->
      L.Typed (L.ListLiteral (List.map (recurse element) values), typ)
  | OptV None, L.BuiltinType ("Option", [_]) ->
      L.Typed (L.Native ("Option.none", []), typ)
  | OptV (Some value), L.BuiltinType ("Option", [element]) ->
      L.Native ("Option.some", [recurse element value])
  | TupleV values, L.TupleType elements when List.length values = List.length elements && List.length values >= 2 ->
      T.nest_pairs (fun left right -> L.Tuple (left, right)) (List.map2 recurse elements values)
  | CaseV notation, (L.Name _ | L.Applied _) ->
      let name, arguments = match shape with
        | L.Name name -> name, [] | L.Applied (name, arguments) -> name, arguments
        | _ -> assert false in
      let mixop = Domain.Mixfix.to_mixop notation in
      let constructor = T.constructor_reference env value.at name arguments mixop in
      let variant = T.StringMap.find constructor.type_name env.T.constructors in
      let _, _, fields = List.find (fun (candidate, _, _) -> Domain.Mixfix.eq_mixop candidate mixop) variant.cases in
      let substitution = List.combine variant.type_parameters constructor.type_arguments in
      let fields = List.map (fun field ->
          T.translate_type_with_parameters variant.type_parameters field
          |> T.substitute_type_parameters substitution) fields in
      let values = Domain.Mixfix.args notation in
      if List.length fields <> List.length values then unsupported value "constructor argument arity";
      L.Constructor (constructor, List.map2 recurse fields values)
  | StructV values, L.Name name ->
      let fields = match T.StringMap.find_opt name env.T.structures with
        | Some fields -> fields | None -> unsupported value "structure without a declaration" in
      let values = List.map (fun (atom, value) ->
          let name = field_name atom in
          let field = match List.find_opt (fun (field : T.structure_field) -> field.name = name) fields with
            | Some field -> field | None -> unsupported value ("unknown structure field " ^ name) in
          name, recurse (T.translate_type field.typ) value) values in
      L.StructureLiteral (typ, values)
  | FuncV _, _ -> unsupported value "function reference"
  | ExternV _, _ -> unsupported value "external value"
  | _ -> unsupported value ("shape mismatch for " ^ Printer.print_type [] typ)
