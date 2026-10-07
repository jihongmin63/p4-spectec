module S = Ast.SpecTec
module L = Ast.Lean
module V = Runtime.Value
module Mixfix = Domain.Mixfix
open Util.Source

type expectation = Accept | Reject | AbortReject

type case = {
  source : string;
  expectation : expectation;
  expected : string option;
  value : V.t;
  fresh_context : (string list * string list) option;
}

let unsupported (value : V.t) (kind : string) : 'a =
  Translator.unsupported value.at ("test case value " ^ kind)

let rec translate_value (env : Translator.env) (typ : L.type_ref)
    (value : V.t) : L.term =
  let recurse typ value = translate_value env typ value in
  let shape = Translator.expand_expression_type env value.at typ in
  match value.it with
  | BoolV boolean -> L.Boolean boolean
  | NumV number ->
      let printed = Lang.Xl.Num.string_of_num number in
      let printed =
        if String.starts_with ~prefix:"+" printed then
          String.sub printed 1 (String.length printed - 1)
        else printed
      in
      L.Number (printed, typ)
  | TextV string -> L.Text string
  | CaseV notation ->
      let name, type_arguments = match shape with
        | L.Name name -> name, []
        | L.Applied (name, arguments) -> name, arguments
        | _ -> unsupported value "constructor without a variant type"
      in
      let mixop = Mixfix.to_mixop notation in
      let reference =
        Translator.constructor_reference env value.at name type_arguments mixop
      in
      let variant = Translator.StringMap.find reference.type_name env.constructors in
      let formal_arguments =
        match List.find_opt
          (fun (candidate, _, _) -> Mixfix.eq_mixop candidate mixop)
          variant.cases with
        | Some (_, _, arguments) -> arguments
        | None -> unsupported value "constructor argument types"
      in
      let bindings = List.combine variant.type_parameters reference.type_arguments in
      let argument_types =
        List.map
          (fun argument ->
            Translator.translate_type_with_parameters variant.type_parameters argument
            |> Translator.substitute_type_parameters bindings)
          formal_arguments
      in
      let arguments = Mixfix.args notation in
      if List.length argument_types <> List.length arguments then
        unsupported value "constructor argument arity";
      L.Constructor (reference, List.map2 recurse argument_types arguments)
  | StructV fields ->
      let field_name atom =
        match atom.it with
        | Domain.Atom.Keyword name -> name
        | Domain.Atom.Tag name -> "_" ^ name
        | other -> Domain.Atom.string_of_atom other
      in
      let name = match shape with
        | L.Name name -> name
        | _ -> unsupported value "structure without a named type"
      in
      let definitions =
        match Translator.StringMap.find_opt name env.structures with
        | Some definitions -> definitions
        | None -> unsupported value "structure without a declaration"
      in
      let translate_field (atom, field) =
        let name = field_name atom in
        let definition =
          match List.find_opt
            (fun (candidate : Translator.structure_field) -> candidate.name = name)
            definitions with
          | Some definition -> definition
          | None -> unsupported field ("unknown structure field " ^ name)
        in
        name, recurse (Translator.translate_type definition.typ) field
      in
      L.StructureLiteral (typ, List.map translate_field fields)
  | TupleV values -> (
      match shape with
      | L.TupleType types when List.length types = List.length values ->
          (match List.map2 recurse types values with
          | _ :: _ :: _ as terms -> Translator.nest_pairs (fun x y -> L.Tuple (x, y)) terms
          | _ -> unsupported value "tuple with fewer than two elements")
      | _ -> unsupported value "tuple type mismatch")
  | OptV None -> L.Typed (L.Native ("Option.none", []), typ)
  | OptV (Some inner) -> (
      match shape with
      | L.BuiltinType ("Option", [ element ]) ->
          L.Native ("Option.some", [ recurse element inner ])
      | _ -> unsupported value "option type mismatch")
  | ListV values -> (
      match shape with
      | L.BuiltinType ("List", [ element ]) ->
          L.Typed (L.ListLiteral (List.map (recurse element) values), typ)
      | _ ->
          unsupported value
            ("list type mismatch: expected " ^ Printer.print_type [] typ
             ^ ", runtime "
             ^ S.Print.string_of_typ (value.note.typ $ value.at)))
  | FuncV _ -> unsupported value "function reference"
  | ExternV _ -> unsupported value "external value"

let render_case (env : Translator.env) (index : int) (case : case) : string =
  let name = "case_" ^ string_of_int index in
  let input = Printer.print_term []
    (translate_value env (L.Name "p4program") case.value) in
  let expected_definition, proposition = match case.expectation, case.expected with
    | Accept, Some expected ->
        let expected_definition =
          "def " ^ name ^ "_expected : p4programIR := " ^ expected ^ "\n" in
        (match case.fresh_context with
        | None ->
            (expected_definition,
             "Program_ok " ^ name ^ "_input " ^ name ^ "_expected ∧\n"
             ^ "  ∀ output : p4programIR, Program_ok " ^ name
             ^ "_input output → output = " ^ name ^ "_expected")
        | Some (allocated, protected) ->
            let names suffix values = "def " ^ name ^ suffix
              ^ " : List String := "
              ^ Printer.print_term [] (L.ListLiteral (List.map (fun s -> L.Text s) values))
              ^ "\n" in
            let alpha = "FreshAlphaIR " ^ name ^ "_fresh_names " ^ name
              ^ "_protected_names " ^ name ^ "_expected output" in
            (expected_definition ^ names "_fresh_names" allocated
               ^ names "_protected_names" protected,
             "(∃ output : p4programIR, Program_ok " ^ name ^ "_input output ∧\n"
             ^ "    " ^ alpha ^ ") ∧\n"
             ^ "  ∀ output : p4programIR, Program_ok " ^ name
             ^ "_input output → " ^ alpha))
    | (Reject | AbortReject), None ->
        ("", "¬ (∃ output : p4programIR, Program_ok " ^ name ^ "_input output)")
    | Accept, None -> invalid_arg "accepted case has no expected output"
    | (Reject | AbortReject), Some _ ->
        invalid_arg "rejected case has an expected output"
  in
  let note = match case.expectation with
    | AbortReject -> " (interpreter abort; rejection to prove)"
    | Accept | Reject -> "" in
  "-- " ^ name ^ ": " ^ Printf.sprintf "%S" case.source ^ note ^ "\n"
  ^ "def " ^ name ^ "_input : p4program := " ^ input ^ "\n"
  ^ expected_definition
  ^ "def " ^ name ^ " : Prop := " ^ proposition

let render ?(start = 0) (spec : S.spec) (cases : case list) : string =
  let env = Translator.build_env spec in
  "namespace SpecTec\n\n"
  ^ String.concat "\n\n" (List.mapi (fun index case -> render_case env (start + index) case) cases)
  ^ "\n\nend SpecTec"
