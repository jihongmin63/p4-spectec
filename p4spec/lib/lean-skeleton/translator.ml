module S = Ast.SpecTec
module L = Ast.Lean
module Mixfix = Domain.Mixfix
open Util.Source

exception Unsupported_il of Diagnostic.t

type branch_argument = Expression of S.exp | Function of S.id * L.type_ref

type branch = {
  name : string;
  arguments : branch_argument list;
  premises : S.prem list;
  at : region;
}

let unsupported (at : region) (construct : string) : 'a =
  raise
    (Unsupported_il
       (Diagnostic.error ~source:"lean" at
          ("Lean skeleton does not support " ^ construct)))

let rec translate_type_with_parameters (type_parameters : string list)
    (typ : S.typ) : L.type_ref =
  match typ.it with
  | BoolT -> L.BuiltinType ("Bool", [])
  | NumT `NatT -> L.BuiltinType ("Nat", [])
  | NumT `IntT -> L.BuiltinType ("Int", [])
  | TextT -> L.BuiltinType ("String", [])
  | VarT (id, []) when List.mem id.it type_parameters -> L.TypeParameter id.it
  | VarT (id, []) -> L.Name id.it
  | VarT (id, arguments) ->
      L.Applied
        ( id.it,
          List.map
            (fun (argument : S.targ) ->
              translate_type_with_parameters type_parameters
                (argument.it $ argument.at))
            arguments )
  | IterT (element, Opt) ->
      L.BuiltinType
        ("Option", [ translate_type_with_parameters type_parameters element ])
  | IterT (element, List) ->
      L.BuiltinType
        ("List", [ translate_type_with_parameters type_parameters element ])
  | TupleT [ left; right ] ->
      L.Pair
        ( translate_type_with_parameters type_parameters left,
          translate_type_with_parameters type_parameters right )
  | _ -> unsupported typ.at ("type " ^ S.Print.string_of_typ typ)

let translate_type (typ : S.typ) : L.type_ref =
  translate_type_with_parameters [] typ

let rec translate_parameter_with_parameters (type_parameters : string list)
    (parameter : S.param) : L.type_ref =
  match parameter.it with
  | ExpP typ -> translate_type_with_parameters type_parameters typ
  | DefP (id, tparams, parameters, result) ->
      if tparams <> [] then
        unsupported parameter.at ("type parameters of function parameter " ^ id.it);
      L.RelationType
        ( List.map (translate_parameter_with_parameters type_parameters) parameters,
          translate_type_with_parameters type_parameters result )

module StringMap = Map.Make (String)

type variant = {
  type_parameters : string list;
  cases : (Mixfix.mixop * string) list;
}

type alias = { type_parameters : string list; body : S.typ }

type structure_field = { atom : S.atom; name : string; typ : S.typ }

type function_kind = RelationFunction | BuiltinFunction of string list | UnsupportedFunction of string

type env = {
  iteration_prefix : string;
  functions : function_kind StringMap.t;
  constructors : variant StringMap.t;
  aliases : alias StringMap.t;
  structures : structure_field list StringMap.t;
}

let structure_fields (fields : S.typfield list) : structure_field list =
  List.map
    (fun ((atom, typ) : S.typfield) ->
      let name : string =
        match atom.it with
        | Domain.Atom.Keyword name -> name
        | Domain.Atom.Tag name -> "_" ^ name
        | value -> Domain.Atom.string_of_atom value
      in
      { atom; name; typ })
    fields

let prefix_name (notation : 'a Mixfix.t) : string option =
  let atom : S.atom option =
    match notation with
    | Mixfix.Atom atom -> Some atom
    | Mixfix.Seq (Mixfix.Atom atom :: arguments)
      when List.for_all (function Mixfix.Arg _ -> true | _ -> false) arguments ->
        Some atom
    | _ -> None
  in
  match atom with
  | Some { it = Domain.Atom.Keyword name; _ } -> Some name
  | Some { it = Domain.Atom.Tag name; _ } -> Some ("_" ^ name)
  | _ -> None

let rec mixop_parts (notation : 'a Mixfix.t) : string list =
  match notation with
  | Mixfix.Arg _ -> [ "%" ]
  | Mixfix.Atom atom -> [ Domain.Atom.string_of_atom atom.it ]
  | Mixfix.Brack (left, inner, right) ->
      mixop_parts (Mixfix.Atom left) @ mixop_parts inner
      @ mixop_parts (Mixfix.Atom right)
  | Mixfix.Infix (left, atom, right) ->
      mixop_parts left @ mixop_parts (Mixfix.Atom atom) @ mixop_parts right
  | Mixfix.Seq parts -> List.concat_map mixop_parts parts

let names_of_cases (cases : S.typcase list) : (Mixfix.mixop * string) list =
  let prefix_names : string list =
    List.filter_map (fun (notation, _, _) -> prefix_name notation.it) cases
  in
  List.map
    (fun (notation, _, _) ->
      let name : string =
        match prefix_name notation.it with
        | Some name
          when List.length (List.filter (String.equal name) prefix_names) = 1 ->
            name
        | _ -> String.concat " " (mixop_parts notation.it)
      in
      (Mixfix.to_mixop notation.it, name))
    cases

let build_env (program : S.spec) : env =
  List.fold_left
    (fun (env : env) (declaration : S.def) ->
      match declaration.it with
      | TypD (id, tparams, { it = VariantT cases; _ }, _) ->
          {
            env with
            constructors =
              StringMap.add id.it
                {
                  type_parameters =
                    List.map (fun (param : S.tparam) -> param.it) tparams;
                  cases = names_of_cases cases;
                }
                env.constructors;
          }
      | TypD (id, tparams, { it = PlainT typ; _ }, _) ->
          {
            env with
            aliases =
              StringMap.add id.it
                {
                  type_parameters =
                    List.map (fun (param : S.tparam) -> param.it) tparams;
                  body = typ;
                }
                env.aliases;
          }
      | TypD (id, _, { it = StructT fields; _ }, _) ->
          {
            env with
            structures =
              StringMap.add id.it (structure_fields fields) env.structures;
          }
      | FuncDecD (id, _, _, _, _, _, _) ->
          { env with functions = StringMap.add id.it RelationFunction env.functions }
      | BuiltinDecD (id, parameters, _, _, _) ->
          { env with functions = StringMap.add id.it
              (BuiltinFunction (List.map (fun (parameter : S.tparam) -> parameter.it) parameters)) env.functions }
      | ExternDecD (id, _, _, _, _) ->
          { env with functions = StringMap.add id.it (UnsupportedFunction "external function") env.functions }
      | TableDecD (id, _, _, _, _) ->
          { env with functions = StringMap.add id.it (UnsupportedFunction "table") env.functions }
      | _ -> env)
    {
      iteration_prefix = "";
      functions = StringMap.empty;
      constructors = StringMap.empty;
      aliases = StringMap.empty;
      structures = StringMap.empty;
    }
    program

let rec substitute_type_parameters (bindings : (string * L.type_ref) list)
    (typ : L.type_ref) : L.type_ref =
  match typ with
  | TypeParameter name -> (
      match List.assoc_opt name bindings with
      | Some binding -> binding
      | None -> typ)
  | Name _ -> typ
  | Applied (name, arguments) ->
      L.Applied (name, List.map (substitute_type_parameters bindings) arguments)
  | BuiltinType (name, arguments) ->
      L.BuiltinType (name, List.map (substitute_type_parameters bindings) arguments)
  | Pair (left, right) ->
      L.Pair
        ( substitute_type_parameters bindings left,
          substitute_type_parameters bindings right )
  | RelationType (arguments, result) ->
      L.RelationType
        ( List.map (substitute_type_parameters bindings) arguments,
          substitute_type_parameters bindings result )

let rec expand_type_aliases (lookup : string -> L.type_alias option)
    (at : region) (visited : string list) (typ : L.type_ref) : L.type_ref =
  let expand (name : string) (arguments : L.type_ref list) : L.type_ref =
    match lookup name with
    | Some alias ->
        if List.mem name visited then
          unsupported at ("cyclic type alias " ^ name);
        if List.length alias.type_parameters <> List.length arguments then
          unsupported at
            (Printf.sprintf "type alias arity in %s: expected %d, got %d"
               name (List.length alias.type_parameters) (List.length arguments));
        let bindings : (string * L.type_ref) list =
          List.combine alias.type_parameters arguments
        in
        substitute_type_parameters bindings alias.body
        |> expand_type_aliases lookup at (name :: visited)
    | None ->
        (match typ with
        | Name _ -> L.Name name
        | _ -> L.Applied (name, arguments))
  in
  match typ with
  | Name name -> expand name []
  | Applied (name, arguments) ->
      expand name (List.map (expand_type_aliases lookup at visited) arguments)
  | BuiltinType (name, arguments) ->
      L.BuiltinType
        (name, List.map (expand_type_aliases lookup at visited) arguments)
  | Pair (left, right) ->
      L.Pair
        ( expand_type_aliases lookup at visited left,
          expand_type_aliases lookup at visited right )
  | RelationType (arguments, result) ->
      L.RelationType
        ( List.map (expand_type_aliases lookup at visited) arguments,
          expand_type_aliases lookup at visited result )
  | TypeParameter _ -> typ

(* Lean rejects nested inductive occurrences under generic abbreviations. *)
let expand_generic_aliases (env : env) (at : region) (visited : string list)
    (typ : L.type_ref) : L.type_ref =
  let lookup (name : string) : L.type_alias option =
    match StringMap.find_opt name env.aliases with
    | Some alias when alias.type_parameters <> [] ->
        Some
          { L.name; type_parameters = alias.type_parameters;
            body = translate_type_with_parameters alias.type_parameters alias.body }
    | _ -> None
  in
  expand_type_aliases lookup at visited typ

let constructor_reference (env : env) (at : region) (type_name : string)
    (type_arguments : L.type_ref list) (notation : 'a Mixfix.t) :
    L.constructor_ref =
  let check_arity (name : string) (parameters : string list)
      (arguments : L.type_ref list) : unit =
    if List.length parameters <> List.length arguments then
      unsupported at
        (Printf.sprintf "constructor type arity in %s: expected %d, got %d"
           name (List.length parameters) (List.length arguments))
  in
  let rec resolve (visited : string list) (name : string)
      (arguments : L.type_ref list) : L.constructor_ref =
    if List.mem name visited then
      unsupported at ("cyclic constructor type alias " ^ name);
    match StringMap.find_opt name env.constructors with
    | Some variant -> (
        check_arity name variant.type_parameters arguments;
        match
          List.find_opt
            (fun (mixop, _) -> Mixfix.eq_mixop mixop notation)
            variant.cases
        with
        | Some (_, constructor_name) ->
            if Identifier.contains_closing_quote constructor_name then
              unsupported at
                ("constructor name containing closing quote »: " ^ constructor_name);
            { L.type_name = name; constructor_name; type_arguments = arguments }
        | None ->
            unsupported at
              ("constructor lookup in " ^ name ^ ": "
              ^ String.concat " " (mixop_parts notation)))
    | None -> (
        match StringMap.find_opt name env.aliases with
        | Some alias -> (
            check_arity name alias.type_parameters arguments;
            let bindings : (string * L.type_ref) list =
              List.combine alias.type_parameters arguments
            in
            let body : L.type_ref =
              substitute_type_parameters bindings
                (translate_type_with_parameters alias.type_parameters alias.body)
            in
            match body with
            | Name target -> resolve (name :: visited) target []
            | Applied (target, arguments) ->
                resolve (name :: visited) target arguments
            | _ -> unsupported at ("constructor type alias " ^ name))
        | None ->
            unsupported at
              ("constructor lookup in " ^ name ^ ": "
              ^ String.concat " " (mixop_parts notation)))
  in
  resolve [] type_name type_arguments

let translate_constructor (env : env) (type_name : string)
    (type_parameters : string list) (ctor : S.typcase) : L.constructor =
  let nottyp, _, _ = ctor in
  let type_arguments : L.type_ref list =
    List.map (fun name -> L.TypeParameter name) type_parameters
  in
  let reference : L.constructor_ref =
    constructor_reference env nottyp.at type_name type_arguments nottyp.it
  in
  {
    name = reference.constructor_name;
    arguments =
      List.map
        (fun (argument : S.typ) ->
          translate_type_with_parameters type_parameters argument
          |> expand_generic_aliases env argument.at [])
        (Mixfix.args nottyp.it);
    result =
      (match type_arguments with
      | [] -> L.Name type_name
      | _ -> L.Applied (type_name, type_arguments));
  }

let rec translate_notation (notation : S.nottyp') : L.notation_part list =
  match notation with
  | Mixfix.Arg _ -> [ L.Hole ]
  | Mixfix.Atom atom -> (
      match atom.it with
      | Domain.Atom.Tag _ -> []
      | value -> [ L.Literal (Domain.Atom.render_atom value) ])
  | Mixfix.Brack (left, inner, right) ->
      translate_notation (Mixfix.Atom left)
      @ translate_notation inner
      @ translate_notation (Mixfix.Atom right)
  | Mixfix.Infix (left, atom, right) ->
      translate_notation left
      @ translate_notation (Mixfix.Atom atom)
      @ translate_notation right
  | Mixfix.Seq parts -> List.concat_map translate_notation parts

