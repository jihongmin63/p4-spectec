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

let rec nest_pairs (make : 'a -> 'a -> 'a) (values : 'a list) : 'a =
  match values with
  | [last] -> last
  | first :: rest -> make first (nest_pairs make rest)
  | [] -> invalid_arg "cannot nest an empty tuple"

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
  | TupleT (_ :: _ :: _ as elements) ->
      L.TupleType
        (List.map (translate_type_with_parameters type_parameters) elements)
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
module StringSet = Set.Make (String)

type variant = {
  type_parameters : string list;
  cases : (Mixfix.mixop * string * S.typ list) list;
}

type alias = { type_parameters : string list; body : S.typ }

type structure_field = { atom : S.atom; name : string; typ : S.typ }

type function_kind = RelationFunction | BuiltinFunction of string list
  | BuiltinRelation of string list

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
                  cases = List.map2
                    (fun (mixop, name) (notation, _, _) ->
                      (mixop, name, Mixfix.args notation.it))
                    (names_of_cases cases) cases;
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
          let names : string list =
            List.map (fun (parameter : S.tparam) -> parameter.it) parameters in
          { env with functions = StringMap.add id.it
              (if Builtin_relation.is_relation id.it then BuiltinRelation names
               else BuiltinFunction names) env.functions }
      | ExternDecD (id, _, _, _, _) ->
          { env with functions = StringMap.add id.it RelationFunction env.functions }
      | TableDecD (id, _, _, _, _) ->
          { env with functions = StringMap.add id.it RelationFunction env.functions }
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
  | TupleType elements ->
      L.TupleType (List.map (substitute_type_parameters bindings) elements)
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
  | TupleType elements ->
      L.TupleType (List.map (expand_type_aliases lookup at visited) elements)
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
            (fun (mixop, _, _) -> Mixfix.eq_mixop mixop notation)
            variant.cases
        with
        | Some (_, constructor_name, _) ->
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

let builtin_constructor (env : env) (at : region) (type_name : string)
    (type_arguments : L.type_ref list) (parts : string list) : L.constructor_ref =
  match StringMap.find_opt type_name env.constructors with
  | None -> unsupported at ("builtin constructor lookup in " ^ type_name)
  | Some variant ->
      match List.find_opt
        (fun (mixop, _, _) -> mixop_parts mixop = parts) variant.cases with
      | None -> unsupported at
          ("builtin constructor mixop in " ^ type_name ^ ": " ^ String.concat " " parts)
      | Some (mixop, _, _) ->
          constructor_reference env at type_name type_arguments mixop

let print_atom (atom : S.atom) : string =
  match atom.it with
  | Domain.Atom.Tag _ -> ""
  | value ->
      value |> Domain.Atom.render_atom |> String.lowercase_ascii

let default_print_format (notation : 'a Mixfix.t) : L.print_format =
  let rec translate (cursor : int) (notation : 'a Mixfix.t) :
      int * L.print_format =
    match notation with
    | Mixfix.Arg _ -> cursor + 1, L.PrintHole cursor
    | Mixfix.Atom atom ->
        let rendered : string = print_atom atom in
        ( cursor,
          if rendered = "" then L.PrintAbsent
          else L.PrintLiteral rendered )
    | Mixfix.Brack (left, inner, right) ->
        let cursor, inner = translate cursor inner in
        ( cursor,
          L.PrintFilteredJoin
            [ (let rendered = print_atom left in
                if rendered = "" then L.PrintAbsent
                else L.PrintLiteral rendered);
              inner;
              (let rendered = print_atom right in
                if rendered = "" then L.PrintAbsent
                else L.PrintLiteral rendered) ] )
    | Mixfix.Infix (left, atom, right) ->
        let cursor, left = translate cursor left in
        let cursor, right = translate cursor right in
        let rendered : string = print_atom atom in
        ( cursor,
          L.PrintFilteredJoin
            [ left;
              (if rendered = "" then L.PrintAbsent
               else L.PrintLiteral rendered);
              right ] )
    | Mixfix.Seq parts ->
        let cursor, parts =
          List.fold_left
            (fun (cursor, translated) part ->
              let cursor, part = translate cursor part in
              cursor, translated @ [ part ])
            (cursor, []) parts
        in
        cursor, L.PrintFilteredJoin parts
  in
  snd (translate 0 notation)

let hint_print_format (hint : Lang.Hints.Alter.t) : L.print_format =
  let open Lang.Hints.Alter in
  let rec translate (cursor : int) (hint : Lang.Hints.Alter.t) :
      int * L.print_format =
    match hint with
    | TextH "" -> cursor, L.PrintAbsent
    | TextH text -> cursor, L.PrintLiteral text
    | AtomH atom -> cursor, L.PrintLiteral (print_atom atom)
    | SeqH hints ->
        let cursor, hints =
          List.fold_left
            (fun (cursor, translated) hint ->
              let cursor, hint = translate cursor hint in
              cursor, translated @ [ hint ])
            (cursor, []) hints
        in
        cursor, L.PrintSequence hints
    | BrackH (left, hint, right) ->
        let cursor, hint = translate cursor hint in
        ( cursor,
          L.PrintFilteredJoin
            [ L.PrintLiteral (print_atom left); hint;
              L.PrintLiteral (print_atom right) ] )
    | HoleH { it = `Next; _ } -> cursor + 1, L.PrintHole cursor
    | HoleH { it = `Num index; _ } -> cursor, L.PrintHole index
    | FuseH (left, right) ->
        let cursor, left = translate cursor left in
        let cursor, right = translate cursor right in
        cursor, L.PrintFuse (left, right)
    | OtherH expression ->
        cursor, L.PrintLiteral (Lang.El.Print.string_of_exp expression)
  in
  snd (translate 0 hint)

let constructor_print_format (notation : S.nottyp)
    (hints : S.hint list) : L.print_format =
  match
    List.find_opt
      (fun hint -> Lang.El.(hint.it.hintid.it = "print"))
      hints
  with
  | Some hint ->
      hint_print_format (Lang.Hints.Alter.init Lang.El.(hint.it.hintexp))
  | None -> default_print_format notation.it

let translate_constructor (env : env) (type_name : string)
    (type_parameters : string list) (ctor : S.typcase) : L.constructor =
  let nottyp, typorigin, hints = ctor in
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
    print_origin = (let origin, _ = typorigin.it in origin.it);
    print_format = constructor_print_format nottyp hints;
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

type term_result = {
  term : L.term;
  premises : L.premise list;
  binders : (string * L.type_ref) list;
  next : int;
  helpers : L.declaration list;
}

type terms_result = {
  terms : L.term list;
  premises : L.premise list;
  binders : (string * L.type_ref) list;
  next : int;
  helpers : L.declaration list;
}

let pure_term (next : int) (term : L.term) : term_result =
  { term; premises = []; binders = []; next; helpers = [] }

let collect_terms (translate : int -> 'a -> term_result) (next : int)
    (values : 'a list) : terms_result =
  List.fold_left
    (fun (result : terms_result) value ->
      let translated : term_result = translate result.next value in
      { terms = result.terms @ [ translated.term ];
        premises = result.premises @ translated.premises;
        binders = result.binders @ translated.binders;
        next = translated.next;
        helpers = result.helpers @ translated.helpers })
    { terms = []; premises = []; binders = []; next; helpers = [] } values

let combine_term (result : terms_result) (term : L.term) : term_result =
  { term; premises = result.premises; binders = result.binders; next = result.next; helpers = result.helpers }

let fresh_term (typ : L.type_ref) (next : int) : term_result =
  (* ':' cannot occur in a SpecTec identifier, including function parameters. *)
  let name : string = "eval:" ^ string_of_int next in
  { term = L.Variable (name, typ); premises = [];
    binders = [ name, typ ]; next = next + 1; helpers = [] }

let append_text (left : L.term) (right : L.term) : L.term =
  L.Binary ("++", left, right)

let utf8_byte_size (value : L.term) : L.term =
  L.Native ("String.utf8ByteSize", [ value ])

let text_slice (result : terms_result) (typ : L.type_ref) (base : L.term)
    (index : L.term) (length : L.term) : term_result =
  (* As with byte prefix/suffix builtins, Lean Strings can represent only valid
     UTF-8. A byte range that cuts a code point has no decomposition and hence
     no derivation, while the OCaml interpreter can produce invalid UTF-8. *)
  let value : term_result = fresh_term typ result.next in
  let prefix : term_result = fresh_term typ value.next in
  let suffix : term_result = fresh_term typ prefix.next in
  let whole : L.term =
    append_text (append_text prefix.term value.term) suffix.term
  in
  { value with
    premises =
      result.premises
      @ [ L.Prop (L.Comparison (L.Eq, base, whole));
          L.Prop (L.Comparison (L.Eq, utf8_byte_size prefix.term, index));
          L.Prop (L.Comparison (L.Eq, utf8_byte_size value.term, length)) ];
    binders = result.binders @ value.binders @ prefix.binders @ suffix.binders;
    next = suffix.next;
    helpers = result.helpers }

let expand_expression_type (env : env) (at : region) (typ : L.type_ref) : L.type_ref =
  let lookup (name : string) : L.type_alias option =
    Option.map
      (fun (alias : alias) ->
        { L.name; type_parameters = alias.type_parameters;
          body = translate_type_with_parameters alias.type_parameters alias.body })
      (StringMap.find_opt name env.aliases)
  in
  expand_type_aliases lookup at [] typ

let ordered_comparison_type (typ : L.type_ref) : bool =
  match typ with
  | BuiltinType (("Nat" | "Int"), []) -> true
  | _ -> false

let function_reference (env : env) (functions : (string * L.type_ref) list)
    (id : S.id) : L.term =
  match List.assoc_opt id.it functions with
  | Some typ -> L.Variable ("$" ^ id.it, typ)
  | None -> (
      match StringMap.find_opt id.it env.functions with
      | Some RelationFunction -> L.FunctionReference (L.Global ("$" ^ id.it))
      | _ -> unsupported id.at ("function argument $" ^ id.it))

let rec expression_type (env : env) (type_parameters : string list)
    (value : S.exp) : L.type_ref =
    match value.it with
    (* Elaboration currently annotates -nat as Nat, but Num.un returns Int. *)
    | UnE (`MinusOp, _, _) -> L.BuiltinType ("Int", [])
    | UnE (`PlusOp, _, inner) -> expression_type env type_parameters inner
    | BinE ((`AddOp | `SubOp | `MulOp | `DivOp | `ModOp as operator), _, left, right) ->
        let left_type : L.type_ref = expression_type env type_parameters left in
        let right_type : L.type_ref = expression_type env type_parameters right in
        if left_type <> right_type then
          unsupported value.at
            ("arithmetic with mixed Nat/Int runtime operands: "
            ^ S.Print.string_of_exp value);
        (match left_type with
        | BuiltinType ("Nat", []) when operator = `SubOp ->
            L.BuiltinType ("Int", [])
        | BuiltinType (("Nat" | "Int"), []) -> left_type
        | _ -> unsupported value.at "non-numeric arithmetic operands")
    | _ ->
        translate_type_with_parameters type_parameters (value.note $ value.at)
        |> expand_expression_type env value.at

let rec identity_iteration_variable (exp : S.exp) : (S.id * S.iter list) option =
  match exp.it with
  | VarE id -> Some (id, [])
  | IterE (body, (iter, [ (id, _, iters) ])) -> (
      match identity_iteration_variable body with
      | Some (body_id, body_iters) when body_id.it = id.it && body_iters = iters ->
          Some (id, iters @ [ iter ])
      | _ -> None)
  | _ -> None

let rec variables_in_term (term : L.term) : (string * L.type_ref) list =
  match term with
  | Variable (name, typ) -> [ name, typ ]
  | Lambda (name, _, body) ->
      List.filter (fun (variable, _) -> variable <> name) (variables_in_term body)
  | _ -> List.concat_map variables_in_term (Traversal.term_children term)

let unique_binders (env : env) (at : region) (variables : (string * L.type_ref) list) :
    (string * L.type_ref) list =
  List.fold_left
    (fun binders (name, typ) ->
      match List.assoc_opt name binders with
      | None -> binders @ [ name, typ ]
      | Some previous
        when previous = typ
             || expand_expression_type env at previous
                = expand_expression_type env at typ -> binders
      | Some _ -> unsupported at ("inconsistent type for variable " ^ name))
    [] variables

let variables_in_premises (functions : (string * L.type_ref) list)
    (at : region) (premises : L.premise list) : (string * L.type_ref) list =
  let local_reference (reference : L.reference) : (string * L.type_ref) list =
    match reference with
    | Global _ -> []
    | Local name ->
        (match List.assoc_opt name functions with
        | Some typ -> [ name, typ ]
        | None -> unsupported at ("unbound local relation " ^ name))
  in
  List.concat_map
    (fun (premise : L.premise) ->
      let target : (string * L.type_ref) list = match premise with
        | Holds application | NotHolds (application, _)
        | NotExists (_, application, _) -> local_reference application.target
        | Prop _ -> []
      in
      let bound : string list = match premise with
        | NotExists (binders, _, _) -> List.map fst binders
        | Holds _ | NotHolds _ | Prop _ -> []
      in
      target @ List.filter (fun (name, _) -> not (List.mem name bound))
        (List.concat_map variables_in_term (Traversal.premise_terms premise)))
    premises

let iteration_variables (type_parameters : string list) (iter : S.iter)
    (variables : S.var list) : ((string * L.type_ref) * L.term) list =
  let wrap (typ : L.type_ref) (iter : S.iter) : L.type_ref =
    L.BuiltinType ((match iter with List -> "List" | Opt -> "Option"), [ typ ])
  in
  List.map
    (fun ((id, typ, iters) : S.var) ->
      let element_type : L.type_ref =
        List.fold_left wrap (translate_type_with_parameters type_parameters typ) iters
      in
      ( (Identifier.name_of_var id iters, element_type),
        L.Variable (Identifier.name_of_var id (iters @ [ iter ]), wrap element_type iter) ))
    variables

(* One constructor advances every collection together; unequal lengths and
   mixed none/some inputs have no derivation. Evaluation binders stay local. *)
let translate_iteration (env : env) (type_parameters : string list)
    (functions : (string * L.type_ref) list) (at : region) (index : int)
    (iter : S.iter) (variables : S.var list) (body : terms_result)
    (outputs : (L.term * L.term * L.type_ref) list) : terms_result =
  let name : string = env.iteration_prefix ^ ":iter:" ^ string_of_int index in
  let inputs : ((string * L.type_ref) * L.term) list =
    iteration_variables type_parameters iter variables
  in
  let elements : (string * L.type_ref) list = List.map fst inputs in
  let vectors : (L.term * L.term * L.type_ref) list =
    List.map (fun ((name, typ), collection) -> L.Variable (name, typ), collection, typ) inputs
    @ outputs
  in
  let local_names : string list = List.map fst (elements @ body.binders) in
  let body_variables : (string * L.type_ref) list =
    unique_binders env at
      (List.concat_map variables_in_term body.terms
       @ variables_in_premises
           (List.map (fun (name, typ) -> "$" ^ name, typ) functions) at body.premises)
  in
  let context : (string * L.type_ref) list =
    List.filter (fun (name, _) -> not (List.mem name local_names)) body_variables
  in
  let context_terms : L.term list = List.map (fun (name, typ) -> L.Variable (name, typ)) context in
  let collection_type (typ : L.type_ref) : L.type_ref =
    L.BuiltinType ((match iter with List -> "List" | Opt -> "Option"), [ typ ])
  in
  let application (collections : L.term list) : L.application =
    { target = L.Global name;
      type_arguments = List.map (fun name -> L.TypeParameter name) type_parameters;
      instance_arguments = [];
      print_instance_arguments = [];
      arguments = context_terms @ collections }
  in
  let empty : L.term list = List.map
    (fun (_, _, typ) -> L.Typed
      ((match iter with List -> L.ListLiteral [] | Opt -> L.Native ("Option.none", [])), collection_type typ)) vectors
  in
  let tails : (string * L.type_ref) list = List.mapi
    (fun index (_, _, typ) -> "tail:" ^ string_of_int index, collection_type typ) vectors
  in
  let tail_terms : L.term list = List.map (fun (name, typ) -> L.Variable (name, typ)) tails in
  let populated : L.term list = List.map2
    (fun (element, _, _) tail -> match iter with
      | List -> L.Binary ("::", element, tail)
      | Opt -> L.Native ("Option.some", [ element ])) vectors tail_terms
  in
  let step_binders : (string * L.type_ref) list =
    unique_binders env at
      (context @ elements @ body.binders @ body_variables
       @ (match iter with List -> tails | Opt -> []))
  in
  let rules : L.rule list = [
    { name = (match iter with List -> "nil" | Opt -> "none"); binders = context;
      premises = []; catchable = []; conclusion = application empty };
    { name = (match iter with List -> "cons" | Opt -> "some"); binders = step_binders;
      premises = body.premises
        @ (match iter with List -> [ L.Holds (application tail_terms) ] | Opt -> []);
      catchable = [];
      conclusion = application populated }
  ] in
  let helper : L.declaration = L.Relation
    { name; type_parameters; equality_parameters = [];
      print_parameters = [];
      argument_types = List.map snd context @ List.map (fun (_, _, typ) -> collection_type typ) vectors;
      input_positions = Some (List.init (List.length context + List.length inputs) Fun.id);
      rules; notation = None }
  in
  { terms = []; premises = [ L.Holds (application (List.map (fun (_, collection, _) -> collection) vectors)) ];
    binders = []; next = body.next; helpers = body.helpers @ [ helper ] }

let variant_instance (env : env) (at : region) (typ : L.type_ref) :
    (string * L.type_ref list * variant) option =
  let named : (string * L.type_ref list) option = match typ with
    | Name name -> Some (name, [])
    | Applied (name, arguments) -> Some (name, arguments)
    | _ -> None
  in
  match named with
  | None -> None
  | Some (name, arguments) ->
      Option.map
        (fun (variant : variant) ->
          if List.length variant.type_parameters <> List.length arguments then
            unsupported at ("variant type arity in " ^ name);
          (name, arguments, variant))
        (StringMap.find_opt name env.constructors)

let variant_cases (env : env) (at : region) (source : L.type_ref)
    (target : L.type_ref) : (string * string * int) list option =
  match variant_instance env at source, variant_instance env at target with
  | Some (_, source_arguments, source_variant), Some (_, target_arguments, target_variant) ->
      let instantiate (variant : variant) (arguments : L.type_ref list)
          (types : S.typ list) : L.type_ref list =
        let bindings : (string * L.type_ref) list =
          List.combine variant.type_parameters arguments
        in
        List.map
          (fun typ ->
            translate_type_with_parameters variant.type_parameters typ
            |> substitute_type_parameters bindings
            |> expand_expression_type env at)
          types
      in
      Some (List.map
        (fun (source_mixop, source_name, source_types) ->
          match List.find_opt
            (fun (target_mixop, _, _) -> Mixfix.eq_mixop source_mixop target_mixop)
            target_variant.cases with
          | None -> unsupported at
              ("UpCastE target variant lacks constructor " ^ source_name)
          | Some (_, target_name, target_types) ->
              if instantiate source_variant source_arguments source_types
                 <> instantiate target_variant target_arguments target_types then
                unsupported at
                  ("UpCastE constructor argument types differ for " ^ source_name);
              (source_name, target_name, List.length source_types))
        source_variant.cases)
  | _ -> None

let rec type_code (typ : L.type_ref) : string =
  match typ with
  | Name name -> "N" ^ name
  | TypeParameter name -> "P" ^ name
  | Applied (name, arguments) ->
      "A" ^ name ^ "(" ^ String.concat "," (List.map type_code arguments) ^ ")"
  | BuiltinType (name, arguments) ->
      "B" ^ name ^ "(" ^ String.concat "," (List.map type_code arguments) ^ ")"
  | TupleType elements ->
      "T(" ^ String.concat "," (List.map type_code elements) ^ ")"
  | RelationType (arguments, result) ->
      "R(" ^ String.concat "," (List.map type_code (result :: arguments)) ^ ")"

let cast_name (source : L.type_ref) (target : L.type_ref) : string =
  match source, target with
  | Name source, Name target -> "cast:" ^ source ^ ":" ^ target
  | _ ->
      "cast:" ^ Digest.to_hex
        (Digest.string (type_code source ^ ":" ^ type_code target))

let membership_name (source : L.type_ref) (target : L.type_ref) : string =
  match source, target with
  | Name source, Name target -> "sub:" ^ source ^ ":" ^ target
  | _ ->
      "sub:" ^ Digest.to_hex
        (Digest.string (type_code source ^ ":" ^ type_code target))

let rec tuple_terms (types : L.type_ref list) (term : L.term) : L.term list =
  match types with
  | [] -> invalid_arg "cannot project an empty tuple"
  | [ _ ] -> [ term ]
  | _ :: rest ->
      let (left, right) : L.term * L.term =
        match term with
        | L.Tuple (left, right) -> left, right
        | _ -> L.Native ("Prod.fst", [ term ]), L.Native ("Prod.snd", [ term ])
      in
      left :: tuple_terms rest right

let rec conjunction (terms : L.term list) : L.term =
  match terms with
  | [] -> L.Boolean true
  | [ term ] -> term
  | term :: rest -> L.Binary ("&&", term, conjunction rest)

let rec check_term (env : env) (type_parameters : string list) (at : region)
    (source : L.type_ref) (target : L.type_ref) (subcheck : S.subcheck)
    (term : L.term) : L.term =
  match subcheck with
  | SkipSC -> L.Boolean true
  | MixopSC mixops ->
      (match variant_instance env at source, variant_instance env at target with
      | Some (_, _, source_variant), Some _ ->
          let cases : (string * int) list =
            List.filter_map
              (fun (mixop, name, arguments) ->
                if List.exists (Mixfix.eq_mixop mixop) mixops then
                  Some (name, List.length arguments)
                else None)
              source_variant.cases
          in
          L.MembershipTest
            (membership_name source target, source, target, cases,
             List.length cases = List.length source_variant.cases, term)
      | _ -> unsupported at
          ("MixopSC requires variant source and target: "
           ^ type_code source ^ " <: " ^ type_code target))
  | TupleSC (_ :: _ :: _ as checks) ->
      (match source, target with
      | TupleType sources, TupleType targets
        when List.length sources = List.length targets
          && List.length sources = List.length checks ->
          let terms : L.term list = tuple_terms sources term in
          List.map2
            (fun (source, target) (check, term) ->
              check_term env type_parameters at source target check term)
            (List.combine sources targets) (List.combine checks terms)
          |> conjunction
      | _ -> unsupported at "TupleSC with non-pair source or target")
  | TupleSC _ -> unsupported at "TupleSC with unsupported tuple arity"
  | IterSC (List, item_check) ->
      (match source, target with
      | BuiltinType ("List", [ source_item ]), BuiltinType ("List", [ target_item ]) ->
          let item : L.term = L.Variable ("sub:item", source_item) in
          L.Native ("List.all", [ term; L.Lambda ("sub:item", source_item,
            check_term env type_parameters at source_item target_item item_check item) ])
      | _ -> unsupported at "IterSC List with non-list source or target")
  | IterSC (Opt, item_check) ->
      (match source, target with
      | BuiltinType ("Option", [ source_item ]), BuiltinType ("Option", [ target_item ]) ->
          let item : L.term = L.Variable ("sub:item", source_item) in
          L.Native ("Option.all", [ L.Lambda ("sub:item", source_item,
            check_term env type_parameters at source_item target_item item_check item); term ])
      | _ -> unsupported at "IterSC Opt with non-option source or target")
  | RecurseSC typ ->
      let checked : L.type_ref =
        translate_type_with_parameters type_parameters typ
        |> expand_expression_type env at
      in
      (match source, checked with
      | BuiltinType ("Int", []), BuiltinType ("Nat", []) ->
          L.Decide ([], L.Comparison (L.Le,
            L.Number ("0", L.BuiltinType ("Int", [])), term))
      | _ -> unsupported at
          ("RecurseSC from " ^ type_code source ^ " to " ^ type_code checked))

let rec cast_term (env : env) (at : region) (source : L.type_ref)
    (target : L.type_ref) (term : L.term) : L.term =
  let source : L.type_ref = expand_expression_type env at source in
  let target : L.type_ref = expand_expression_type env at target in
  if source = target then term
  else match source, target with
  | BuiltinType ("Nat", []), BuiltinType ("Int", []) ->
      L.Native ("Int.ofNat", [ term ])
  | TupleType sources, TupleType targets
    when List.length sources = List.length targets ->
      List.map2
        (fun (source, term) target -> cast_term env at source target term)
        (List.combine sources (tuple_terms sources term)) targets
      |> nest_pairs (fun left right -> L.Tuple (left, right))
  | BuiltinType ("List", [ source_element ]),
    BuiltinType ("List", [ target_element ]) ->
      (match term with
      | Typed (ListLiteral elements, _) | ListLiteral elements ->
          L.Typed (L.ListLiteral
            (List.map (cast_term env at source_element target_element) elements), target)
      | _ ->
          let item : L.term = L.Variable ("cast:item", source_element) in
          L.Native ("List.map", [ L.Lambda ("cast:item", source_element,
            cast_term env at source_element target_element item); term ]))
  | BuiltinType ("Option", [ source_element ]),
    BuiltinType ("Option", [ target_element ]) ->
      (match term with
      | Native ("Option.some", [ element ]) ->
          L.Native ("Option.some", [ cast_term env at source_element target_element element ])
      | Typed (Native ("Option.none", []), _) ->
          L.Typed (L.Native ("Option.none", []), target)
      | _ ->
          let item : L.term = L.Variable ("cast:item", source_element) in
          L.Native ("Option.map", [ L.Lambda ("cast:item", source_element,
            cast_term env at source_element target_element item); term ]))
  | BuiltinType ("Option", [ source_element ]),
    BuiltinType ("List", [ target_element ]) ->
      let item : L.term = L.Variable ("cast:item", source_element) in
      let mapped : L.term =
        if source_element = target_element then term
        else L.Native ("Option.map", [ L.Lambda ("cast:item", source_element,
          cast_term env at source_element target_element item); term ])
      in
      L.Native ("Option.toList", [ mapped ])
  | _, BuiltinType ("Option", [ target_element ]) ->
      L.Native ("Option.some", [ cast_term env at source target_element term ])
  | _, BuiltinType ("List", [ target_element ]) ->
      L.Typed (L.ListLiteral [ cast_term env at source target_element term ], target)
  | _ ->
      (match variant_cases env at source target with
      | Some cases ->
          (match term with
          | Constructor (reference, arguments) ->
              (match List.find_opt
                (fun (source_name, _, _) -> source_name = reference.constructor_name)
                cases with
              | Some (_, target_name, _) ->
                  let (target_type, target_arguments) : string * L.type_ref list =
                    match target with
                    | Name name -> name, []
                    | Applied (name, arguments) -> name, arguments
                    | _ -> assert false
                  in
                  L.Constructor
                    ({ L.type_name = target_type; constructor_name = target_name;
                       type_arguments = target_arguments }, arguments)
              | None -> unsupported at
                  ("UpCastE source constructor " ^ reference.constructor_name))
          | _ -> L.Coerce (cast_name source target, source, target, term))
      | None -> unsupported at
          ("UpCastE from " ^ type_code source ^ " to " ^ type_code target))

let rec translate_term (env : env) (type_parameters : string list)
    (functions : (string * L.type_ref) list) (next : int) (exp : S.exp) : term_result =
  let typ : L.type_ref = translate_type_with_parameters type_parameters (exp.note $ exp.at) in
  let expanded (value : S.exp) : L.type_ref =
    translate_type_with_parameters type_parameters (value.note $ value.at)
    |> expand_expression_type env value.at
  in
  let recurse : int -> S.exp -> term_result = translate_term env type_parameters functions in
  let build (values : S.exp list) (make : L.term list -> L.term) : term_result =
    let result : terms_result = collect_terms recurse next values in
    combine_term result (make result.terms)
  in
  let unary (value : S.exp) (make : L.term -> L.term) : term_result =
    let result : term_result = recurse next value in
    { result with term = make result.term }
  in
  let binary (left : S.exp) (right : S.exp)
      (make : L.term -> L.term -> L.term) : term_result =
    build [ left; right ] (function
      | [ left; right ] -> make left right
      | _ -> assert false)
  in
  let numeric_type : S.exp -> L.type_ref = expression_type env type_parameters in
  let integer (value : S.exp) (term : L.term) : L.term =
    match numeric_type value with
    | BuiltinType ("Nat", []) -> L.Native ("Int.ofNat", [ term ])
    | BuiltinType ("Int", []) -> term
    | _ -> unsupported value.at "non-numeric integer operand"
  in
  match exp.it with
  | VarE id -> pure_term next (L.Variable (Identifier.name_of_var id [], typ))
  | BoolE value -> pure_term next (L.Boolean value)
  | NumE value ->
      let number : string = Lang.Xl.Num.string_of_num value in
      let number : string =
        if String.starts_with ~prefix:"+" number then
          String.sub number 1 (String.length number - 1)
        else number
      in
      pure_term next (L.Number (number, typ))
  | TextE value -> pure_term next (L.Text value)
  | CaseE notation -> (
      match exp.note with
      | VarT (id, arguments) ->
          let reference : L.constructor_ref =
            constructor_reference env exp.at id.it
              (List.map (translate_type_with_parameters type_parameters) arguments) notation
          in
          build (Mixfix.args notation) (fun arguments -> L.Constructor (reference, arguments))
      | _ -> unsupported exp.at ("constructor " ^ S.Print.string_of_exp exp))
  | CallE (id, type_arguments, arguments) ->
      let target : L.reference =
        if List.mem_assoc id.it functions then L.Local ("$" ^ id.it)
        else L.Global ("$" ^ id.it)
      in
      let direct : bool =
        if List.mem_assoc id.it functions then false
        else match StringMap.find_opt id.it env.functions with
        | Some RelationFunction -> false
        | Some (BuiltinRelation parameters) -> (
            match Builtin_relation.signature id.it parameters with
            | Ok _ -> false
            | Error reason -> unsupported exp.at ("builtin call " ^ reason))
        | Some (BuiltinFunction parameters) -> (
            match Builtin.translate id.it parameters with
            | Ok _ ->
                if Builtin.is_text_set_operation id.it then (
                  match type_arguments with
                  | [ key ] ->
                      let expanded_key : L.type_ref =
                        translate_type_with_parameters type_parameters key
                        |> expand_expression_type env exp.at
                      in
                      if expanded_key <> L.BuiltinType ("String", []) then
                        unsupported exp.at
                          ("builtin call $" ^ id.it ^ " with K = "
                         ^ S.Print.string_of_typ key
                         ^ " because Lean translates this builtin only for \
                            text keys")
                  | _ ->
                      unsupported exp.at
                        ("builtin call $" ^ id.it
                       ^ " because its number of type arguments is unexpected"));
                true
            | Error reason -> unsupported exp.at ("builtin call " ^ reason))
        | None -> unsupported exp.at ("unknown function call $" ^ id.it)
      in
      let translate_argument (next : int) (argument : S.arg) : term_result =
        match argument.it with
        | ExpA value -> recurse next value
        | DefA id -> pure_term next (function_reference env functions id)
      in
      let result : terms_result = collect_terms translate_argument next arguments in
      let application : L.application =
        { target;
          type_arguments =
            (if Builtin.is_text_set_operation id.it && direct then []
             else
               List.map
                 (translate_type_with_parameters type_parameters)
                 type_arguments);
          instance_arguments = [];
          print_instance_arguments = [];
          arguments = result.terms }
      in
      if direct then combine_term result (L.Apply application)
      else
        let fresh : term_result = fresh_term typ result.next in
        { fresh with premises = result.premises @ [ L.Holds { application with arguments = application.arguments @ [ fresh.term ] } ];
          binders = result.binders @ fresh.binders; helpers = result.helpers }
  | UnE (`NotOp, _, value) -> unary value (fun term -> L.Unary ("!", term))
  | UnE (`MinusOp, _, value) ->
      unary value (fun term -> L.Unary ("-", integer value term))
  | UnE (`PlusOp, _, value) -> recurse next value
  | BinE (`PowOp, _, _, _) -> unsupported exp.at "power expression"
  | BinE ((`AndOp | `OrOp | `ImplOp | `EquivOp as operator), _, left, right) ->
      binary left right (fun left right -> match operator with
        | `AndOp -> L.Binary ("&&", left, right)
        | `OrOp -> L.Binary ("||", left, right)
        | `ImplOp -> L.Binary ("||", L.Unary ("!", left), right)
        | `EquivOp -> L.Binary ("==", left, right))
  | BinE ((`AddOp | `SubOp | `MulOp | `DivOp | `ModOp as operator), _, left, right) ->
      let result_type : L.type_ref = numeric_type exp in
      let result : terms_result = collect_terms recurse next [ left; right ] in
      let (left_term, right_term) : L.term * L.term =
        match result.terms with
        | [ a; b ] when result_type = L.BuiltinType ("Int", []) -> integer left a, integer right b
        | [ a; b ] when result_type = L.BuiltinType ("Nat", []) && operator <> `SubOp -> a, b
        | _ -> unsupported exp.at "numeric operation result type"
      in
      let term : L.term = match operator with
        | `AddOp -> L.Binary ("+", left_term, right_term)
        | `SubOp -> L.Binary ("-", left_term, right_term)
        | `MulOp -> L.Binary ("*", left_term, right_term)
        | `DivOp when result_type = L.BuiltinType ("Int", []) -> L.Native ("Int.tdiv", [ left_term; right_term ])
        | `ModOp when result_type = L.BuiltinType ("Int", []) -> L.Native ("Int.tmod", [ left_term; right_term ])
        | `DivOp -> L.Binary ("/", left_term, right_term)
        | `ModOp -> L.Binary ("%", left_term, right_term)
      in
      let translated : term_result = combine_term result term in
      if operator = `DivOp || operator = `ModOp then
        { translated with premises = translated.premises @ [ L.Prop (L.Comparison (L.Ne, right_term, L.Number ("0", result_type))) ] }
      else translated
  | UpCastE (_, value) ->
      (* The source is the runtime type: -n and nat - nat are annotated Nat but
         already translate to Int terms. *)
      unary value (cast_term env exp.at (numeric_type value) (expanded exp))
  | TupleE (_ :: _ :: _ as elements) ->
      build elements (nest_pairs (fun left right -> L.Tuple (left, right)))
  | OptE None -> pure_term next (L.Typed (L.Native ("Option.none", []), typ))
  | OptE (Some value) -> unary value (fun term -> L.Native ("Option.some", [ term ]))
  | ListE values -> build values (fun terms -> L.Typed (L.ListLiteral terms, typ))
  | ConsE (left, right) -> binary left right (fun left right -> L.Binary ("::", left, right))
  | CatE (left, right) -> (
      match expanded exp with
      | BuiltinType ("List", [ _ ]) | BuiltinType ("String", []) ->
          binary left right (fun left right -> L.Binary ("++", left, right))
      | _ -> unsupported exp.at "concatenation operand type")
  | LenE value -> (
      match expanded value with
      | BuiltinType ("List", [ _ ]) -> unary value (fun term -> L.Native ("List.length", [ term ]))
      | BuiltinType ("String", []) -> unary value (fun term -> L.Native ("String.utf8ByteSize", [ term ]))
      | _ -> unsupported exp.at "length operand type")
  | IdxE (base, index) -> (
      match expanded base, numeric_type index with
      | BuiltinType ("List", [ _ ]), BuiltinType ("Nat", []) ->
          let result : terms_result = collect_terms recurse next [ base; index ] in
          let fresh : term_result = fresh_term typ result.next in
          let prop : L.prop = match result.terms with
            | [ base; index ] -> L.Comparison (L.Eq, L.Index (base, index), L.Native ("Option.some", [ fresh.term ]))
            | _ -> assert false
          in
          { fresh with premises = result.premises @ [ L.Prop prop ]; binders = result.binders @ fresh.binders; helpers = result.helpers }
      | BuiltinType ("String", []), BuiltinType ("Nat", []) ->
          let result : terms_result = collect_terms recurse next [ base; index ] in
          (match result.terms with
          | [ base; index ] ->
              text_slice result typ base index
                (L.Number ("1", L.BuiltinType ("Nat", [])))
          | _ -> assert false)
      | _ ->
          unsupported exp.at
            "indexing other than a list or text with a natural index")
  | DotE (base, atom) ->
      let (name, field) : string * structure_field = structure_field env base.at (expanded base) atom in
      unary base (fun term -> L.Projection (name, field.name, term))
  | StrE fields ->
      let fields : (string * S.exp) list = List.map
        (fun (atom, value) ->
          let (_, field) : string * structure_field = structure_field env exp.at (expanded exp) atom in
          field.name, value) fields
      in
      build (List.map snd fields) (fun values -> L.StructureLiteral (typ, List.combine (List.map fst fields) values))
  | CmpE (operator, _, left, right) ->
      let left_type : L.type_ref = numeric_type left in
      let right_type : L.type_ref = numeric_type right in
      if left_type <> right_type then
        unsupported exp.at "comparison operands with different runtime types";
      let operator : L.comparison = match operator with
        | `EqOp -> L.Eq | `NeOp -> L.Ne | `LtOp -> L.Lt | `LeOp -> L.Le | `GtOp -> L.Gt | `GeOp -> L.Ge
      in
      let empty_test (value : S.exp) : string option =
        match value.it, numeric_type value with
        | ListE [], BuiltinType ("List", [ _ ]) -> Some "List.isEmpty"
        | OptE None, BuiltinType ("Option", [ _ ]) -> Some "Option.isNone"
        | _ -> None
      in
      (match operator, empty_test left, empty_test right with
      | (L.Eq | L.Ne), Some test, _ ->
          unary right (fun term ->
            let result : L.term = L.Native (test, [ term ]) in
            if operator = L.Ne then L.Unary ("!", result) else result)
      | (L.Eq | L.Ne), None, Some test ->
          unary left (fun term ->
            let result : L.term = L.Native (test, [ term ]) in
            if operator = L.Ne then L.Unary ("!", result) else result)
      | (L.Eq | L.Ne), None, None ->
          binary left right (fun left right ->
            L.Decide ([ left_type ], L.Comparison (operator, left, right)))
      | _ ->
          if not (ordered_comparison_type left_type) then
            unsupported exp.at "ordered comparison of non-numeric operands";
          binary left right (fun left right ->
            L.Decide ([], L.Comparison (operator, left, right))))
  | MemE (element, collection) ->
      let element_type : L.type_ref = numeric_type element in
      (match expanded collection with
      | BuiltinType ("List", [ typ ]) when typ = element_type -> ()
      | _ -> unsupported exp.at "membership in a non-list");
      binary element collection (fun element collection ->
        L.Decide ([ element_type ], L.Membership (element, collection)))
  | IterE (body, (iter, variables)) -> (
      match identity_iteration_variable exp with
      | Some (id, iters) ->
          pure_term next (L.Variable (Identifier.name_of_var id iters, typ))
      | None ->
          let element_type : L.type_ref = match iter, expand_expression_type env exp.at typ with
            | List, BuiltinType ("List", [ element ])
            | Opt, BuiltinType ("Option", [ element ]) -> element
            | _ -> unsupported exp.at "iteration result collection type"
          in
          if expression_type env type_parameters body
             <> expand_expression_type env body.at element_type then
            unsupported body.at "iteration body with a different runtime element type";
          let body : term_result = recurse (next + 1) body in
          let result : term_result = fresh_term typ body.next in
          let evaluation : terms_result =
            { terms = [ body.term ]; premises = body.premises; binders = body.binders;
              next = result.next; helpers = body.helpers }
          in
          let iteration : terms_result = translate_iteration env type_parameters functions exp.at
            next iter variables evaluation [ body.term, result.term, element_type ]
          in
          { result with premises = iteration.premises; helpers = iteration.helpers })
  | SubE (value, target, subcheck) ->
      let result : term_result = recurse next value in
      let source : L.type_ref = expanded value in
      let target : L.type_ref =
        translate_type_with_parameters type_parameters target
        |> expand_expression_type env exp.at
      in
      { result with term = check_term env type_parameters exp.at source target subcheck result.term }
  | SliceE (base, index, length) -> (
      match expanded base, numeric_type index, numeric_type length with
      | BuiltinType ("List", [ _ ]), BuiltinType ("Nat", []),
        BuiltinType ("Nat", []) ->
          let result : terms_result =
            collect_terms recurse next [ base; index; length ]
          in
          (match result.terms with
          | [ base; index; length ] ->
              let term : L.term =
                L.Native ("List.take",
                  [ length; L.Native ("List.drop", [ index; base ]) ])
              in
              let bound : L.prop =
                L.Comparison
                  (L.Le, L.Binary ("+", index, length),
                   L.Native ("List.length", [ base ]))
              in
              { (combine_term result term) with
                premises = result.premises @ [ L.Prop bound ] }
          | _ -> assert false)
      | BuiltinType ("String", []), BuiltinType ("Nat", []),
        BuiltinType ("Nat", []) ->
          let result : terms_result =
            collect_terms recurse next [ base; index; length ]
          in
          (match result.terms with
          | [ base; index; length ] -> text_slice result typ base index length
          | _ -> assert false)
      | _ ->
          unsupported exp.at
            "slicing other than a list or text with a natural start and length")
  | UpdE (base, path, value) ->
      let evaluated : terms_result = collect_terms recurse next [ base; value ] in
      let (base_term, value_term) : L.term * L.term =
        match evaluated.terms with
        | [ base; value ] -> base, value
        | _ -> assert false
      in
      let expanded_path (path : S.path) : L.type_ref =
        translate_type_with_parameters type_parameters (path.note $ path.at)
        |> expand_expression_type env path.at
      in
      let rec access_path (path : S.path) : L.term =
        match path.it with
        | RootP -> base_term
        | DotP (parent, atom) ->
            let (name, field) : string * structure_field =
              structure_field env parent.at (expanded_path parent) atom
            in
            L.Projection (name, field.name, access_path parent)
        | IdxP _ -> unsupported path.at "UpdE path with a non-final index"
        | SliceP _ -> unsupported path.at "SliceP in UpdE path"
      in
      let rec update_fields (path : S.path) (replacement : L.term) : L.term =
        match path.it with
        | RootP -> replacement
        | DotP (parent, atom) ->
            let (name, field) : string * structure_field =
              structure_field env parent.at (expanded_path parent) atom
            in
            let updated : L.term =
              L.StructureUpdate
                (L.Name name, access_path parent, field.name, replacement)
            in
            update_fields parent updated
        | IdxP _ -> unsupported path.at "UpdE path with a non-final index"
        | SliceP _ -> unsupported path.at "SliceP in UpdE path"
      in
      (match path.it with
      | RootP | DotP _ ->
          combine_term evaluated (update_fields path value_term)
      | SliceP _ -> unsupported path.at "SliceP in UpdE path"
      | IdxP (parent, index) ->
          (match parent.it with
          | RootP -> ()
          | _ -> unsupported parent.at "UpdE path with a non-final index");
          if numeric_type index <> L.BuiltinType ("Nat", []) then
            unsupported index.at "UpdE index other than a natural";
          let index_result : term_result = recurse evaluated.next index in
          let premises : L.premise list =
            evaluated.premises @ index_result.premises
          in
          let binders : (string * L.type_ref) list =
            evaluated.binders @ index_result.binders
          in
          let helpers : L.declaration list =
            evaluated.helpers @ index_result.helpers
          in
          (match expanded_path parent with
          | BuiltinType ("List", [ _ ]) ->
              let bound : L.prop =
                L.Comparison
                  (L.Lt, index_result.term,
                   L.Native ("List.length", [ base_term ]))
              in
              { term =
                  L.Native
                    ("List.set", [ base_term; index_result.term; value_term ]);
                premises = premises @ [ L.Prop bound ]; binders;
                next = index_result.next; helpers }
          | BuiltinType ("String", []) ->
              let prefix : term_result =
                fresh_term (L.BuiltinType ("String", [])) index_result.next
              in
              let old : term_result =
                fresh_term (L.BuiltinType ("String", [])) prefix.next
              in
              let suffix : term_result =
                fresh_term (L.BuiltinType ("String", [])) old.next
              in
              let one : L.term =
                L.Number ("1", L.BuiltinType ("Nat", []))
              in
              { term =
                  append_text (append_text prefix.term value_term) suffix.term;
                premises =
                  premises
                  @ [ L.Prop
                        (L.Comparison
                           (L.Eq, base_term,
                            append_text
                              (append_text prefix.term old.term) suffix.term));
                      L.Prop
                        (L.Comparison
                           (L.Eq, utf8_byte_size prefix.term,
                            index_result.term));
                      L.Prop
                        (L.Comparison
                           (L.Eq, utf8_byte_size old.term, one));
                      L.Prop
                        (L.Comparison
                           (L.Eq, utf8_byte_size value_term, one)) ];
                binders =
                  binders @ prefix.binders @ old.binders @ suffix.binders;
                next = suffix.next; helpers }
          | _ -> unsupported path.at "UpdE index on a non-list or non-text"))
  | MatchE _ -> unsupported exp.at ("MatchE expression " ^ S.Print.string_of_exp exp)
  | DownCastE _ -> unsupported exp.at ("DownCastE expression " ^ S.Print.string_of_exp exp)
  | TupleE _ -> unsupported exp.at ("TupleE expression with unsupported arity: " ^ S.Print.string_of_exp exp)

and structure_field (env : env) (at : region) (typ : L.type_ref) (atom : S.atom) :
    string * structure_field =
  match typ with
  | Name name -> (
      match StringMap.find_opt name env.structures with
      | Some fields -> (
          match List.find_opt (fun (field : structure_field) -> field.atom.it = atom.it) fields with
          | Some field -> name, field
          | None -> unsupported atom.at ("unknown structure field in " ^ name))
      | None -> unsupported at ("field access on non-structure " ^ name))
  | _ -> unsupported at "field access on non-structure type"

let translate_application (env : env) (type_parameters : string list)
    (functions : (string * L.type_ref) list) (next : int) (name : string)
    (type_arguments : L.type_ref list) (arguments : S.exp list) :
    L.application * terms_result =
  let result : terms_result = collect_terms (translate_term env type_parameters functions) next arguments in
  { target = L.Global name; type_arguments; instance_arguments = [];
    print_instance_arguments = [];
    arguments = result.terms }, result

type condition_result = { condition : L.prop; evaluation : terms_result }

let rec translate_condition (env : env) (type_parameters : string list)
    (functions : (string * L.type_ref) list) (next : int) (exp : S.exp) : condition_result =
  let recurse : int -> S.exp -> condition_result = translate_condition env type_parameters functions in
  match exp.it with
  | UnE (`NotOp, _, value) ->
      let result : condition_result = recurse next value in
      { result with condition = L.Not result.condition }
  | BinE ((`AndOp | `OrOp | `ImplOp | `EquivOp as operator), _, left, right) ->
      let left : condition_result = recurse next left in
      let right : condition_result = recurse left.evaluation.next right in
      let condition : L.prop = match operator with
        | `AndOp -> L.And (left.condition, right.condition)
        | `OrOp -> L.Or (left.condition, right.condition)
        | `ImplOp -> L.Implies (left.condition, right.condition)
        | `EquivOp -> L.Iff (left.condition, right.condition)
      in
      { condition; evaluation = {
          terms = []; premises = left.evaluation.premises @ right.evaluation.premises;
          binders = left.evaluation.binders @ right.evaluation.binders;
          next = right.evaluation.next;
          helpers = left.evaluation.helpers @ right.evaluation.helpers } }
  | CmpE (operator, _, left, right) ->
      if expression_type env type_parameters left <> expression_type env type_parameters right then
        unsupported exp.at "comparison operands with different runtime types";
      let evaluation : terms_result = collect_terms (translate_term env type_parameters functions) next [ left; right ] in
      let operator : L.comparison = match operator with
        | `EqOp -> L.Eq | `NeOp -> L.Ne | `LtOp -> L.Lt | `LeOp -> L.Le | `GtOp -> L.Gt | `GeOp -> L.Ge
      in
      let condition : L.prop = match evaluation.terms with
        | [ left; right ] -> L.Comparison (operator, left, right)
        | _ -> assert false
      in
      { condition; evaluation }
  | MemE (element, collection) ->
      (match expression_type env type_parameters collection with
      | BuiltinType ("List", [ typ ]) when typ = expression_type env type_parameters element -> ()
      | _ -> unsupported exp.at "membership in a non-list");
      let evaluation : terms_result = collect_terms (translate_term env type_parameters functions) next [ element; collection ] in
      let condition : L.prop = match evaluation.terms with
        | [ element; collection ] -> L.Membership (element, collection)
        | _ -> assert false
      in
      { condition; evaluation }
  | _ ->
      let result : term_result = translate_term env type_parameters functions next exp in
      { condition = L.IsTrue result.term;
        evaluation = { terms = []; premises = result.premises; binders = result.binders; next = result.next; helpers = result.helpers } }

let rec translate_premise (env : env) (type_parameters : string list)
    (functions : (string * L.type_ref) list) (next : int) (premise : S.prem) : terms_result =
  match premise.it with
  | RulePr (id, notation, _) | IfHoldPr (id, notation) ->
      let (application, result) : L.application * terms_result =
        translate_application env type_parameters functions next id.it [] (Mixfix.args notation)
      in
      { result with terms = []; premises = result.premises @ [ L.Holds application ] }
  | IfNotHoldPr (id, notation) ->
      let (application, result) : L.application * terms_result =
        translate_application env type_parameters functions next id.it [] (Mixfix.args notation)
      in
      { result with terms = []; premises = result.premises @ [ L.NotHolds (application, premise.at) ] }
  | IfPr exp ->
      let result : condition_result = translate_condition env type_parameters functions next exp in
      { result.evaluation with terms = []; premises = result.evaluation.premises @ [ L.Prop result.condition ] }
  | LetPr _ -> unsupported premise.at ("LetPr premise " ^ S.Print.string_of_prem premise)
  | IterPr (body, (iter, variables, outputs)) ->
      let body : terms_result = translate_premise env type_parameters functions (next + 1) body in
      translate_iteration env type_parameters functions premise.at next iter (variables @ outputs) body []
  | DebugPr _ ->
      { terms = []; premises = []; binders = []; next; helpers = [] }

let translate_branch (env : env) (type_parameters : string list)
    (relation_name : string) (arity : int) (input_positions : int list)
    (branch : branch) : L.rule * L.declaration list =
  if List.length branch.arguments <> arity then
    unsupported branch.at ("arity mismatch in rule " ^ branch.name ^ " of " ^ relation_name);
  let env : env = { env with iteration_prefix = relation_name ^ ":" ^ branch.name } in
  let functions : (string * L.type_ref) list =
    List.filter_map (function Function (id, typ) -> Some (id.it, typ) | Expression _ -> None) branch.arguments
  in
  let translate_argument (next : int) (argument : branch_argument) : term_result =
    match argument with
    | Expression exp -> translate_term env type_parameters functions next exp
    | Function (id, typ) -> pure_term next (L.Variable ("$" ^ id.it, typ))
  in
  (* Outputs are evaluated only after the premises succeed. Use the source
     input hint for relations too, including interleaved/multiple outputs. *)
  let inputs, outputs = Lang.Hints.Input.split input_positions branch.arguments in
  let result : terms_result = collect_terms translate_argument 0 inputs in
  let (result, catchable) : terms_result * int list = List.fold_left
    (fun ((result, catchable) : terms_result * int list) (premise : S.prem) ->
      let translated : terms_result =
        translate_premise env type_parameters functions result.next premise
      in
      let offset = List.length result.premises in
      let new_catchable = match premise.it with
        | RulePr _ ->
            List.filter_map (fun (index, item) ->
              match item with L.Holds _ -> Some (offset + index) | _ -> None)
              (List.mapi (fun index item -> index, item) translated.premises)
        | IfHoldPr _ ->
            (match List.rev translated.premises with
            | L.Holds _ :: _ -> [ offset + List.length translated.premises - 1 ]
            | _ -> [])
        | _ -> []
      in
      ({ result with premises = result.premises @ translated.premises;
         binders = result.binders @ translated.binders; next = translated.next;
         helpers = result.helpers @ translated.helpers },
       catchable @ new_catchable))
    (result, []) branch.premises
  in
  let outputs : terms_result =
    collect_terms translate_argument result.next outputs
  in
  let result : terms_result =
    { terms = Lang.Hints.Input.combine input_positions result.terms outputs.terms;
      premises = result.premises @ outputs.premises;
      binders = result.binders @ outputs.binders;
      next = outputs.next; helpers = result.helpers @ outputs.helpers }
  in
  let conclusion : L.application =
    { target = L.Global relation_name;
      type_arguments = List.map (fun name -> L.TypeParameter name) type_parameters;
      instance_arguments = [];
      print_instance_arguments = [];
      arguments = result.terms }
  in
  let variables : (string * L.type_ref) list =
    List.concat_map variables_in_term
      (conclusion.arguments @ List.concat_map Traversal.premise_terms result.premises)
  in
  { name = branch.name; binders = unique_binders env branch.at (variables @ result.binders);
    premises = result.premises; catchable; conclusion }, result.helpers

let branch_of_rule (rule : S.rule) : branch =
  let id, conclusion, premises = rule.it in
  let name : string = if id.it = "" then "rule" else id.it in
  {
    name;
    arguments = List.map (fun exp -> Expression exp) (Mixfix.args conclusion);
    premises;
    at = rule.at;
  }

let branch_of_clause (type_parameters : string list) (parameters : S.param list)
    (index : int) (clause : S.clause) : branch =
  let arguments, result, premises = clause.it in
  if List.length arguments <> List.length parameters then
    unsupported clause.at
      (Printf.sprintf "function clause argument count: expected %d, got %d"
         (List.length parameters) (List.length arguments));
  let arguments : branch_argument list =
    List.mapi
      (fun position ((parameter : S.param), (argument : S.arg)) ->
        match parameter.it, argument.it with
        | ExpP _, ExpA exp -> Expression exp
        | DefP _, DefA id ->
            Function
              (id, translate_parameter_with_parameters type_parameters parameter)
        | ExpP _, DefA _ ->
            unsupported argument.at
              (Printf.sprintf
                 "function clause argument %d: expected expression, got function"
                 (position + 1))
        | DefP _, ExpA _ ->
            unsupported argument.at
              (Printf.sprintf
                 "function clause argument %d: expected function, got expression"
                 (position + 1)))
      (List.combine parameters arguments)
  in
  {
    name = "case_" ^ string_of_int index;
    arguments = arguments @ [ Expression result ];
    premises;
    at = clause.at;
  }

let substitute_application (bindings : (string * L.type_ref) list)
    (application : L.application) : L.application =
  Traversal.map_application_types (substitute_type_parameters bindings) application

(* SpecTec uses a type name as a variable name, as in [$repeat_<X>(X, n)].
   A Lean binder [X] would shadow the type parameter [X], so rename the type
   parameter instead of the variable. *)
let rename_type_parameters (env : env) (type_parameters : string list)
    (argument_types : L.type_ref list) (rules : L.rule list) :
    string list * L.type_ref list * L.rule list =
  let binder_names : string list =
    List.concat_map (fun (rule : L.rule) -> List.map fst rule.binders) rules
  in
  let taken (name : string) : bool =
    List.mem name binder_names
    || List.mem name type_parameters
    || StringMap.mem name env.constructors
    || StringMap.mem name env.aliases
    || StringMap.mem name env.structures
  in
  let fresh (name : string) : string =
    let rec search (index : int) : string =
      let candidate : string =
        if index = 0 then name ^ "_T" else name ^ "_T" ^ string_of_int index
      in
      if taken candidate then search (index + 1) else candidate
    in
    search 0
  in
  let renamings : (string * string) list =
    List.filter_map
      (fun name ->
        if List.mem name binder_names then Some (name, fresh name) else None)
      type_parameters
  in
  if renamings = [] then (type_parameters, argument_types, rules)
  else
    let bindings : (string * L.type_ref) list =
      List.map (fun (name, renamed) -> (name, L.TypeParameter renamed)) renamings
    in
    let rename (name : string) : string =
      Option.value ~default:name (List.assoc_opt name renamings)
    in
    ( List.map rename type_parameters,
      List.map (substitute_type_parameters bindings) argument_types,
      List.map
        (fun (rule : L.rule) ->
          {
            rule with
            binders =
              List.map
                (fun (name, typ) ->
                  (name, substitute_type_parameters bindings typ))
                rule.binders;
            premises = List.map (Traversal.map_premise_types (substitute_type_parameters bindings)) rule.premises;
            conclusion = substitute_application bindings rule.conclusion;
          })
        rules )

let translate_relation_unrenamed ?input_positions (env : env) (name : string) (type_parameters : string list)
    (argument_types : L.type_ref list) (branches : branch list)
    (notation : L.notation_part list option) : L.declaration list =
  let arity : int = List.length argument_types in
  let input_positions = Option.value input_positions
    ~default:(List.init (max 0 (arity - 1)) Fun.id) in
  let (_, rules, helpers) : string list * L.rule list * L.declaration list =
    List.fold_left
      (fun (used, rules, helpers) (branch : branch) ->
        let rec unique_name (index : int) : string =
          let candidate : string =
            if index = 1 then branch.name
            else branch.name ^ "_" ^ string_of_int index
          in
          if List.mem candidate used then unique_name (index + 1) else candidate
        in
        let name_rule : string = unique_name 1 in
        let (rule, emitted) : L.rule * L.declaration list =
          translate_branch env type_parameters name arity input_positions
            { branch with name = name_rule }
        in
        (name_rule :: used, rule :: rules, helpers @ emitted))
      ([], [], []) branches
  in
  let rules : L.rule list = List.rev rules in
  L.Relation
    { name; type_parameters; equality_parameters = []; print_parameters = [];
      argument_types; input_positions = Some input_positions; rules; notation }
  :: helpers

let rename_relation_declarations (env : env) (type_parameters : string list)
    (declarations : L.declaration list) : L.declaration list =
  (* Helpers in a mutual block must use exactly their parent's parameters,
     including renamings needed to avoid element-variable shadowing. *)
  let all_rules : L.rule list = List.concat_map
    (function L.Relation { rules; _ } -> rules | _ -> []) declarations
  in
  let (renamed, _, _) : string list * L.type_ref list * L.rule list =
    rename_type_parameters env type_parameters [] all_rules
  in
  let bindings : (string * L.type_ref) list =
    List.combine type_parameters (List.map (fun name -> L.TypeParameter name) renamed)
  in
  let substitute : L.type_ref -> L.type_ref = substitute_type_parameters bindings in
  List.map
    (function
      | L.Relation relation -> L.Relation
          { relation with type_parameters = renamed;
            argument_types = List.map substitute relation.argument_types;
            rules = List.map (fun (rule : L.rule) ->
              { rule with binders = List.map (fun (name, typ) -> name, substitute typ) rule.binders;
                premises = List.map (Traversal.map_premise_types substitute) rule.premises;
                conclusion = substitute_application bindings rule.conclusion }) relation.rules }
      | declaration -> declaration)
    declarations

let translate_relation ?input_positions (env : env) (name : string) (type_parameters : string list)
    (argument_types : L.type_ref list) (branches : branch list)
    (notation : L.notation_part list option) : L.declaration list =
  rename_relation_declarations env type_parameters
    (translate_relation_unrenamed ?input_positions env name type_parameters argument_types branches notation)

type table_parameter = {
  lean_type : L.type_ref;
  type_name : string;
  variant : variant;
}

type selector_pattern_info =
  | AnySelectorPattern
  | ConstructorSelectorPattern of Mixfix.mixop * L.constructor_ref * int

let table_parameter (env : env) (parameter : S.param) : table_parameter =
  match parameter.it with
  | ExpP ({ it = VarT (id, []); _ } as typ) -> (
      match StringMap.find_opt id.it env.constructors with
      | Some variant ->
          { lean_type = translate_type typ; type_name = id.it; variant }
      | None ->
          unsupported typ.at
            ("table parameter type without a variant definition " ^ id.it))
  | ExpP typ ->
      unsupported typ.at
        ("table parameter type other than a variant without type arguments "
        ^ S.Print.string_of_typ typ)
  | DefP (id, _, _, _) ->
      unsupported parameter.at ("function parameter of table " ^ id.it)

let rec table_nested_pattern_irrefutable (env : env) (pattern : S.exp) : bool =
  match pattern.it with
  | VarE _ -> true
  | IterE (element, _) -> table_nested_pattern_irrefutable env element
  | CaseE notation -> (
      match pattern.note with
      | VarT (id, _) -> (
          match StringMap.find_opt id.it env.constructors with
          | Some { cases = [ (mixop, _, _) ]; _ }
            when Mixfix.eq_mixop mixop (Mixfix.to_mixop notation) ->
              List.for_all
                (table_nested_pattern_irrefutable env)
                (Mixfix.args notation)
          | _ -> false)
      | _ -> false)
  | _ -> false

let table_constructor_pattern (env : env) (parameter : table_parameter)
    (at : region) (notation : S.notexp) : selector_pattern_info =
  List.iter
    (fun pattern ->
      if not (table_nested_pattern_irrefutable env pattern) then
        unsupported pattern.at
          ("refutable nested table pattern " ^ S.Print.string_of_exp pattern))
    (Mixfix.args notation);
  let mixop : Mixfix.mixop = Mixfix.to_mixop notation in
  let arity : int =
    match
      List.find_opt
        (fun (candidate, _, _) -> Mixfix.eq_mixop candidate mixop)
        parameter.variant.cases
    with
    | Some (_, _, arguments) -> List.length arguments
    | None ->
        unsupported at
          ("table constructor lookup in " ^ parameter.type_name ^ ": "
          ^ String.concat " " (mixop_parts notation))
  in
  ConstructorSelectorPattern
    ( mixop,
      constructor_reference env at parameter.type_name [] notation,
      arity )

let table_pattern_alternatives (env : env) (parameter : table_parameter)
    (pattern : S.exp) : selector_pattern_info list =
  match pattern.it with
  | VarE _ -> [ AnySelectorPattern ]
  | CaseE notation ->
      [ table_constructor_pattern env parameter pattern.at notation ]
  | UpCastE (_, ({ it = CaseE notation; _ } as constructor)) ->
      [ table_constructor_pattern env parameter constructor.at notation ]
  | UpCastE (_, { it = VarE _; note = VarT (id, []); at }) -> (
      match StringMap.find_opt id.it env.constructors with
      | None ->
          unsupported at
            ("table subtype pattern without a variant definition " ^ id.it)
      | Some subtype ->
          List.map
            (fun (mixop, _, _) ->
              let notation : unit Mixfix.t = mixop in
              let arity : int =
                match
                  List.find_opt
                    (fun (candidate, _, _) -> Mixfix.eq_mixop candidate mixop)
                    parameter.variant.cases
                with
                | Some (_, _, arguments) -> List.length arguments
                | None ->
                    unsupported pattern.at
                      ("table subtype constructor lookup in "
                      ^ parameter.type_name ^ ": "
                      ^ String.concat " " (mixop_parts mixop))
              in
              ConstructorSelectorPattern
                ( mixop,
                  constructor_reference env pattern.at parameter.type_name []
                    notation,
                  arity ))
            subtype.cases)
  | UpCastE (_, { it = VarE _; _ }) ->
      unsupported pattern.at "table subtype pattern with a non-variant type"
  | _ ->
      unsupported pattern.at
        ("table row pattern " ^ S.Print.string_of_exp pattern)

let rec combinations (alternatives : 'a list list) : 'a list list =
  match alternatives with
  | [] -> [ [] ]
  | choices :: rest ->
      List.concat_map
        (fun choice -> List.map (fun tail -> choice :: tail) (combinations rest))
        choices

let selector_pattern_matches (pattern : selector_pattern_info)
    (constructor : Mixfix.mixop) : bool =
  match pattern with
  | AnySelectorPattern -> true
  | ConstructorSelectorPattern (expected, _, _) ->
      Mixfix.eq_mixop expected constructor

let selector_arm_matches (patterns : selector_pattern_info list)
    (constructors : Mixfix.mixop list) : bool =
  List.for_all2 selector_pattern_matches patterns constructors

let selector_pattern (pattern : selector_pattern_info) : L.selector_pattern =
  match pattern with
  | AnySelectorPattern -> L.Wildcard
  | ConstructorSelectorPattern (_, reference, arity) ->
      L.ConstructorPattern (reference, arity)

let table_selector (env : env) (name : string)
    (parameters : table_parameter list) (rows : S.tablerow list) : L.selector =
  let universe : Mixfix.mixop list list =
    parameters
    |> List.map (fun parameter ->
           List.map (fun (mixop, _, _) -> mixop) parameter.variant.cases)
    |> combinations
  in
  let (_, (arms, covered)) :
      int
      * ((L.selector_pattern list * int) list
        * selector_pattern_info list list) =
    List.fold_left
      (fun (row_index, (arms, covered)) (row : S.tablerow) ->
        let arguments, _ = row.it in
        if List.length arguments <> List.length parameters then
          unsupported row.at
            (Printf.sprintf "table row argument count: expected %d, got %d"
               (List.length parameters) (List.length arguments));
        let alternatives : selector_pattern_info list list =
          List.map2
            (fun parameter (argument : S.arg) ->
              match argument.it with
              | ExpA pattern -> table_pattern_alternatives env parameter pattern
              | DefA id ->
                  unsupported argument.at
                    ("function argument in table row " ^ id.it))
            parameters arguments
          |> combinations
        in
        let (row_arms, covered) :
            (L.selector_pattern list * int) list
            * selector_pattern_info list list =
          List.fold_left
            (fun (row_arms, covered) patterns ->
              let reachable : bool =
                List.exists
                  (fun constructors ->
                    selector_arm_matches patterns constructors
                    && not
                         (List.exists
                            (fun previous ->
                              selector_arm_matches previous constructors)
                            covered))
                  universe
              in
              if not reachable then row_arms, covered
              else
                ( row_arms
                  @ [ (List.map selector_pattern patterns, row_index) ],
                  covered @ [ patterns ] ))
            ([], covered) alternatives
        in
        if row_arms = [] then
          unsupported row.at
            (Printf.sprintf "dead table row %d of %s" row_index name);
        row_index + 1, (arms @ row_arms, covered))
      (0, ([], [])) rows
  in
  let missing : bool =
    List.exists
      (fun constructors ->
        not
          (List.exists
             (fun patterns -> selector_arm_matches patterns constructors)
             covered))
      universe
  in
  let arms : (L.selector_pattern list * int) list =
    if missing then
      arms
      @ [ (List.map (fun _ -> L.Wildcard) parameters, List.length rows) ]
    else arms
  in
  { L.name = name ^ ":row";
    parameters = List.map (fun parameter -> parameter.lean_type) parameters;
    arms }

let normalize_table_argument (result : S.exp) (argument : S.arg) : S.arg =
  match argument.it with
  | ExpA ({ it = UpCastE (_, ({ it = VarE id; _ } as variable)); _ } as exp) ->
      if Domain.Lib.IdSet.mem id (S.Free.free_exp result) then
        unsupported result.at
          ("table subtype variable used in result " ^ id.it);
      { argument with it = ExpA { exp with it = variable.it } }
  | _ -> argument

let translate_table (env : env) (id : S.id) (params : S.param list)
    (result_type : S.typ) (rows : S.tablerow list) : L.declaration list =
  let parameters : table_parameter list = List.map (table_parameter env) params in
  let relation_name : string = "$" ^ id.it in
  let selector : L.selector = table_selector env relation_name parameters rows in
  let selector_name : string = selector.name in
  let branches : branch list =
    List.mapi
      (fun index (row : S.tablerow) ->
        let arguments, result = row.it in
        let arguments : S.arg list =
          List.map (normalize_table_argument result) arguments
        in
        let clause : S.clause = (arguments, result, []) $ row.at in
        { (branch_of_clause [] params index clause) with
          name = "row_" ^ string_of_int index })
      rows
  in
  let argument_types : L.type_ref list =
    List.map (fun parameter -> parameter.lean_type) parameters
    @ [ translate_type result_type ]
  in
  let relation : L.declaration list =
    translate_relation env relation_name [] argument_types branches None
    |> List.map (function
         | L.Relation ({ name; rules; _ } as relation)
           when String.equal name relation_name ->
             let rules : L.rule list =
               List.mapi
                 (fun index (rule : L.rule) ->
                   let selector_arguments : L.term list =
                     List.filteri
                       (fun position _ -> position < List.length params)
                       rule.conclusion.arguments
                   in
                   let selected : L.term =
                     L.Apply
                       { target = L.Global selector_name;
                         type_arguments = []; instance_arguments = [];
                         print_instance_arguments = [];
                         arguments = selector_arguments }
                   in
                   let premise : L.premise =
                     L.Prop
                       (L.Comparison
                          ( L.Eq,
                            selected,
                            L.Number
                              (string_of_int index,
                               L.BuiltinType ("Nat", [])) ))
                   in
                   { rule with premises = premise :: rule.premises })
                 rules
             in
             L.Relation { relation with rules }
         | declaration -> declaration)
  in
  L.Selector selector :: relation

let translate_otherwise_relation (env : env) (name : string)
    (type_parameters : string list) (argument_types : L.type_ref list)
    (branches : branch list) (otherwise : branch) (inputs : Lang.Hints.Input.t)
    (notation : L.notation_part list option) : L.declaration list =
  let regular_name : string = name ^ ":regular" in
  let regular : L.declaration list =
    translate_relation_unrenamed ~input_positions:inputs env regular_name type_parameters argument_types branches None
  in
  let enabled_name : string = name ^ ":enabled" in
  let (input_types, _) : L.type_ref list * L.type_ref list =
    Lang.Hints.Input.split inputs argument_types
  in
  let enabled_rules, equality_parameters, print_parameters =
    match regular with
    | L.Relation relation :: _ ->
        (List.map
          (fun (rule : L.rule) : L.rule ->
            let (arguments, _) =
              Lang.Hints.Input.split inputs rule.conclusion.arguments
            in
            { name = "from_" ^ rule.name; binders = rule.binders;
              premises = [ L.Holds rule.conclusion ];
              catchable = [];
              conclusion = { rule.conclusion with
                target = L.Global enabled_name; arguments } })
          relation.rules,
         relation.equality_parameters, relation.print_parameters)
    | _ -> unsupported otherwise.at ("missing regular relation " ^ name)
  in
  let enabled : L.declaration =
    L.Relation
      { name = enabled_name; type_parameters; equality_parameters;
        print_parameters; argument_types = input_types;
        input_positions = Some (List.init (List.length input_types) Fun.id);
        rules = enabled_rules; notation = None }
  in
  let public : L.declaration list =
    translate_relation_unrenamed ~input_positions:inputs env name type_parameters argument_types [ otherwise ] notation
  in
  let binders : (string * L.type_ref) list =
    List.mapi (fun index typ -> "arg:" ^ string_of_int index, typ) argument_types
  in
  let application : L.application =
    { target = L.Global name;
      type_arguments = List.map (fun name -> L.TypeParameter name) type_parameters;
      instance_arguments = [];
      print_instance_arguments = [];
      arguments = List.map (fun (name, typ) -> L.Variable (name, typ)) binders }
  in
  let wrapper : L.rule =
    { name = "regular"; binders;
      premises = [ L.Holds { application with target = L.Global regular_name } ];
      catchable = [];
      conclusion = application }
  in
  let guard (rule : L.rule) : L.rule =
    let (arguments, _) : L.term list * L.term list =
      Lang.Hints.Input.split inputs rule.conclusion.arguments
    in
    let negative : L.application =
      { rule.conclusion with target = L.Global enabled_name; arguments }
    in
    { rule with premises = L.NotHolds (negative, otherwise.at) :: rule.premises;
      catchable = List.map (( + ) 1) rule.catchable }
  in
  let public : L.declaration list = match public with
    | L.Relation relation :: helpers ->
        let rules : L.rule list = List.map guard relation.rules in
        let rec wrapper_name (index : int) : string =
          let candidate : string = if index = 0 then "regular" else "regular_" ^ string_of_int index in
          if List.exists (fun (rule : L.rule) -> rule.name = candidate) rules then
            wrapper_name (index + 1)
          else candidate
        in
        L.Relation { relation with rules = { wrapper with name = wrapper_name 0 } :: rules } :: helpers
    | _ -> unsupported otherwise.at ("missing otherwise relation " ^ name)
  in
  rename_relation_declarations env type_parameters (regular @ [ enabled ] @ public)

let rec validate_names (at : region) (names : string list) : unit =
  match names with
  | [] -> ()
  | name :: rest ->
      if name = "" then unsupported at "unnamed rules";
      if List.mem name rest then
        unsupported at ("duplicate constructor name " ^ name);
      validate_names at rest

let reserved_structure_field (name : string) : bool =
  let numbered (prefix : string) : bool =
    if not (String.starts_with ~prefix name) then false
    else
      let suffix : string =
        String.sub name (String.length prefix)
          (String.length name - String.length prefix)
      in
      let suffix : string =
        if String.ends_with ~suffix:"_eq" suffix then
          String.sub suffix 0 (String.length suffix - 3)
        else suffix
      in
      suffix <> "" && String.for_all Identifier.is_digit suffix
  in
  List.mem name
    [ "mk"; "rec"; "recOn"; "casesOn"; "noConfusion";
      "noConfusionType"; "below"; "brecOn"; "ctorIdx"; "_sizeOf_inst" ]
  || List.exists numbered [ "rec_"; "below_"; "brecOn_"; "_sizeOf_" ]

let translate_structure_fields (env : env) (fields : structure_field list) :
    (string * L.type_ref) list =
  List.map
    (fun (field : structure_field) ->
      if Identifier.contains_closing_quote field.name then
        unsupported field.atom.at
          ("structure field name containing closing quote »: " ^ field.name);
      if List.length (List.filter (fun other -> other.name = field.name) fields) > 1
      then unsupported field.atom.at ("duplicate structure field name " ^ field.name);
      if reserved_structure_field field.name then
        unsupported field.atom.at
          ("structure field name reserved by Lean " ^ field.name);
      ( field.name,
        translate_type field.typ |> expand_generic_aliases env field.typ.at [] ))
    fields

let translate_declaration (env : env) (decl : S.def) : L.declaration list =
  let declarations : L.declaration list =
    match decl.it with
    | TypD (id, tparams, { it = VariantT cases; _ }, _) ->
        let type_parameters : string list =
          List.map (fun (parameter : S.tparam) -> parameter.it) tparams
        in
        let constructors : L.constructor list =
          List.map (translate_constructor env id.it type_parameters) cases
        in
        [ L.Datatype { name = id.it; type_parameters; constructors } ]
    | TypD (id, tparams, { it = PlainT typ; _ }, _) ->
        let type_parameters : string list =
          List.map (fun (parameter : S.tparam) -> parameter.it) tparams
        in
        [ L.TypeAlias
             {
               name = id.it;
               type_parameters;
               body = translate_type_with_parameters type_parameters typ;
             } ]
    | TypD (id, tparams, { it = StructT _; _ }, _) ->
        if tparams <> [] then
          unsupported decl.at ("type parameters of structure " ^ id.it);
        [ L.Structure
             {
               name = id.it;
               fields =
                 translate_structure_fields env
                   (StringMap.find id.it env.structures);
             } ]
    | ExternTypD (id, _) ->
        if not (List.mem id.it [ "json"; "archState"; "objectState" ]) then
          unsupported decl.at ("unknown external type declaration " ^ id.it);
        [ L.ExternType id.it ]
    | VarD _ ->
        (* TODO: Translate metavariable declarations. *)
        []
    | ExternRelD (id, nottyp, _, _) ->
        if not (List.mem id.it
          [ "Call_extern_func"; "Call_builtin_func"; "Call_extern_rel";
            "ExternFunctionCall_eval_lctk"; "ExternFunctionCall_eval";
            "ExternMethodCall_eval" ]) then
          unsupported decl.at ("unknown external relation declaration " ^ id.it);
        let argument_types = List.map translate_type (Mixfix.args nottyp.it) in
        [ Extern_model.relation id.it argument_types
            (Extern_model.relation_predicate id.it)
            (Some (translate_notation nottyp.it)) ]
    | RelD (id, nottyp, inputs, rulegroups, elsegroup, _) ->
        let argument_types : L.type_ref list =
          List.map translate_type (Mixfix.args nottyp.it)
        in
        let branches : branch list =
          List.concat_map
            (fun (group : S.rulegroup) ->
              List.map branch_of_rule (snd group.it))
            rulegroups
        in
        let notation : L.notation_part list = translate_notation nottyp.it in
        if
          not
            (List.exists
               (function L.Literal _ -> true | L.Hole -> false)
               notation)
        then unsupported nottyp.at "relation notation without a visible atom";
        (match elsegroup with
        | None -> translate_relation ~input_positions:inputs env id.it [] argument_types branches (Some notation)
        | Some group ->
            let otherwise : branch = branch_of_rule (snd group.it) in
            translate_otherwise_relation env id.it [] argument_types branches otherwise inputs
              (Some notation))
    | ExternDecD (id, tparams, params, result, _) ->
        if tparams <> [] || not (List.mem id.it [ "init_archState"; "init_objectState" ])
        then unsupported decl.at ("unknown external function declaration " ^ id.it);
        let arguments = List.map (translate_parameter_with_parameters []) params in
        [ Extern_model.relation ("$" ^ id.it)
            (arguments @ [ translate_type result ])
            (Extern_model.function_predicate id.it) None ]
    | BuiltinDecD (id, tparams, params, result, _) ->
        let type_parameters : string list =
          List.map (fun (parameter : S.tparam) -> parameter.it) tparams
        in
        let parameters : L.type_ref list =
          List.map
            (fun (parameter : S.param) ->
              match parameter.it with
              | ExpP typ -> translate_type_with_parameters type_parameters typ
              | DefP (id, _, _, _) ->
                  unsupported parameter.at ("builtin function parameter " ^ id.it))
            params
        in
        let result : L.type_ref =
          translate_type_with_parameters type_parameters result
        in
        if Builtin_relation.is_relation id.it then
          let (expected_parameters, expected_result) : L.type_ref list * L.type_ref =
            match Builtin_relation.signature id.it type_parameters with
            | Ok signature -> signature
            | Error reason -> unsupported decl.at ("builtin relation " ^ reason)
          in
          if parameters <> expected_parameters || result <> expected_result then
            unsupported decl.at
              ("builtin relation " ^ id.it
             ^ " because its signature differs from the SpecTec implementation");
          (match
             Builtin_relation.translate id.it type_parameters
               (builtin_constructor env decl.at)
           with
          | Ok declarations -> declarations
          | Error reason -> unsupported decl.at ("builtin relation " ^ reason))
        else
          (match Builtin.signature id.it type_parameters with
          | Ok (expected_parameters, expected_result) ->
              if parameters <> expected_parameters || result <> expected_result then
                unsupported decl.at
                  ("builtin function " ^ id.it
                 ^ " because its signature differs from the SpecTec implementation");
              (match Builtin.translate id.it type_parameters with
              | Ok builtin ->
                  [ L.Builtin { builtin with name = "$" ^ builtin.name } ]
              | Error reason ->
                  unsupported decl.at ("builtin function " ^ reason))
          (* A rule-less relation would claim that the builtin has no result. *)
          | Error reason -> unsupported decl.at ("builtin function " ^ reason))
    | TableDecD (id, params, result, rows, _) ->
        translate_table env id params result rows
    | FuncDecD (id, tparams, params, result, clauses, elseclause, _) ->
        let type_parameters : string list =
          List.map (fun (parameter : S.tparam) -> parameter.it) tparams
        in
        let argument_types : L.type_ref list =
          List.map (translate_parameter_with_parameters type_parameters) params
          @ [ translate_type_with_parameters type_parameters result ]
        in
        let branches : branch list =
          List.mapi
            (fun index clause ->
              branch_of_clause type_parameters params (index + 1) clause)
            clauses
        in
        (match elseclause with
        | None -> translate_relation env ("$" ^ id.it) type_parameters argument_types branches None
        | Some clause ->
            let otherwise : branch =
              branch_of_clause type_parameters params (List.length clauses + 1) clause
            in
            translate_otherwise_relation env ("$" ^ id.it) type_parameters argument_types
              branches otherwise (List.init (List.length params) Fun.id) None)
  in
  List.iter
    (function
      | L.Datatype { constructors; _ } ->
          validate_names decl.at
            (List.map
               (fun (constructor : L.constructor) -> constructor.name)
               constructors)
      | L.Relation { rules; _ } ->
          validate_names decl.at
            (List.map (fun (rule : L.rule) -> rule.name) rules)
      | L.TypeAlias _ -> ()
      | L.ExternType _ -> ()
      | L.Structure _ -> ()
      | L.Builtin _ | L.Selector _ | L.Coercion _ | L.Membership _ -> ())
    declarations;
  declarations

let rec type_parameters_in (typ : L.type_ref) : string list =
  match typ with
  | TypeParameter name -> [ name ]
  | Name _ -> []
  | Applied (_, arguments) | BuiltinType (_, arguments) ->
      List.concat_map type_parameters_in arguments
  | TupleType elements -> List.concat_map type_parameters_in elements
  | RelationType (arguments, result) ->
      List.concat_map type_parameters_in (result :: arguments)

let rec equality_types_in_term (term : L.term) : L.type_ref list =
  let nested : L.type_ref list =
    List.concat_map equality_types_in_term (Traversal.term_children term)
  in
  match term with L.Decide (types, _) -> types @ nested | _ -> nested

let relation_terms (rules : L.rule list) : L.term list =
  List.concat_map
    (fun (rule : L.rule) ->
      rule.conclusion.arguments
      @ List.concat_map Traversal.premise_terms rule.premises)
    rules

let relation_applications (rules : L.rule list) : L.application list =
  List.concat_map
    (fun (rule : L.rule) ->
      rule.conclusion
      :: (List.concat_map Traversal.term_applications
            rule.conclusion.arguments
         @ List.concat_map Traversal.premise_applications rule.premises))
    rules

(* The source interpreter keeps the fresh counter across nested calls and
   across clauses which fail after evaluating a guard. Give every relation
   which can reach fresh an entry and exit counter. Its ordinary public name
   is an entry point at zero; calls made while evaluating another relation
   use the :state relation and pass the current counter. *)
module Fresh_state = struct
  let nat = L.BuiltinType ("Nat", [])
  let zero = L.Number ("0", nat)
  let state_name name = name ^ ":state"
  (* fail:i summarizes failure of clauses 0 through i. Exact mode includes their
     effects; rollback mode records only the counter at the call's entry. *)
  let fail_name name index = name ^ ":fail:" ^ string_of_int index
  let all_fail_name name = name ^ ":fail"
  let match_name name index = name ^ ":match:" ^ string_of_int index
  let call_match_name name index position =
    name ^ ":callmatch:" ^ string_of_int index ^ ":" ^ string_of_int position
  let variable name = L.Variable (name, nat)
  let counter index = "fresh:counter:" ^ string_of_int index
  let initial = variable (counter 0)

  let target_name = function L.Global name -> Some name | L.Local _ -> None

  let active (names : StringSet.t) (application : L.application) : bool =
    match target_name application.target with
    | Some name -> StringSet.mem name names
    | None -> false

  let effectful (declarations : L.located_declaration list) : StringSet.t =
    let rec close names =
      let next = List.fold_left (fun names located ->
        match located.L.declaration with
        | L.Relation { name; rules; _ } ->
            if List.exists (active names) (relation_applications rules)
            then StringSet.add name names else names
        | _ -> names) names declarations in
      if StringSet.equal names next then names else close next
    in
    close (StringSet.singleton "$fresh_typeId")

  (* The pure WFS encoding implements otherwise with regular/enabled wrappers.
     Stateful evaluation must try the source clauses once, in order. Flatten
     those wrappers before lowering so the ordinary failure chain implements
     source priority with the selected counter policy. *)
  let inline_otherwise names declarations =
    let relations = List.fold_left (fun map located ->
      match located.L.declaration with
      | L.Relation { name; rules; _ } -> StringMap.add name rules map
      | _ -> map) StringMap.empty declarations in
    let replacements, removed = List.fold_left (fun (replacements, removed) located ->
      match located.L.declaration with
      | L.Relation ({ name; rules = [ wrapper; fallback ]; _ } as relation)
        when StringSet.mem name names ->
          let regular = name ^ ":regular" and enabled = name ^ ":enabled" in
          (match StringMap.find_opt regular relations, wrapper.premises, fallback.premises with
          | Some rules, [ L.Holds call ], L.NotHolds (guard, _) :: premises
            when call.target = L.Global regular && guard.target = L.Global enabled ->
              let rules = List.map (fun (rule : L.rule) ->
                { rule with conclusion = { rule.conclusion with target = L.Global name } }) rules in
              let rec fallback_name index =
                let candidate = if index = 1 then fallback.name
                  else fallback.name ^ "_" ^ string_of_int index in
                if List.exists (fun (rule : L.rule) -> rule.name = candidate) rules
                then fallback_name (index + 1) else candidate in
              let fallback = { fallback with name = fallback_name 1; premises;
                catchable = List.map (fun position -> position - 1) fallback.catchable } in
              let replacement = L.Relation { relation with rules = rules @ [ fallback ] } in
              StringMap.add name replacement replacements,
              StringSet.add regular (StringSet.add enabled removed)
          | _ -> replacements, removed)
      | _ -> replacements, removed)
      (StringMap.empty, StringSet.empty) declarations in
    List.filter_map (fun located ->
      match located.L.declaration with
      | L.Relation { name; _ } when StringSet.mem name removed -> None
      | L.Relation { name; _ } ->
          Some { located with declaration =
            Option.value (StringMap.find_opt name replacements) ~default:located.declaration }
      | _ -> Some located) declarations

  let state_call name before args after (application : L.application) =
    { application with target = L.Global (state_name name);
      arguments = before :: args @ [ after ] }

  let split_result arguments =
    match List.rev arguments with
    | _result :: reversed_inputs -> List.rev reversed_inputs
    | [] -> []

  let project (positions : int list) arguments =
    List.filteri (fun index _ -> List.mem index positions) arguments

  let inputs_for (positions : int list StringMap.t) name arguments =
    match StringMap.find_opt name positions with
    | Some indices -> project indices arguments
    | None -> split_result arguments

  let sequence ~rollback (active_names : StringSet.t) (positions : int list StringMap.t)
      (premises : L.premise list)
      (start : int) : L.premise list * (string * L.type_ref) list * int =
    List.fold_left (fun (translated, binders, index) premise ->
      let before = variable (counter index) in
      match premise with
      | L.Holds application when active active_names application ->
          let name = Option.get (target_name application.target) in
          let next = index + 1 in
          (translated @ [ L.Holds (state_call name before application.arguments
                                      (variable (counter next)) application) ],
           binders @ [ counter next, nat ], next)
      | L.NotHolds (application, _) when active active_names application ->
          let name = Option.get (target_name application.target) in
          let next = index + 1 in
          let failure = { application with target = L.Global (all_fail_name name);
            arguments = before :: inputs_for positions name application.arguments
                        @ (if rollback then [] else [ variable (counter next) ]) } in
          (translated @ [ L.Holds failure ],
           binders @ (if rollback then [] else [ counter next, nat ]),
           if rollback then index else next)
      | _ -> translated @ [ premise ], binders, index)
      ([], [], start) premises

  let make_relation template name argument_types rules =
    match template with
    | L.Relation relation ->
        L.Relation { relation with name; argument_types; rules; notation = None }
    | _ -> invalid_arg "fresh state requires a relation"

  let fresh_rule () =
    let before = initial in
    let fresh = L.Binary ("++", L.Text "FRESH__",
                          L.Native ("Nat.repr", [ before ])) in
    let after = L.Binary ("+", before, L.Number ("1", nat)) in
    { L.name = "next"; binders = [ counter 0, nat ]; premises = [];
      catchable = [];
      conclusion = { target = L.Global (state_name "$fresh_typeId");
        type_arguments = []; instance_arguments = [];
        print_instance_arguments = [];
        arguments = [ before; fresh; after ] } }

  (* Distinct variables (possibly in tuples) match every value of the input
     type. Repeated variables, constants and variant/list patterns can fail. *)
  let irrefutable_inputs terms =
    let rec pattern seen = function
      | L.Variable (name, _) when not (StringSet.mem name seen) ->
          Some (StringSet.add name seen)
      | L.Typed (term, _) -> pattern seen term
      | L.Tuple (left, right) ->
          Option.bind (pattern seen left) (fun seen -> pattern seen right)
      | _ -> None in
    List.fold_left (fun seen term -> Option.bind seen (fun seen -> pattern seen term))
      (Some StringSet.empty) terms
    |> Option.is_some

  let lower_relation ~rollback (names : StringSet.t) (positions : int list StringMap.t)
      (located : L.located_declaration) :
      L.located_declaration list =
    match located.declaration with
    | L.Relation ({ name; argument_types; rules; _ } as relation)
      when StringSet.mem name names ->
        if relation.input_positions = None then
          unsupported located.at
            ("fresh counter through relation " ^ name
             ^ " without declared input positions");
        let original = L.Relation relation in
        let state_type = nat :: argument_types @ [ nat ] in
        let input_types = inputs_for positions name argument_types in
        let fail_type = nat :: input_types @ (if rollback then [] else [ nat ]) in
        let failure_arguments before inputs after =
          before :: inputs @ (if rollback then [] else [ after ]) in
        let state_rules, helpers =
          if name = "$fresh_typeId" then [ fresh_rule () ], []
          else
            List.mapi (fun index rule ->
              let previous, previous_binders, current =
                if index = 0 then [], [], 0 else
                  let call = { rule.L.conclusion with
                    target = L.Global (fail_name name (index - 1));
                    arguments = failure_arguments initial
                      (inputs_for positions name rule.conclusion.arguments)
                      (variable (counter 1)) } in
                  [ L.Holds call ], (if rollback then [] else [ counter 1, nat ]),
                  if rollback then 0 else 1
              in
              let premises, binders, finish = sequence ~rollback names positions rule.premises current in
              let success = { rule with
                binders = (counter 0, nat) :: rule.binders
                          @ previous_binders @ binders;
                premises = previous @ premises;
                conclusion = state_call name initial rule.conclusion.arguments
                  (variable (counter finish)) rule.conclusion } in
              let input_terms = inputs_for positions name rule.conclusion.arguments in
              let needs_match = not (irrefutable_inputs input_terms) in
              let input_names = List.concat_map variables_in_term input_terms |> List.map fst in
              let matcher = make_relation original (match_name name index)
                input_types
                [ { rule with name = "recognize"; premises = [];
                    binders = List.filter (fun (name, _) -> List.mem name input_names) rule.binders;
                    conclusion = { rule.conclusion with
                      target = L.Global (match_name name index);
                      arguments = input_terms } } ] in
              let generic = List.mapi (fun i typ ->
                L.Variable ("fresh:input:" ^ string_of_int i, typ)) input_types in
              let mismatch_call = { rule.conclusion with
                target = L.Global (match_name name index); arguments = generic } in
              let mismatch = { L.name = "mismatch";
                binders = (counter 0, nat) :: List.mapi
                  (fun i typ -> "fresh:input:" ^ string_of_int i, typ) input_types;
                premises = [ L.NotHolds (mismatch_call, located.at) ];
                catchable = [];
                conclusion = { rule.conclusion with
                  target = L.Global (fail_name name index);
                  arguments = failure_arguments initial generic initial } } in
              let failed_guards =
                List.filter_map (fun (position, premise) ->
                  let prefix = List.filteri (fun i _ -> i < position) rule.premises in
                  let bound_names =
                    List.concat_map variables_in_term
                      (input_terms @ List.concat_map Traversal.premise_terms prefix)
                    |> List.map fst in
                  let fully_bound =
                    List.concat_map variables_in_term
                      (Traversal.premise_terms premise)
                    |> List.for_all (fun (name, _) -> List.mem name bound_names)
                  in
                  let prefix, prefix_binders, at = sequence ~rollback names positions prefix 0 in
                  let before = variable (counter at) in
                  let call_match (application : L.application) =
                    let fixed = List.filter
                      (fun (variable, _) -> List.mem variable bound_names)
                      rule.binders in
                    let arguments = List.map
                      (fun (variable, typ) -> L.Variable (variable, typ)) fixed in
                    let helper_name = call_match_name name index position in
                    let call = { rule.conclusion with
                      target = L.Global helper_name; arguments } in
                    let helper_rule = { rule with
                      name = "has_match"; premises = [ L.Holds application ];
                      catchable = []; conclusion = call }
                      |> Relation_optimizer.trim_failure_binders in
                    let helper = make_relation original helper_name
                      (List.map snd fixed) [ helper_rule ] in
                    L.NotHolds (call, located.at), helper
                  in
                  let failure = match premise with
                    | L.Prop proposition ->
                        (* A binding pattern fails only when no assignment to
                           its newly introduced variables can satisfy it. *)
                        let mentioned = List.concat_map variables_in_term
                          (Traversal.prop_terms proposition) |> List.map fst in
                        let unbound = List.filter (fun (name, _) ->
                          List.mem name mentioned && not (List.mem name bound_names))
                          rule.binders in
                        let binds_value pattern value = match pattern with
                          | L.Variable (name, _) when not (List.mem name bound_names) ->
                              List.for_all (fun (name, _) -> List.mem name bound_names)
                                (variables_in_term value)
                          | _ -> false in
                        let irrefutable = match proposition with
                          | L.Comparison (L.Eq, left, right) ->
                              binds_value left right || binds_value right left
                          | _ -> false in
                        (* A fresh variable can always bind an evaluated value;
                           its universally negated equality is unsatisfiable. *)
                        if irrefutable then None else
                        let failure = List.fold_right (fun (name, typ) body ->
                          L.Forall (name, typ, body)) unbound (L.Not proposition) in
                        Some (L.Prop failure, before, [], [])
                    | L.Holds application
                      when List.mem position rule.catchable
                           && active names application ->
                        let target = Option.get (target_name application.target) in
                        let inputs = inputs_for positions target application.arguments in
                        let inputs_bound = List.concat_map variables_in_term inputs
                          |> List.for_all (fun (name, _) -> List.mem name bound_names) in
                        if not inputs_bound then None else
                        let next = at + 1 in
                        Some (L.Holds { application with
                          target = L.Global (all_fail_name target);
                          arguments = failure_arguments before inputs (variable (counter next)) },
                          (if rollback then before else variable (counter next)),
                          (if rollback then [] else [ counter next, nat ]), [])
                    | L.Holds application
                      when List.mem position rule.catchable && fully_bound ->
                        Some (L.NotHolds (application, located.at), before, [], [])
                    | L.Holds application when List.mem position rule.catchable ->
                        let negative, helper = call_match application in
                        Some (negative, before, [], [ helper ])
                    | L.NotHolds (application, _) when active names application ->
                        let target = Option.get (target_name application.target) in
                        let next = at + 1 in
                        Some (L.Holds (state_call target before
                          application.arguments (variable (counter next)) application),
                          (if rollback then before else variable (counter next)),
                          [ counter next, nat ], [])
                    | L.NotHolds (application, _) when fully_bound ->
                        Some (L.Holds application, before, [], [])
                    | L.Holds _ | L.NotExists _ | L.NotHolds _ -> None
                  in
                  Option.map (fun (negative, after, extra, generated) ->
                    let rec quantified = function
                      | L.Forall (name, _, body) -> name :: quantified body
                      | _ -> [] in
                    let bound = match negative with
                      | L.Prop proposition -> quantified proposition
                      | _ -> [] in
                    (* Newly quantified variables occur in neither the input
                       nor the prefix. Do not demand outer witnesses for them. *)
                    let binders = List.filter (fun (name, _) -> not (List.mem name bound))
                      rule.binders in
                    { L.name = "guard_" ^ string_of_int position;
                      binders = (counter 0, nat) :: binders
                        @ prefix_binders @ extra;
                      premises = prefix @ [ negative ]; catchable = [];
                      conclusion = { rule.conclusion with
                        target = L.Global (fail_name name index);
                        arguments = failure_arguments initial input_terms after } },
                    generated) failure)
                  (List.mapi (fun i premise -> i, premise) rule.premises) in
              let call_helpers = List.concat_map snd failed_guards in
              let failed_guards = List.map fst failed_guards in
              let failures = failed_guards @ (if needs_match then [ mismatch ] else []) in
              let failures = if index = 0 then failures else if rollback then
                List.map (fun (failure : L.rule) ->
                  let previous = { failure.conclusion with
                    target = L.Global (fail_name name (index - 1)) } in
                  { failure with premises = L.Holds previous :: failure.premises }) failures
                else
                List.map (fun (failure : L.rule) ->
                  let entry = variable "fresh:entry" in
                  let inputs = List.tl (split_result failure.conclusion.arguments) in
                  let previous = { failure.conclusion with
                    target = L.Global (fail_name name (index - 1));
                    arguments = entry :: inputs @ [ initial ] } in
                  { failure with
                    binders = ("fresh:entry", nat) :: failure.binders;
                    premises = L.Holds previous :: failure.premises;
                    conclusion = { failure.conclusion with
                      arguments = entry :: List.tl failure.conclusion.arguments } }) failures in
              let failures = List.map Relation_optimizer.trim_failure_binders failures in
              let failure = make_relation original (fail_name name index) fail_type failures in
              success, (if needs_match then [ matcher ] else []) @ call_helpers @ Relation_optimizer.share failure) rules
            |> fun lowered ->
               List.map fst lowered, List.concat_map snd lowered
        in
        let all_fail =
          let inputs = List.mapi (fun i typ ->
            L.Variable ("fresh:input:" ^ string_of_int i, typ)) input_types in
          let premises = [ L.Holds {
              target = L.Global (fail_name name (List.length rules - 1));
              type_arguments = List.map (fun n -> L.TypeParameter n)
                relation.type_parameters;
              instance_arguments = []; print_instance_arguments = [];
              arguments = failure_arguments initial inputs (variable (counter 1)) } ] in
          let rule = { L.name = "all_failed";
            binders = [ counter 0, nat ] @ (if rollback then [] else [ counter 1, nat ])
              @ List.mapi (fun i typ -> "fresh:input:" ^ string_of_int i, typ)
                  input_types;
            premises; catchable = [];
            conclusion = { target = L.Global (all_fail_name name);
              type_arguments = List.map (fun n -> L.TypeParameter n)
                relation.type_parameters;
              instance_arguments = []; print_instance_arguments = [];
              arguments = failure_arguments initial inputs (variable (counter 1)) } } in
          make_relation original (all_fail_name name) fail_type
            (if rules = [] then [] else [ rule ])
        in
        let state_relation = make_relation original (state_name name) state_type state_rules in
        let inputs = List.mapi (fun i typ ->
          L.Variable ("fresh:arg:" ^ string_of_int i, typ)) argument_types in
        let final = variable "fresh:final" in
        let wrapper_call : L.application = { target = L.Global (state_name name);
          type_arguments = List.map (fun n -> L.TypeParameter n) relation.type_parameters;
          instance_arguments = []; print_instance_arguments = [];
          arguments = zero :: inputs @ [ final ] } in
        let wrapper = make_relation original name argument_types
          [ { L.name = "from_initial_counter";
              binders = ("fresh:final", nat) ::
                List.mapi (fun i typ -> "fresh:arg:" ^ string_of_int i, typ)
                  argument_types;
              premises = [ L.Holds wrapper_call ]; catchable = [];
              conclusion = { wrapper_call with target = L.Global name;
                arguments = inputs } } ] in
        List.map (fun declaration -> { located with declaration })
          (state_relation :: helpers @ [ all_fail; wrapper ])
    | _ -> [ located ]

  let lower ?(rollback = false) declarations =
    if not (List.exists (function
      | { L.declaration = L.Relation { name = "$fresh_typeId"; _ }; _ } -> true
      | _ -> false) declarations)
    then declarations
    else
      let declarations = inline_otherwise (effectful declarations) declarations in
      let names = effectful declarations in
      let rec stateful_reference term =
        match term with
        | L.FunctionReference (L.Global name) when StringSet.mem name names ->
            Some name
        | _ ->
            List.find_map stateful_reference (Traversal.term_children term)
      in
      List.iter (fun located ->
        match located.L.declaration with
        | L.Relation { rules; _ } ->
            (match List.find_map stateful_reference (relation_terms rules) with
            | Some name -> unsupported located.at
                ("stateful function argument " ^ name
                 ^ " because a function value cannot carry the fresh counter")
            | None -> ())
        | _ -> ()) declarations;
      let positions = List.fold_left (fun positions located ->
        match located.L.declaration with
        | L.Relation { name; input_positions = Some indices; _ } ->
            StringMap.add name indices positions
        | _ -> positions) StringMap.empty declarations in
      List.concat_map (lower_relation ~rollback names positions) declarations
end

let required_type_parameters (parameters : string list)
    (types : L.type_ref list) : string list =
  let mentioned : string list = List.concat_map type_parameters_in types in
  List.filter (fun parameter -> List.mem parameter mentioned) parameters

type instance_signature = {
  type_parameters : string list;
  equality : string list;
  printer : string list;
}

let equality_parameters (declarations : L.located_declaration list) :
    L.located_declaration list =
  let signatures : instance_signature StringMap.t =
    List.fold_left
      (fun signatures (located : L.located_declaration) ->
        match located.declaration with
        | L.Relation
            { name; type_parameters; equality_parameters; print_parameters;
              rules; _ } ->
            let direct : string list =
              relation_terms rules
              |> List.concat_map equality_types_in_term
              |> required_type_parameters type_parameters
            in
            StringMap.add name
              { type_parameters;
                equality =
                  List.filter
                    (fun parameter ->
                      List.mem parameter equality_parameters
                      || List.mem parameter direct)
                    type_parameters;
                printer = print_parameters }
              signatures
        | L.Builtin builtin ->
            StringMap.add builtin.name
              { type_parameters = builtin.type_parameters;
                equality = builtin.equality_parameters;
                printer = builtin.print_parameters }
              signatures
        | _ -> signatures)
      StringMap.empty declarations
  in
  let rec parameter_position (name : string) (index : int)
      (parameters : string list) : int option =
    match parameters with
    | [] -> None
    | parameter :: _ when parameter = name -> Some index
    | _ :: rest -> parameter_position name (index + 1) rest
  in
  let required_by_application (caller_parameters : string list)
      (select : instance_signature -> string list)
      (signatures : instance_signature StringMap.t)
      (application : L.application) : string list =
    match application.target with
    | L.Local _ -> []
    | L.Global name -> (
        match StringMap.find_opt name signatures with
        | None -> []
        | Some signature ->
            let types : L.type_ref list =
              List.filter_map
                (fun parameter ->
                  match
                    parameter_position parameter 0 signature.type_parameters
                  with
                  | Some index -> List.nth_opt application.type_arguments index
                  | None -> None)
                (select signature)
            in
            required_type_parameters caller_parameters types)
  in
  let rec close (signatures : instance_signature StringMap.t) :
      instance_signature StringMap.t =
    let changed : bool ref = ref false in
    let next : instance_signature StringMap.t =
      List.fold_left
        (fun next (located : L.located_declaration) ->
          match located.declaration with
          | L.Relation { name; type_parameters; rules; _ } ->
              let current : instance_signature =
                StringMap.find name signatures in
              let called_equalities : string list =
                relation_applications rules
                |> List.concat_map
                     (required_by_application type_parameters
                        (fun signature -> signature.equality) signatures)
              in
              let called_printers : string list =
                relation_applications rules
                |> List.concat_map
                     (required_by_application type_parameters
                        (fun signature -> signature.printer) signatures)
              in
              let equality : string list =
                List.filter
                  (fun parameter ->
                    List.mem parameter current.equality
                    || List.mem parameter called_equalities)
                  type_parameters
              in
              let printer : string list =
                List.filter
                  (fun parameter ->
                    List.mem parameter current.printer
                    || List.mem parameter called_printers)
                  type_parameters
              in
              if equality <> current.equality || printer <> current.printer
              then changed := true;
              StringMap.add name { type_parameters; equality; printer } next
          | _ -> next)
        signatures declarations
    in
    if !changed then close next else next
  in
  let signatures : instance_signature StringMap.t = close signatures in
  let arguments (select : instance_signature -> string list)
      (value : L.application) : L.type_ref list =
    match value.target with
    | L.Local _ -> []
    | L.Global name -> (
        match StringMap.find_opt name signatures with
        | None -> []
        | Some signature ->
            List.filter_map
              (fun parameter ->
                match
                  parameter_position parameter 0 signature.type_parameters
                with
                | Some index -> List.nth_opt value.type_arguments index
                | None -> None)
              (select signature))
  in
  let application (value : L.application) : L.application =
    { value with
      instance_arguments = arguments (fun signature -> signature.equality) value;
      print_instance_arguments =
        arguments (fun signature -> signature.printer) value }
  in
  let rule (value : L.rule) : L.rule =
    let conclusion : L.application =
      application
        { value.conclusion with
          arguments =
            List.map (Traversal.map_term_applications application)
              value.conclusion.arguments }
    in
    { value with conclusion;
      premises =
        List.map (Traversal.map_premise_applications application)
          value.premises }
  in
  List.map
    (fun (located : L.located_declaration) ->
      let declaration : L.declaration =
        match located.declaration with
        | L.Relation relation ->
            let required : instance_signature =
              StringMap.find relation.name signatures in
            L.Relation
              { relation with equality_parameters = required.equality;
                print_parameters = required.printer;
                rules = List.map rule relation.rules }
        | L.Builtin builtin ->
            let required : instance_signature =
              StringMap.find builtin.name signatures in
            L.Builtin
              { builtin with equality_parameters = required.equality;
                print_parameters = required.printer }
        | declaration -> declaration
      in
      { located with declaration })
    declarations

let terms_in_declaration (located : L.located_declaration) : L.term list =
  match located.declaration with
  | Relation { rules; _ } -> relation_terms rules
  | _ -> []

let type_declaration_region (program : S.spec) (at : region)
    (source : L.type_ref) : region =
  let source_name : string = match source with
    | Name name | Applied (name, _) -> name
    | _ -> unsupported at ("generated definition source is not a named type: " ^ type_code source)
  in
  match List.find_opt
    (fun (definition : S.def) -> match definition.it with
      | TypD (id, _, _, _) -> id.it = source_name
      | _ -> false) program with
  | Some definition -> definition.at
  | None -> unsupported at ("source type declaration " ^ source_name)

let collected_terms (declarations : L.located_declaration list) : L.term list =
  List.concat_map terms_in_declaration declarations

let coercion_declarations (env : env) (program : S.spec)
    (terms : L.term list) : L.located_declaration list =
  let rec from_term (term : L.term) :
      (string * L.type_ref * L.type_ref) list =
    let children : (string * L.type_ref * L.type_ref) list =
      List.concat_map from_term (Traversal.term_children term)
    in
    match term with
    | Coerce (name, source, target, _) -> (name, source, target) :: children
    | _ -> children
  in
  let casts : (string * L.type_ref * L.type_ref) list =
    List.concat_map from_term terms
    (* One definition per name: renaming the type parameters of a generic user
       changes the recorded types but not the name. *)
    |> List.sort_uniq (fun (left, _, _) (right, _, _) -> String.compare left right)
  in
  List.map
    (fun (name, source, target) ->
      let cases : (string * string * int) list =
        match variant_cases env (List.hd program).at source target with
        | Some cases -> cases
        | None -> unsupported (List.hd program).at
            ("coercion source or target is not a variant: " ^ name)
      in
      let at : region = type_declaration_region program (List.hd program).at source in
      let type_parameters : string list =
        List.sort_uniq String.compare
          (type_parameters_in source @ type_parameters_in target)
      in
      { L.declaration = L.Coercion
          { name; source; target; type_parameters; cases }; at })
    casts

let membership_declarations (program : S.spec) (terms : L.term list) :
    L.located_declaration list =
  let rec from_term (term : L.term) :
      (string * L.type_ref * L.type_ref * (string * int) list * bool) list =
    let children : (string * L.type_ref * L.type_ref * (string * int) list * bool) list =
      List.concat_map from_term (Traversal.term_children term)
    in
    match term with
    | MembershipTest (name, source, target, cases, exhaustive, _) ->
        (name, source, target, cases, exhaustive) :: children
    | _ -> children
  in
  List.concat_map from_term terms
  |> List.sort_uniq (fun (left, _, _, _, _) (right, _, _, _, _) -> String.compare left right)
  |> List.map
    (fun (name, source, target, cases, exhaustive) ->
      let at : region = type_declaration_region program (List.hd program).at source in
      let type_parameters : string list =
        List.sort_uniq String.compare
          (type_parameters_in source @ type_parameters_in target)
      in
      { L.declaration = L.Membership
          { name; source; target; type_parameters; cases; exhaustive }; at })

let generated_declarations (env : env) (program : S.spec)
    (declarations : L.located_declaration list) : L.located_declaration list =
  let terms : L.term list = collected_terms declarations in
  coercion_declarations env program terms @ membership_declarations program terms

let translate ?(fresh_rollback = false) (program : S.spec) :
    (L.located_declaration list, Diagnostic.t) result =
  let env : env = build_env program in
  try
    let declarations : L.located_declaration list =
      List.concat_map
         (fun (declaration : S.def) ->
           List.map
             (fun (translated : L.declaration) ->
               { L.declaration = translated; at = declaration.at })
             (translate_declaration env declaration))
         program
    in
    let declarations : L.located_declaration list =
      declarations @ generated_declarations env program declarations
      |> Fresh_state.lower ~rollback:fresh_rollback
      |> Relation_optimizer.prune_helpers
    in
    Ok (equality_parameters declarations)
  with Unsupported_il diagnostic -> Error diagnostic

let translate_all ?(fresh_rollback = false) (program : S.spec) :
    L.located_declaration list * Diagnostic.t list =
  let env : env = build_env program in
  let (declarations, diagnostics) :
      L.located_declaration list * Diagnostic.t list =
    List.fold_left
      (fun (declarations, diagnostics) (declaration : S.def) ->
        try
          let translated : L.located_declaration list = List.map
            (fun (translated : L.declaration) -> { L.declaration = translated; at = declaration.at })
            (translate_declaration env declaration)
          in
          (List.rev_append translated declarations, diagnostics)
        with Unsupported_il diagnostic ->
          (declarations, diagnostic :: diagnostics))
      ([], []) program
  in
  let declarations : L.located_declaration list = List.rev declarations in
  let declarations : L.located_declaration list =
    declarations @ generated_declarations env program declarations
    |> Fresh_state.lower ~rollback:fresh_rollback
    |> Relation_optimizer.prune_helpers
    |> equality_parameters
  in
  (declarations, List.rev diagnostics)
