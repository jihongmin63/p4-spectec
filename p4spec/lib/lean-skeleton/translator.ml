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

let expand_expression_type (env : env) (at : region) (typ : L.type_ref) : L.type_ref =
  let lookup (name : string) : L.type_alias option =
    Option.map
      (fun (alias : alias) ->
        { L.name; type_parameters = alias.type_parameters;
          body = translate_type_with_parameters alias.type_parameters alias.body })
      (StringMap.find_opt name env.aliases)
  in
  expand_type_aliases lookup at [] typ

let primitive_equality_type (typ : L.type_ref) : bool =
  match typ with
  | BuiltinType (("Nat" | "Int" | "Bool" | "String"), []) -> true
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
      premises = []; conclusion = application empty };
    { name = (match iter with List -> "cons" | Opt -> "some"); binders = step_binders;
      premises = body.premises
        @ (match iter with List -> [ L.Holds (application tail_terms) ] | Opt -> []);
      conclusion = application populated }
  ] in
  let helper : L.declaration = L.Relation
    { name; type_parameters;
      argument_types = List.map snd context @ List.map (fun (_, _, typ) -> collection_type typ) vectors;
      rules; notation = None }
  in
  { terms = []; premises = [ L.Holds (application (List.map (fun (_, collection, _) -> collection) vectors)) ];
    binders = []; next = body.next; helpers = body.helpers @ [ helper ] }

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
        | Some (BuiltinFunction parameters) -> (
            match Builtin.translate id.it parameters with
            | Ok _ -> true
            | Error reason -> unsupported exp.at ("builtin call " ^ reason))
        | Some (UnsupportedFunction kind) -> unsupported exp.at (kind ^ " call $" ^ id.it)
        | None -> unsupported exp.at ("unknown function call $" ^ id.it)
      in
      let translate_argument (next : int) (argument : S.arg) : term_result =
        match argument.it with
        | ExpA value -> recurse next value
        | DefA id -> pure_term next (function_reference env functions id)
      in
      let result : terms_result = collect_terms translate_argument next arguments in
      let application : L.application =
        { target; type_arguments = List.map (translate_type_with_parameters type_parameters) type_arguments;
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
  | UpCastE (_, value) when expanded value = L.BuiltinType ("Nat", []) && expanded exp = L.BuiltinType ("Int", []) ->
      unary value (integer value)
  | TupleE [ left; right ] -> binary left right (fun left right -> L.Tuple (left, right))
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
      | _ -> unsupported exp.at "indexing other than a list with a natural index")
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
      if not (primitive_equality_type (numeric_type left)) then
        unsupported exp.at "comparison in term position for a non-primitive type";
      if numeric_type left <> numeric_type right then
        unsupported exp.at "comparison operands with different runtime types";
      let operator : L.comparison = match operator with
        | `EqOp -> L.Eq | `NeOp -> L.Ne | `LtOp -> L.Lt | `LeOp -> L.Le | `GtOp -> L.Gt | `GeOp -> L.Ge
      in
      binary left right (fun left right -> L.Decide (L.Comparison (operator, left, right)))
  | MemE (element, collection) ->
      if not (primitive_equality_type (numeric_type element)) then
        unsupported exp.at "membership in term position for a non-primitive type";
      (match expanded collection with
      | BuiltinType ("List", [ typ ]) when typ = numeric_type element -> ()
      | _ -> unsupported exp.at "membership in a non-list");
      binary element collection (fun element collection -> L.Decide (L.Membership (element, collection)))
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
  | UpCastE _ -> unsupported exp.at ("UpCastE expression " ^ S.Print.string_of_exp exp)
  | SubE _ -> unsupported exp.at ("SubE expression " ^ S.Print.string_of_exp exp)
  | SliceE _ -> unsupported exp.at "SliceE expression (start and length with bounds checks)"
  | UpdE _ -> unsupported exp.at ("UpdE expression " ^ S.Print.string_of_exp exp)
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
  { target = L.Global name; type_arguments; arguments = result.terms }, result

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
    (relation_name : string) (arity : int) (branch : branch) : L.rule * L.declaration list =
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
  let result : terms_result = collect_terms translate_argument 0 branch.arguments in
  let conclusion : L.application =
    { target = L.Global relation_name;
      type_arguments = List.map (fun name -> L.TypeParameter name) type_parameters;
      arguments = result.terms }
  in
  let result : terms_result = List.fold_left
    (fun (result : terms_result) (premise : S.prem) ->
      let translated : terms_result =
        translate_premise env type_parameters functions result.next premise
      in
      { result with premises = result.premises @ translated.premises;
        binders = result.binders @ translated.binders; next = translated.next;
        helpers = result.helpers @ translated.helpers })
    result branch.premises
  in
  let variables : (string * L.type_ref) list =
    List.concat_map variables_in_term
      (conclusion.arguments @ List.concat_map Traversal.premise_terms result.premises)
  in
  { name = branch.name; binders = unique_binders env branch.at (variables @ result.binders);
    premises = result.premises; conclusion }, result.helpers

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

let translate_relation_unrenamed (env : env) (name : string) (type_parameters : string list)
    (argument_types : L.type_ref list) (branches : branch list)
    (notation : L.notation_part list option) : L.declaration list =
  let arity : int = List.length argument_types in
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
          translate_branch env type_parameters name arity
            { branch with name = name_rule }
        in
        (name_rule :: used, rule :: rules, helpers @ emitted))
      ([], [], []) branches
  in
  let rules : L.rule list = List.rev rules in
  L.Relation { name; type_parameters; argument_types; rules; notation } :: helpers

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

let translate_relation (env : env) (name : string) (type_parameters : string list)
    (argument_types : L.type_ref list) (branches : branch list)
    (notation : L.notation_part list option) : L.declaration list =
  rename_relation_declarations env type_parameters
    (translate_relation_unrenamed env name type_parameters argument_types branches notation)

let translate_otherwise_relation (env : env) (name : string)
    (type_parameters : string list) (argument_types : L.type_ref list)
    (branches : branch list) (otherwise : branch) (inputs : Lang.Hints.Input.t)
    (notation : L.notation_part list option) : L.declaration list =
  let regular_name : string = name ^ ":regular" in
  let regular : L.declaration list =
    translate_relation_unrenamed env regular_name type_parameters argument_types branches None
  in
  let public : L.declaration list =
    translate_relation_unrenamed env name type_parameters argument_types [ otherwise ] notation
  in
  let binders : (string * L.type_ref) list =
    List.mapi (fun index typ -> "arg:" ^ string_of_int index, typ) argument_types
  in
  let application : L.application =
    { target = L.Global name;
      type_arguments = List.map (fun name -> L.TypeParameter name) type_parameters;
      arguments = List.map (fun (name, typ) -> L.Variable (name, typ)) binders }
  in
  let wrapper : L.rule =
    { name = "regular"; binders;
      premises = [ L.Holds { application with target = L.Global regular_name } ];
      conclusion = application }
  in
  let guard (rule : L.rule) : L.rule =
    let (arguments, _) : L.term list * L.term list =
      Lang.Hints.Input.split inputs rule.conclusion.arguments
    in
    let (_, output_types) : L.type_ref list * L.type_ref list =
      Lang.Hints.Input.split inputs argument_types
    in
    let outputs : (string * L.type_ref) list =
      List.mapi (fun index typ -> "otherwise:" ^ string_of_int index, typ) output_types
    in
    let negative : L.application =
      { rule.conclusion with target = L.Global regular_name;
        arguments = Lang.Hints.Input.combine inputs arguments
          (List.map (fun (name, typ) -> L.Variable (name, typ)) outputs) }
    in
    { rule with premises = L.NotExists (outputs, negative, otherwise.at) :: rule.premises }
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
  rename_relation_declarations env type_parameters (regular @ public)
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
        unsupported decl.at ("external type declaration " ^ id.it)
    | VarD _ ->
        (* TODO: Translate metavariable declarations. *)
        []
    | ExternRelD (id, _, _, _) ->
        unsupported decl.at ("external relation declaration " ^ id.it)
    | RelD (id, _, _, _, Some otherwise, _)
      when List.mem id.it env.recursive_otherwise ->
        unsupported otherwise.at ("otherwise of recursive definition " ^ id.it)
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
        | None -> translate_relation env id.it [] argument_types branches (Some notation)
        | Some group ->
            let otherwise : branch = branch_of_rule (snd group.it) in
            translate_otherwise_relation env id.it [] argument_types branches otherwise inputs
              (Some notation))
    | ExternDecD (id, _, _, _, _) ->
        unsupported decl.at ("external function declaration " ^ id.it)
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
        (match Builtin.translate id.it type_parameters with
        | Ok expected ->
            if parameters <> expected.parameters || result <> expected.result then
              unsupported decl.at
                ("builtin function " ^ id.it
               ^ " because its signature differs from the SpecTec implementation");
            [ L.Builtin { expected with name = "$" ^ expected.name } ]
        (* A rule-less relation would claim that the builtin has no result. *)
        | Error reason -> unsupported decl.at ("builtin function " ^ reason))
    | TableDecD (id, _, _, _, _) ->
        unsupported decl.at ("table declaration " ^ id.it)
    | FuncDecD (id, _, _, _, _, Some otherwise, _)
      when List.mem ("$" ^ id.it) env.recursive_otherwise ->
        unsupported otherwise.at ("otherwise of recursive definition $" ^ id.it)
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
      | L.Structure _ -> ()
      | L.Builtin _ -> ())
    declarations;
  declarations

let translate (program : S.spec) : (L.located_declaration list, Diagnostic.t) result =
  let env : env = build_env program in
  try
    Ok
      (List.concat_map
         (fun (declaration : S.def) ->
           List.map
             (fun (translated : L.declaration) ->
               { L.declaration = translated; at = declaration.at })
             (translate_declaration env declaration))
         program)
  with Unsupported_il diagnostic -> Error diagnostic

let translate_all (program : S.spec) :
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
  (List.rev declarations, List.rev diagnostics)
