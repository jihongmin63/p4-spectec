(** Lower the interpreter's directional AL clauses to the shared Eval language.
    This module never turns absence of a relation proof into execution failure. *)
module S = Ast.SpecTec
module A = Lang.Al
module L = Ast.Lean
module E = Execution_ir
module M = Translator.StringMap
open Util.Source

let ( let* ) = Result.bind
let ident = Printer.print_identifier

type compiled_clause = {
  parameters : string;
  body : string;
  equality_parameters : string list;
  value_terms : L.term list;
  calls : Order.StringSet.t;
}

let modes source =
  let table = Hashtbl.create 32 in
  List.iter (fun (def : S.def) -> match def.it with
    | RelD (id, _, inputs, _, _, _) | ExternRelD (id, _, inputs, _) ->
        Hashtbl.replace table id.it inputs
    | FuncDecD (id, _, params, _, _, _, _)
    | ExternDecD (id, _, params, _, _)
    | BuiltinDecD (id, _, params, _, _)
    | TableDecD (id, params, _, _, _) ->
        Hashtbl.replace table ("$" ^ id.it) (List.init (List.length params) Fun.id)
    | _ -> ()) source;
  table

let normalized (def : S.def) (analyzed : A.def) : S.def =
  match analyzed.it with
  | A.RelD (id, notation, inputs, groups, otherwise, hints) ->
      let group (name, (_, patterns, match_prems), paths) at =
        let rules = List.map (fun (rid, prems, outputs) ->
          (rid, Domain.Mixfix.fill (Domain.Mixfix.to_mixop notation.it)
            (Lang.Hints.Input.combine inputs patterns outputs), match_prems @ prems) $ at) paths in
        (name, rules) $ at in
      let groups = List.map (fun g -> group g.it g.at) groups in
      let groups = groups @ (match otherwise with
        | None -> []
        | Some g -> let name, m, path = g.it in [group (name, m, [path]) g.at]) in
      S.RelD (id, notation, inputs, groups, None, hints) $ def.at
  | A.FuncDecD (id, ts, ps, result, clauses, otherwise, hints) ->
      S.FuncDecD (id, ts, ps, result,
        clauses @ Option.to_list otherwise, None, hints) $ def.at
  | _ -> def

let rec call_type bound = function
  | L.RelationType (args, result) ->
      "(" ^ String.concat " → " (List.map (call_type bound) args @ ["(Call " ^ call_type bound result ^ ")"]) ^ ")"
  | typ -> Printer.print_type bound typ

let compile ~executable env (signatures : E.signature M.t) (signature : E.signature) (rule : L.rule) at =
  let rule = if signature.name = "$partition_"
    && (match M.find_opt "partition_" env.Translator.functions with Some (Translator.BuiltinRelation _) -> true | _ -> false) then
    match rule.conclusion.arguments with
    | _ :: count :: _ -> {rule with premises = L.Prop (L.Comparison (L.Le, count,
        L.Number ("4611686018427387903", L.BuiltinType ("Nat", [])))) :: rule.premises}
    | _ -> rule
    else rule in
  let bound_types = signature.parameters @ List.map fst rule.binders in
  let fresh_index = ref 0 in
  let fresh () = incr fresh_index; ident ("exec:" ^ string_of_int !fresh_index) in
  let term = Printer.print_term bound_types in
  let prop = Printer.print_prop bound_types in
  let vars t = List.map fst (Translator.variables_in_term t) in
  let equality_parameters = ref [] in
  let value_terms = ref [] in
  let calls = ref Order.StringSet.empty in
  let retain_values terms = value_terms := terms @ !value_terms in
  let need_equality terms =
    if executable then
      let types = List.concat_map Translator.variables_in_term terms |> List.map snd in
      equality_parameters := Translator.required_type_parameters signature.parameters types
        @ !equality_parameters in
  let rec prop_vars = function
    | L.Forall (n, _, body) -> List.filter ((<>) n) (prop_vars body)
    | L.And (p,q) | L.Or (p,q) | L.Implies (p,q) | L.Iff (p,q) -> prop_vars p @ prop_vars q
    | L.Not p -> prop_vars p
    | p -> List.concat_map vars (Traversal.prop_terms p) in
  let ground bound t = List.for_all (fun n -> List.mem n bound) (vars t) in
  let ensure bound t = if not (ground bound t) then
    Translator.unsupported at ("unbound execution value " ^ String.concat ", " (List.filter (fun n -> not (List.mem n bound)) (vars t))
      ^ " in " ^ signature.name ^ "/" ^ rule.name) in
  let guard condition continuation =
    "(.bind (.guard (" ^ condition ^ ")) (fun (_ : Unit) => " ^ continuation ^ "))" in
  let call typ request =
    if executable then "(.call (" ^ request ^ "))"
    else "(.call ⟨" ^ call_type bound_types typ ^ ", " ^ request ^ "⟩)" in
  let value t = match t with
    | L.FunctionReference (L.Global n) ->
        if M.mem n signatures then "Call." ^ ident n
        else Translator.unsupported at ("function execution reference " ^ n)
    | L.FunctionReference (L.Local n) -> ident n
    | _ -> term t in
  let rec patterns bound pats actuals next = match pats, actuals with
    | [], [] -> next bound
    | p :: ps, a :: rest -> pattern bound p a (fun bound -> patterns bound ps rest next)
    | _ -> assert false
  and pattern bound pat actual next = match pat with
    | L.Typed (p, _) -> pattern bound p actual next
    | L.Variable (n, typ) when not (List.mem n bound) ->
        "(let " ^ ident n ^ " : " ^ call_type bound_types typ ^ " := " ^ actual
        ^ "; " ^ next (n :: bound) ^ ")"
    | L.Variable _ | L.Boolean _ | L.Number _ | L.Text _ ->
        ensure bound pat; need_equality [pat]; guard (actual ^ " = " ^ value pat) (next bound)
    | L.Tuple (left, right) ->
        patterns bound [left; right] ["(" ^ actual ^ ").1"; "(" ^ actual ^ ").2"] next
    | L.StructureLiteral (_, fields) ->
        patterns bound (List.map snd fields)
          (List.map (fun (n, _) -> "(" ^ actual ^ ")." ^ ident n) fields) next
    | L.ListLiteral [] ->
        "(match " ^ actual ^ " with | [] => " ^ next bound ^ " | _ :: _ => .unmatch)"
    | L.ListLiteral (head :: tail) -> pattern bound (L.Binary ("::", head, L.ListLiteral tail)) actual next
    | L.Binary ("++", affix, (L.Variable (n, L.BuiltinType ("String", [])) as result))
        when ground bound affix && not (List.mem n bound) ->
        let length = "(" ^ actual ^ ").utf8ByteSize - (" ^ value affix ^ ").utf8ByteSize" in
        let start = "(" ^ value affix ^ ").utf8ByteSize" in
        guard ("_root_.specTecTextSliceValid " ^ actual ^ " " ^ start ^ " (" ^ length ^ ")")
          (pattern bound result ("(_root_.specTecTextSlice " ^ actual ^ " " ^ start ^ " (" ^ length ^ "))")
            (fun bound -> guard (actual ^ " = " ^ value pat) (next bound)))
    | L.Binary ("++", (L.Variable (n, L.BuiltinType ("String", [])) as result), affix)
        when ground bound affix && not (List.mem n bound) ->
        let length = "(" ^ actual ^ ").utf8ByteSize - (" ^ value affix ^ ").utf8ByteSize" in
        guard ("_root_.specTecTextSliceValid " ^ actual ^ " 0 (" ^ length ^ ")")
          (pattern bound result ("(_root_.specTecTextSlice " ^ actual ^ " 0 (" ^ length ^ "))")
            (fun bound -> guard (actual ^ " = " ^ value pat) (next bound)))
    | L.Binary ("::", head, tail) ->
        let h, t = fresh (), fresh () in
        "(match " ^ actual ^ " with | " ^ h ^ " :: " ^ t ^ " => "
        ^ patterns bound [head; tail] [h; t] next ^ " | [] => .unmatch)"
    | L.Native ("Option.none", []) ->
        "(match " ^ actual ^ " with | none => " ^ next bound ^ " | some _ => .unmatch)"
    | L.Native ("Option.some", [p]) ->
        let x = fresh () in "(match " ^ actual ^ " with | some " ^ x ^ " => "
        ^ pattern bound p x next ^ " | none => .unmatch)"
    | L.Constructor (reference, args) ->
        let xs = List.map (fun _ -> fresh ()) args in
        let exhaustive = match M.find_opt reference.type_name env.Translator.constructors with
          | Some v -> List.length v.cases = 1 | None -> false in
        "(match " ^ actual ^ " with | ." ^ ident reference.constructor_name ^ " "
        ^ String.concat " " xs ^ " => " ^ patterns bound args xs next
        ^ (if exhaustive then "" else " | _ => .unmatch") ^ ")"
    | _ when ground bound pat ->
        need_equality [pat]; guard (actual ^ " = " ^ value pat) (next bound)
    | _ -> Translator.unsupported at ("execution pattern in " ^ signature.name ^ "/" ^ rule.name)
  in
  let request bound (app : L.application) =
    let input_mode, output_types = match app.target with
      | L.Global name ->
          (match M.find_opt name signatures with
          | Some s -> s.inputs, List.map (Translator.substitute_type_parameters
              (List.combine s.parameters app.type_arguments)) (E.output_types s)
          | None -> Translator.unsupported at ("execution call " ^ name))
      | L.Local name ->
          (match List.assoc_opt name rule.binders with
          | Some (L.RelationType (args, output)) -> List.init (List.length args) Fun.id, [output]
          | _ -> Translator.unsupported at ("local execution call " ^ name)) in
    let inputs, outputs = Lang.Hints.Input.split input_mode app.arguments in
    List.iter (ensure bound) inputs;
    retain_values inputs;
    let head = match app.target with
      | L.Global n -> calls := Order.StringSet.add n !calls; "Call." ^ ident n
      | L.Local n -> ident n in
    let type_args = List.map (Printer.print_type bound_types) app.type_arguments in
    String.concat " " (head :: type_args @ List.map value inputs), outputs, E.tuple_type output_types in
  let rec premises bound = function
    | [] ->
        let outputs = snd (E.split signature rule.conclusion.arguments) in
        List.iter (ensure bound) outputs;
        retain_values outputs;
        "(.pure (" ^ term (L.Typed (E.tuple_term outputs, E.tuple_type (E.output_types signature))) ^ "))"
    | L.Holds app :: rest ->
        let request, outputs, typ = request bound app in
        let actual = fresh () in
        (* Project by output count; this also handles a single tuple-valued output. *)
        let rec projections actual = function
          | [] -> [] | [_] -> [actual]
          | _ :: rest -> ("(" ^ actual ^ ").1") :: projections ("(" ^ actual ^ ").2") rest in
        "(.bind " ^ call typ request ^ " (fun (" ^ actual ^ " : "
        ^ call_type bound_types typ ^ ") => "
        ^ patterns bound outputs (projections actual outputs) (fun bound -> premises bound rest) ^ "))"
    | L.NotHolds (app, _) :: rest ->
        let req, _, typ = request bound app in
        "(.bind (.notHold " ^ call typ req ^ ") (fun (_ : Unit) => " ^ premises bound rest ^ "))"
    | L.Prop (L.Comparison (L.Eq, pattern_, rhs)) :: rest when ground bound rhs ->
        retain_values [rhs];
        pattern bound pattern_ (value rhs) (fun bound -> premises bound rest)
    | L.Prop (L.Comparison (L.Eq, lhs, pattern_)) :: rest when ground bound lhs ->
        retain_values [lhs];
        pattern bound pattern_ (value lhs) (fun bound -> premises bound rest)
    | L.Prop (L.Iff (L.IsTrue (L.Variable (n, typ)), condition)) :: rest when not (List.mem n bound) ->
        need_equality (Traversal.prop_terms condition);
        let vars = prop_vars condition in
        if not (List.for_all (fun n -> List.mem n bound) vars) then Translator.unsupported at ("unbound builtin condition " ^ signature.name);
        "(.orElse (let " ^ ident n ^ " : " ^ call_type bound_types typ ^ " := true; "
        ^ guard (prop condition) (premises (n :: bound) rest)
        ^ ") (fun () => (let " ^ ident n ^ " : " ^ call_type bound_types typ ^ " := false; "
        ^ guard ("¬ (" ^ prop condition ^ ")") (premises (n :: bound) rest) ^ ")))"
    | (L.Prop condition | L.RuntimeCheck (condition, _)) as check :: rest ->
        need_equality (Traversal.prop_terms condition);
        let variables = prop_vars condition in
        if not (List.for_all (fun n -> List.mem n bound) variables) then
          Translator.unsupported at ("unbound execution condition in " ^ signature.name ^ "/" ^ rule.name);
        (match check with
        | L.RuntimeCheck (_, message) ->
            "(.bind (SpecTecExecution." ^ (if executable then "ExecutableAction." else "") ^ "require (" ^ prop condition ^ ") "
            ^ term (L.Text message) ^ ") (fun (_ : Unit) => " ^ premises bound rest ^ "))"
        | _ -> guard (prop condition) (premises bound rest))
  in
  let inputs = fst (E.split signature rule.conclusion.arguments) in
  let args = List.mapi (fun i _ -> "input" ^ string_of_int i) inputs in
  let parameters = List.map2 (fun name typ -> "(" ^ name ^ " : " ^ call_type bound_types typ ^ ")") args (E.input_types signature) in
  let body = patterns [] inputs args (fun bound -> premises bound rule.premises) in
  { parameters = String.concat " " parameters; body;
    equality_parameters = !equality_parameters;
    value_terms = !value_terms; calls = !calls }

(* Executable guards need equality instances that relational premises alone
   did not require. Collect them from emitted tests, then propagate to callers
   with the existing instance analysis before printing request constructors. *)
let executable_equalities ~executable compiled declarations =
  if not executable then declarations else
  List.map (fun (d : L.located_declaration) -> match d.declaration with
    | L.Relation r ->
        let required = List.concat_map (fun (rule : L.rule) ->
          match Hashtbl.find_opt compiled (r.name, rule.name) with
          | Some clause -> clause.equality_parameters | None -> []) r.rules in
        {d with declaration = L.Relation {r with equality_parameters =
          List.filter (fun p -> List.mem p r.equality_parameters || List.mem p required) r.type_parameters}}
    | _ -> d) declarations
  |> Translator.equality_parameters

let signature env external_names = function
  | L.Relation r ->
      let inputs = match Hashtbl.find_opt env.Translator.input_modes r.name with
        | Some mode -> mode
        | None -> List.init (max 0 (List.length r.argument_types - 1)) Fun.id in
      Some {E.name = r.name; parameters = r.type_parameters; arguments = r.argument_types;
        inputs; external_ = List.mem r.name external_names}
  | _ -> None

let external_names source = List.filter_map (fun (d : S.def) -> match d.it with
  | ExternRelD (id, _, _, _) -> Some id.it
  | ExternDecD (id, _, _, _, _) -> Some ("$" ^ id.it)
  | _ -> None) source

let signatures env external_names declarations =
  List.filter_map (signature env external_names) declarations
  |> List.fold_left (fun m s -> M.add s.E.name s m) M.empty

let compile_declaration ~executable env signatures compiled (d : L.located_declaration) =
  match d.declaration with
  | L.Relation r when not (M.find r.name signatures).E.external_ ->
      List.iter (fun (rule : L.rule) -> Hashtbl.replace compiled (r.name, rule.L.name)
        (compile ~executable env signatures (M.find r.name signatures) rule d.at)) r.rules
  | _ -> ()

let declarations source ~keep_going =
  let env = { (Translator.build_env source) with ordered = true; input_modes = modes source } in
  let analyzed = Pass.algo_defs source in
  let declarations, diagnostics = List.fold_left (fun (decls, ds) ((def : S.def), analyzed) ->
    try
      let normalized = match def.it, analyzed with
        | S.TableDecD _, _ -> def
        | _, Ok analyzed -> normalized def analyzed
        | _, Error d -> raise (Translator.Unsupported_il d) in
      let emitted = Translator.translate_declaration env normalized
        |> List.map (fun declaration -> {L.declaration; at = def.at}) in
      decls @ emitted, ds
    with
    | Translator.Unsupported_il d ->
        if keep_going then decls, ds @ [d] else raise (Translator.Unsupported_il d)) ([], []) (List.combine source analyzed) in
  env, Translator.equality_parameters
    (declarations @ Translator.generated_declarations env source declarations), diagnostics

let emit ~executable source env ordered compiled =
  let declarations = List.concat_map Printer.declarations_in_group ordered in
  let relations = List.filter (function L.Relation _ -> true | _ -> false) declarations in
  let signatures = signatures env (external_names source) relations in
  (* Lean's runtime reserves constructor tags above 243. Such requests can
     still occur in kernel definitions, but cannot be allocated by native code.
     Nullary constructors are scalar values and do not have this restriction. *)
  let kernel_only_calls = List.mapi (fun index -> function
    | L.Relation r when index > 243 &&
        (E.input_types (M.find r.name signatures) <> [] ||
         r.equality_parameters <> [] || r.print_parameters <> []) -> Some r.name
    | _ -> None) relations
    |> List.filter_map Fun.id |> Order.StringSet.of_list in
  let kernel_only_data = List.fold_left (fun types -> function
    | L.Datatype d ->
        let constructors = List.mapi (fun index (c : L.constructor) ->
          if index > 243 && c.arguments <> [] then Some c.name else None) d.constructors
          |> List.filter_map Fun.id |> Order.StringSet.of_list in
        M.add d.name constructors types
    | _ -> types) M.empty declarations in
  let rec kernel_only_term term =
    (match term with
    | L.Constructor (reference, _) ->
        (match M.find_opt reference.type_name kernel_only_data with
        | Some constructors -> Order.StringSet.mem reference.constructor_name constructors
        | None -> false)
    | _ -> false)
    || List.exists kernel_only_term (Traversal.term_children term) in
  let kernel_only_clause name (rule : L.rule) =
    not executable && not (M.find name signatures).external_ &&
    let clause = Hashtbl.find compiled (name, rule.name) in
      (not (Order.StringSet.is_empty (Order.StringSet.inter kernel_only_calls
        (Order.StringSet.union clause.calls
          (Order.unions (List.map Order.term_references clause.value_terms)))))
      || List.exists kernel_only_term clause.value_terms) in
  let declaration kernel_only = if kernel_only then "noncomputable def " else "def " in
  let kernel_only_body = List.exists (function
    | L.Relation r -> List.exists (kernel_only_clause r.name) r.rules
    | _ -> false) relations in
  let fresh_builtins = List.filter_map (fun (d : S.def) -> match d.it with
    | S.BuiltinDecD (id, _, _, _, _) when id.it = "fresh_typeId" -> Some ("$" ^ id.it)
    | _ -> None) source in
  let data =List.filter (fun group -> not (List.exists (function L.Relation _ -> true | _ -> false)
    (Printer.declarations_in_group group))) ordered in
  let base = Printer.print ~ordered_externs:true data in
  (* Restore call metadata removed by filtering the raw inductive declarations. *)
  Printer.call_type_parameters := List.fold_left (fun m -> function
    | L.Relation r -> Order.StringMap.add r.name r.type_parameters m
    | _ -> m) !(Printer.call_type_parameters) relations;
  let type_dependencies = List.filter_map (function
    | L.Datatype d -> Some (d.name, List.concat_map (fun (c : L.constructor) -> c.arguments) d.constructors)
    | L.Structure {name; fields} -> Some (name, List.map snd fields)
    | L.TypeAlias d -> Some (d.name, [d.body])
    | _ -> None) declarations in
  let extern_names = List.fold_left (fun names -> function
    | L.ExternType n -> Order.StringSet.add n names | _ -> names) Order.StringSet.empty declarations in
  let uses_extern names typ = not (Order.StringSet.is_empty
    (Order.StringSet.inter names (Order.type_references typ))) in
  let rec close names =
    let next = List.fold_left (fun names (n, types) ->
      if List.exists (uses_extern names) types then Order.StringSet.add n names else names) names type_dependencies in
    if Order.StringSet.equal next names then names else close next in
  let extern_names = close extern_names in
  let call_extern_types = List.exists (function L.Relation r ->
    List.exists (uses_extern extern_names) r.argument_types | _ -> false) relations in
  let aborting_builtins = List.filter_map (fun (d : S.def) -> match d.it with
    | S.BuiltinDecD (id, _, _, _, _) when List.mem id.it
        ["text_to_int"; "strip_prefix"; "strip_suffix"; "split_text";
         "adds_map"; "bitacc"; "bitacc_replace"; "partition_"; "print_"] -> Some ("$" ^ id.it)
    | _ -> None) source in
  let tables = List.filter_map (fun (d : S.def) -> match d.it with
    | S.TableDecD (id, _, _, _, _) -> Some ("$" ^ id.it)
    | _ -> None) source in
  (* As in the SL interpreter, a failed builtin or a table without an
     applicable row aborts rather than letting the caller select fallback. *)
  let abort_tail name =
    if List.mem name aborting_builtins then
      [".abort \"builtin " ^ name ^ " failed\""]
    else if List.mem name tables then
      [".abort \"table " ^ name ^ " did not return a value\""]
    else [] in
  let groups = ref [] in
  let add s = groups := !groups @ [s] in
  let instances eq print = String.concat ""
    (List.map (fun n -> " [_root_.DecidableEq " ^ ident n ^ "]") eq
     @ List.map (fun n -> " [_root_.SpecTecPrint " ^ ident n ^ "]") print) in
  let type_binders names = String.concat "" (List.map (fun n -> " (" ^ ident n ^ " : Type)") names) in
  let args s = List.mapi (fun i typ -> "input" ^ string_of_int i, typ) (E.input_types s) in
  let arg_binders bound args = String.concat "" (List.map (fun (n,t) -> " (" ^ n ^ " : " ^ call_type bound t ^ ")") args) in
  let instance_patterns eq print = List.map (fun n -> "eq_" ^ n) eq @ List.map (fun n -> "print_" ^ n) print in
  let restore_instances eq print =
    String.concat " " (List.map (fun n -> "letI : _root_.DecidableEq " ^ ident n ^ " := eq_" ^ n ^ ";") eq
      @ List.map (fun n -> "letI : _root_.SpecTecPrint " ^ ident n ^ " := print_" ^ n ^ ";") print) in
  let arms ?(only_extern = false) ?(typed = false) f = List.filter_map (function L.Relation r ->
    let s = M.find r.name signatures in
    if only_extern && not s.external_ then None else Some ((if typed then "  | @Call." else "  | ⟨_, @Call.") ^ ident r.name ^ " " ^ String.concat " "
      ((if call_extern_types then ["_"] else []) @ List.map ident r.type_parameters @ instance_patterns r.equality_parameters r.print_parameters @ List.map fst (args s))
      ^ (if typed then " => " else "⟩ => ") ^ restore_instances r.equality_parameters r.print_parameters ^ " " ^ f s r.name)
    | _ -> None) relations in
  (* Even a singleton polymorphic call family needs an index, not a promoted
     parameter: dispatch patterns bind its result type. *)
  add ("set_option inductive.autoPromoteIndices false in\ninductive Call : Type → Type 1 where\n" ^ String.concat "\n" (List.filter_map (function
    | L.Relation r -> let s = M.find r.name signatures in
      Some ("  | " ^ ident r.name ^ type_binders r.type_parameters
        ^ instances r.equality_parameters r.print_parameters ^ arg_binders r.type_parameters (args s) ^ " : Call " ^ call_type r.type_parameters (E.tuple_type (E.output_types s)))
    | _ -> None) relations));
  add "abbrev Request := Sigma Call";
  List.iter (function L.Relation r ->
    let s = M.find r.name signatures in
    if not s.external_ && not (List.mem r.name fresh_builtins) then (
      let clause_names = List.mapi (fun i _ -> r.name ^ ":clause:" ^ string_of_int i) r.rules in
      let clauses = List.map ident clause_names in
      let shared = type_binders r.type_parameters ^ instances r.equality_parameters r.print_parameters in
      let output = call_type r.type_parameters (E.tuple_type (E.output_types s)) in
      let applied_args = String.concat " " (List.map ident r.type_parameters @ List.map fst (args s)) in
      List.iter2 (fun name (rule : L.rule) ->
        let clause = Hashtbl.find compiled (r.name, rule.L.name) in
        let params, body = clause.parameters, clause.body in
        if executable then (
          add ("def " ^ ident (name ^ ":exec") ^ shared ^ " " ^ params
            ^ " : SpecTecExecution.ExecutableAction Call " ^ output ^ " :=\n  " ^ body);
          add ("def " ^ ident name ^ shared ^ " " ^ params
            ^ " : SpecTecExecution.Action.{1} Request :=\n  ("
            ^ ident (name ^ ":exec") ^ " " ^ applied_args ^ ").erase"))
        else add (declaration (kernel_only_clause r.name rule) ^ ident name ^ shared ^ " " ^ params ^ " : SpecTecExecution.Action.{1} Request :=\n  " ^ body)) clause_names r.rules;
      let applied = List.map (fun name -> "(" ^ name ^ " " ^ String.concat " " (List.map ident r.type_parameters)
        ^ " " ^ String.concat " " (List.map fst (args s)) ^ ")") clauses in
      (* Inputs have already been applied to these clause actions. *)
      add (declaration (List.exists (kernel_only_clause r.name) r.rules) ^ ident (r.name ^ "_clauses") ^ shared ^ arg_binders r.type_parameters (args s)
        ^ " : List (SpecTecExecution.Action.{1} Request) :=\n  ["
        ^ String.concat ", " (applied @ abort_tail r.name) ^ "]");
      if executable then
        add ("def " ^ ident (r.name ^ "_clauses:exec") ^ shared ^ arg_binders r.type_parameters (args s)
          ^ " : List (SpecTecExecution.ExecutableAction Call " ^ output ^ ") :=\n  ["
          ^ String.concat ", " (List.map (fun name ->
              ident (name ^ ":exec") ^ " " ^ applied_args) clause_names
              @ abort_tail r.name) ^ "]"))
    | _ -> ()) relations;
  (* Externs expose their unconditional inductive API. Their body chooses
     exactly the typed successes allowed by that API. *)
  let extern_application s arguments =
    String.concat " " (ident s.E.name
      :: List.map (fun n -> "(" ^ ident n ^ " := " ^ ident n ^ ")") s.parameters
      @ arguments) in
  List.iter (function L.Relation r ->
    let s = M.find r.name signatures in
    if s.external_ then (
      let all = List.mapi (fun i typ -> "arg" ^ string_of_int i, typ) s.arguments in
      let parameters = String.concat "" (List.map (fun n -> " {" ^ ident n ^ " : Type}") s.parameters)
        ^ instances r.equality_parameters r.print_parameters in
      let signature = String.concat " → " (List.map (call_type s.parameters) s.arguments @ ["Prop"]) in
      let conclusion = extern_application s (List.map fst all) in
      add ("inductive " ^ ident r.name ^ parameters ^ " : " ^ signature ^ " where\n  | allowed : "
        ^ (if all = [] then "" else "∀" ^ arg_binders s.parameters all ^ ", ") ^ conclusion
        ^ (match r.notation with None -> "" | Some n -> "\n\n" ^ Printer.print_notation r.name n)))
    | _ -> ()) relations;
  let extern_choose s =
    let outputs = E.output_types s in
    let output_names = List.mapi (fun i _ -> "output" ^ string_of_int i) outputs in
    let arguments = Lang.Hints.Input.combine s.inputs (List.map fst (args s)) output_names in
    let binder = match output_names with
      | [] -> "_"
      | [name] -> name
      | names -> "(" ^ String.concat ", " names ^ ")" in
    ".choose " ^ call_type s.parameters (E.tuple_type outputs) ^ " (fun " ^ binder
      ^ " => " ^ extern_application s arguments ^ ")" in
  if executable then (
    add ("def specTecExecutableBody {α : Type} (request : Call α) : SpecTecExecution.ExecutableAction Call α :=\n"
    ^ (if relations = [] then "  nomatch request" else "  match request with\n" ^ String.concat "\n" (arms ~typed:true (fun s name ->
        if s.E.external_ then extern_choose s
        else if List.mem name fresh_builtins then ".freshId" else
        "SpecTecExecution.ExecutableAction.tryClauses (" ^ ident (name ^ "_clauses:exec") ^ " "
          ^ String.concat " " (List.map ident s.parameters @ List.map fst (args s)) ^ ")"))));
    add "def specTecExecutableProgram : SpecTecExecution.ExecutableProgram Call :=\n  ⟨fun request => specTecExecutableBody request⟩";
    add "def Body (request : Request) : SpecTecExecution.Action.{1} Request :=\n  (specTecExecutableBody request.2).erase")
  else (
  add (declaration kernel_only_body ^ "Body (request : Request) : SpecTecExecution.Action.{1} Request :=\n"
    ^ (if relations = [] then "  nomatch request.2" else "  match request with\n" ^ String.concat "\n" (arms (fun s name ->
      if s.E.external_ then extern_choose s
      else if List.mem name fresh_builtins then ".freshId" else
      "SpecTecExecution.tryClauses (" ^ ident (name ^ "_clauses") ^ " "
        ^ String.concat " " (List.map ident s.parameters @ List.map fst (args s)) ^ ")")))));
  List.iter (function L.Relation r ->
    let s = M.find r.name signatures in
    if not s.external_ then (
    let all = List.mapi (fun i typ -> "arg" ^ string_of_int i, typ) s.arguments in
    let input, output = E.split s all in
    let request = "Call." ^ ident r.name ^ " "
      ^ String.concat " " (List.map ident s.parameters
        @ List.map fst input) in
    let output_term = List.map (fun (n,t) -> L.Variable (n,t)) output |> E.tuple_term |> Printer.print_term r.type_parameters in
    add ("def " ^ ident r.name ^ type_binders r.type_parameters ^ instances r.equality_parameters r.print_parameters
      ^ arg_binders r.type_parameters all ^ " : Prop :=\n  ∃ finalSupply : Nat, SpecTecExecution.Eval Body (.call ⟨" ^ call_type r.type_parameters (E.tuple_type (E.output_types s)) ^ ", " ^ request
      ^ "⟩) 0 (.success (.of (" ^ output_term ^ "))) finalSupply"
      ^ (match r.notation with None -> "" | Some n -> "\n\n" ^ Printer.print_notation r.name n)))
    | _ -> ()) relations;
  let first_marker = List.length data in
  let extras = List.mapi (fun i text -> let n = string_of_int (first_marker+i) in
    "-- SpecTecModule:decl:begin:" ^ n ^ "\n" ^ text ^ "\n-- SpecTecModule:decl:end:" ^ n) !groups in
  let suffix = "end SpecTec" in
  assert (String.ends_with ~suffix base);
  Execution_support.source
  ^ (if executable then "\n" ^ Execution_support.run_eval_source else "")
  ^ "\n\nset_option maxHeartbeats 4000000\nset_option maxRecDepth 4096\n\n"
  ^ String.sub base 0 (String.length base - String.length suffix)
  ^ String.concat "\n\n" extras ^ "\n\nend SpecTec"

let transpile_all ?(executable = false) source =
  let env, declarations, diagnostics = declarations source ~keep_going:true in
  let signatures = signatures env (external_names source)
    (List.map (fun d -> d.L.declaration) declarations) in
  Printer.configure (List.map (fun d -> d.L.declaration) declarations);
  (* Prune callers of untranslated declarations before compiling clauses, so
     their diagnostics name the missing dependency, not an execution call. *)
  let retained, errors_dependency = Order.order_all declarations in
  let retained = List.concat_map Printer.declarations_in_group retained
    |> List.map Order.defined_name |> Order.StringSet.of_list in
  let compiled = Hashtbl.create 32 in
  let declarations, failed, errors = List.fold_left (fun (ds, failed, errors) d ->
    if not (Order.StringSet.mem (Order.defined_name d.L.declaration) retained) then ds, failed, errors
    else try compile_declaration ~executable env signatures compiled d; ds @ [d], failed, errors
    with Translator.Unsupported_il error -> ds, d.L.at :: failed, errors @ [error])
    ([], [], []) declarations in
  (* Helpers share the region of their IL definition; drop them with it. *)
  let declarations = List.filter (fun d -> not (List.mem d.L.at failed)) declarations in
  let declarations = executable_equalities ~executable compiled declarations in
  let ordered, errors_order = Order.order_all declarations in
  emit ~executable source env ordered compiled, diagnostics @ errors_dependency @ errors @ errors_order

let transpile ?(executable = false) source =
  try
    let env, declarations, _ = declarations source ~keep_going:false in
    let* ordered = Order.order declarations in
    let signatures = signatures env (external_names source)
      (List.map (fun d -> d.L.declaration) declarations) in
    Printer.configure (List.map (fun d -> d.L.declaration) declarations);
    let compiled = Hashtbl.create 32 in
    List.iter (compile_declaration ~executable env signatures compiled) declarations;
    let* ordered = if executable then
      Order.order (executable_equalities ~executable compiled declarations)
      else Ok ordered in
    Ok (emit ~executable source env ordered compiled)
  with Translator.Unsupported_il d -> Error d
