module L = Ast.Lean
module Names = Set.Make (String)

let union_map f values =
  List.fold_left (fun names value -> Names.union names (f value)) Names.empty values

let reference_names = function
  | L.Local name -> Names.singleton name
  | L.Global _ -> Names.empty

(* Scope matters when hiding intermediate witnesses inside a shared prefix. *)
let rec term_names = function
  | L.Variable (name, _) -> Names.singleton name
  | L.FunctionReference reference -> reference_names reference.target
  | L.Lambda (name, _, body) -> Names.remove name (term_names body)
  | L.Decide (_, prop) -> prop_names prop
  | L.Apply application -> application_names application
  | term -> union_map term_names (Traversal.term_children term)

and prop_names = function
  | L.Forall (name, _, body) -> Names.remove name (prop_names body)
  | L.Not body -> prop_names body
  | L.And (left, right) | L.Or (left, right)
  | L.Implies (left, right) | L.Iff (left, right) ->
      Names.union (prop_names left) (prop_names right)
  | prop -> union_map term_names (Traversal.prop_terms prop)

and application_names (application : L.application) =
  Names.union (reference_names application.target)
    (union_map term_names application.arguments)

let premise_names = function
  | L.Holds application | L.NotHolds (application, _) -> application_names application
  | L.NotExists (binders, application, _) ->
      List.fold_left (fun names (name, _) -> Names.remove name names)
        (application_names application) binders
  | L.Prop prop -> prop_names prop

(* Failure rules are evaluated before the rest of the source clause. Their
   copied binders must not require witnesses used only by later premises. *)
let trim_failure_binders (rule : L.rule) =
  let used = Names.union (application_names rule.conclusion)
    (union_map premise_names rule.premises) in
  { rule with binders = List.filter (fun (name, _) -> Names.mem name used) rule.binders }

let rec term_weight term =
  let own = match term with
    | L.Text text -> 1 + String.length text / 8
    | L.Variable (name, _) -> 1 + String.length name / 8
    | _ -> 1 in
  own + List.fold_left (fun total term -> total + term_weight term)
    0 (Traversal.term_children term)

let premise_weight premise =
  let own = match premise with
    | L.Holds { target = L.Global name; _ }
    | L.NotHolds ({ target = L.Global name; _ }, _) -> 4 + String.length name / 8
    | _ -> 3 in
  own + List.fold_left (fun total term -> total + term_weight term)
    0 (Traversal.premise_terms premise)

type candidate = {
  prefix : L.premise list;
  mutable uses : (int * L.rule * L.premise list) list;
}

let best_prefix (rules : L.rule list) =
  let table = Hashtbl.create 32 in
  let candidates = ref [] in
  List.iteri (fun index (rule : L.rule) ->
    let rec collect reversed = function
      | [] -> ()
      | premise :: suffix ->
          let reversed = premise :: reversed in
          if List.length reversed >= 2 then (
            let candidate = match Hashtbl.find_opt table reversed with
              | Some candidate -> candidate
              | None ->
                  let candidate = { prefix = List.rev reversed; uses = [] } in
                  Hashtbl.add table reversed candidate;
                  candidates := candidate :: !candidates;
                  candidate in
            candidate.uses <- (index, rule, suffix) :: candidate.uses);
          collect reversed suffix
    in
    collect [] rule.premises) rules;
  (* Traverse in source order so equal scores yield reproducible output. The
     estimate charges for the new relation, its arguments and its one rule. *)
  List.fold_left (fun best candidate ->
    let count = List.length candidate.uses in
    if count < 2 then best else
    let inside = union_map premise_names candidate.prefix in
    let outside = union_map (fun (_, (rule : L.rule), suffix) ->
      Names.union (application_names rule.conclusion)
        (union_map premise_names suffix)) candidate.uses in
    let boundary = Names.inter inside outside in
    let weight = List.fold_left (fun sum p -> sum + premise_weight p) 0 candidate.prefix in
    let score = (count - 1) * weight - (count + 1) * (4 + 2 * Names.cardinal boundary) - 24 in
    let previous = match best with None -> 0 | Some (score, _, _, _) -> score in
    if score > previous then Some (score, candidate, inside, boundary) else best)
    None (List.rev !candidates)

(* Definitional extension of the WFS program: the helper proves exactly the
   shared conjunction. Only variables used by a consumer cross its boundary;
   other witnesses remain bound by the helper's rule. No rule is discarded. *)
let share (declaration : L.declaration) : L.declaration list =
  match declaration with
  | L.Relation relation ->
      let rec factor index rules helpers =
        match best_prefix rules with
        | None -> L.Relation { relation with rules } :: List.rev helpers
        | Some (_, candidate, inside, boundary) ->
            let _, source, _ = List.hd candidate.uses in
            let binders = List.filter (fun (name, _) -> Names.mem name inside) source.binders in
            let parameters = List.filter (fun (name, _) -> Names.mem name boundary) binders in
            let name = relation.name ^ ":prefix:" ^ string_of_int index in
            let call : L.application = {
              target = L.Global name;
              type_arguments = List.map (fun name -> L.TypeParameter name) relation.type_parameters;
              instance_arguments = []; print_instance_arguments = [];
              arguments = List.map (fun (name, typ) -> L.Variable (name, typ)) parameters } in
            let helper = L.Relation { relation with name;
              argument_types = List.map snd parameters; input_positions = None; notation = None;
              selection_policy = L.Nondeterministic;
              rules = [ { L.name = "intro"; binders; premises = candidate.prefix;
                          catchable = []; conclusion = call } ] } in
            let rules = List.mapi (fun index (rule : L.rule) ->
              match List.find_opt (fun (used, _, _) -> used = index) candidate.uses with
              | None -> rule
              | Some (_, _, suffix) ->
                  { rule with premises = L.Holds call :: suffix;
                    binders = List.filter (fun (name, _) ->
                      not (Names.mem name inside) || Names.mem name boundary) rule.binders }) rules in
            factor (index + 1) rules (helper :: helpers)
      in
      factor 0 relation.rules []
  | _ -> [ declaration ]

let global_name = function
  | L.Global name -> Names.singleton name
  | L.Local _ -> Names.empty

let rec term_dependencies term =
  let direct = match term with
    | L.FunctionReference reference -> global_name reference.target
    | L.Apply application -> global_name application.target
    | _ -> Names.empty in
  Names.union direct (union_map term_dependencies (Traversal.term_children term))

let rule_dependencies (rule : L.rule) =
  let calls = union_map (fun (application : L.application) -> global_name application.target)
    (List.concat_map Traversal.premise_applications rule.premises) in
  Names.union calls (union_map term_dependencies
    (rule.conclusion.arguments @ List.concat_map Traversal.premise_terms rule.premises))

let prune_from_roots (roots : string list)
    (declarations : L.located_declaration list) =
  let relations = Hashtbl.create (List.length declarations) in
  List.iter (fun located ->
    match located.L.declaration with
    | L.Relation { name; rules; _ } ->
        Hashtbl.add relations name rules
    | _ -> ()) declarations;
  let rec visit reachable = function
    | [] -> reachable
    | name :: pending when Names.mem name reachable -> visit reachable pending
    | name :: pending ->
        let dependencies = match Hashtbl.find_opt relations name with
          | Some rules -> union_map rule_dependencies rules |> Names.elements
          | None -> [] in
        visit (Names.add name reachable) (dependencies @ pending) in
  let reachable = visit Names.empty roots in
  List.filter (fun located -> match located.L.declaration with
    | L.Relation { name; _ } -> Names.mem name reachable
    | _ -> true) declarations

(* ':' is reserved for generated relations. Every source relation is a root,
   including public functions used only by a client. Keep dependencies under
   negation and function values as well as direct positive calls. *)
let prune_helpers (declarations : L.located_declaration list) =
  let roots = List.filter_map (fun located ->
    match located.L.declaration with
    | L.Relation { name; _ } when not (String.contains name ':') -> Some name
    | _ -> None) declarations in
  prune_from_roots roots declarations

let prune_to_roots (roots : string list)
    (declarations : L.located_declaration list) =
  let available = List.fold_left (fun names located ->
    match located.L.declaration with
    | L.Relation { name; _ } -> Names.add name names
    | _ -> names) Names.empty declarations in
  match List.find_opt (fun name -> not (Names.mem name available)) roots with
  | Some name -> Error ("unknown relation root: " ^ name)
  | None -> Ok (prune_from_roots roots declarations)
