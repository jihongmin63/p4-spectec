module L = Ast.Lean
module StringMap = Map.Make (String)
module StringSet = Set.Make (String)

module Key = struct
  type t = string * int
  let compare = compare
end

module KeyMap = Map.Make (Key)

type edge_kind = Positive | Negative | Callback

type edge = {
  source : string;
  target : string;
  kind : edge_kind;
}

type callback_site = {
  relation : string;
  parameter : int;
  signature : L.type_ref;
  targets : string list;
  has_external : bool;
}

type component = {
  id : int;
  relations : string list;
  recursive : bool;
  negative_cycle : bool;
}

type analysis = {
  components : component list;
  edges : edge list;
  callback_sites : callback_site list;
}

let rec relations_in_group (group : L.declaration_group) : L.declaration list =
  match group with
  | L.Single (L.Relation _ as relation) -> [ relation ]
  | L.Mutual declarations ->
      List.filter (function L.Relation _ -> true | _ -> false) declarations
  | L.DerivingDecidableEq group -> relations_in_group group
  | L.Single _ | L.ManualDecidableEq _ | L.ManualPrinter _ -> []

let relation_name = function
  | L.Relation { name; _ } -> name
  | _ -> invalid_arg "expected relation"

let relation_rules = function
  | L.Relation { rules; _ } -> rules
  | _ -> invalid_arg "expected relation"

let target_name = function
  | L.Global name -> Some name
  | L.Local _ -> None

let callback_positions (relation : L.declaration) : (int * L.type_ref) list =
  match relation with
  | L.Relation { argument_types; _ } ->
      List.filter_map
        (fun (index, typ) ->
          match typ with L.RelationType _ -> Some (index, typ) | _ -> None)
        (List.mapi (fun index typ -> index, typ) argument_types)
  | _ -> []

let applications_in_terms (terms : L.term list) : L.application list =
  List.concat_map Traversal.term_applications terms

let nested_in_application (application : L.application) : L.application list =
  applications_in_terms application.arguments

let direct_edges (relations : L.declaration StringMap.t)
    (owner : string) (rule : L.rule) : edge list =
  let add kind application edges =
    match target_name application.L.target with
    | Some target when StringMap.mem target relations ->
        { source = owner; target; kind } :: edges
    | _ -> edges
  in
  let from_premise edges = function
    | L.Holds application ->
        List.fold_left (fun edges call -> add Positive call edges)
          (add Positive application edges) (nested_in_application application)
    | L.NotHolds (application, _) ->
        List.fold_left (fun edges call -> add Positive call edges)
          (add Negative application edges) (nested_in_application application)
    | L.NotExists (_, application, _) ->
        List.fold_left (fun edges call -> add Positive call edges)
          (add Negative application edges) (nested_in_application application)
    | L.Prop proposition ->
        applications_in_terms (Traversal.prop_terms proposition)
        |> List.fold_left (fun edges call -> add Positive call edges) edges
  in
  let edges = applications_in_terms rule.conclusion.arguments
    |> List.fold_left (fun edges call -> add Positive call edges) [] in
  List.fold_left from_premise edges rule.premises

let applications_in_rule (rule : L.rule) : L.application list =
  applications_in_terms rule.conclusion.arguments
  @ List.concat_map Traversal.premise_applications rule.premises

let local_callback_parameters (relation : L.declaration) (rule : L.rule) :
    (string * int) list =
  callback_positions relation
  |> List.filter_map (fun (position, _) ->
       match List.nth_opt rule.conclusion.arguments position with
       | Some (L.Variable (name, L.RelationType _)) -> Some (name, position)
       | _ -> None)

let compare_kind left right =
  match left, right with
  | Positive, Positive | Negative, Negative | Callback, Callback -> 0
  | Positive, _ -> -1
  | _, Positive -> 1
  | Negative, _ -> -1
  | _, Negative -> 1

let kind_name = function
  | Positive -> "positive"
  | Negative -> "negative"
  | Callback -> "callback"

let analyze (program : L.program) : (analysis, Diagnostic.t) result =
  let relation_list = List.concat_map relations_in_group program in
  let relations = relation_list
    |> List.map (fun relation -> relation_name relation, relation)
    |> List.to_seq |> StringMap.of_seq in
  let indices = relation_list
    |> List.mapi (fun index relation -> relation_name relation, index)
    |> List.to_seq |> StringMap.of_seq in
  let keys = relation_list
    |> List.concat_map (fun relation ->
         callback_positions relation
         |> List.map (fun (position, _) -> relation_name relation, position)) in
  let initial_targets = List.fold_left
    (fun targets key -> KeyMap.add key StringSet.empty targets)
    KeyMap.empty keys in
  let targets = ref initial_targets in
  let flows : (Key.t * Key.t) list ref = ref [] in
  let invocations : (string * Key.t) list ref = ref [] in
  let invalid_target : string option ref = ref None in
  let add_target key target =
    if StringMap.mem target relations then
      let previous = Option.value ~default:StringSet.empty (KeyMap.find_opt key !targets) in
      targets := KeyMap.add key (StringSet.add target previous) !targets
    else invalid_target := Some target
  in
  List.iter (fun relation ->
    let owner = relation_name relation in
    let rules = relation_rules relation in
    List.iter (fun rule ->
      let local = local_callback_parameters relation rule in
      let local_position name = List.assoc_opt name local in
      List.iter (fun (application : L.application) ->
        (match application.target with
        | L.Local name ->
            Option.iter (fun position ->
              invocations := (owner, (owner, position)) :: !invocations)
              (local_position name)
        | L.Global callee ->
            (match StringMap.find_opt callee relations with
            | None -> ()
            | Some declaration ->
                List.iter (fun (position, expected) ->
                  match List.nth_opt application.arguments position with
                  | Some (L.FunctionReference reference) ->
                      (match reference.signature, expected, reference.target with
                      | L.RelationType _, L.RelationType _, L.Global target ->
                          add_target (callee, position) target
                      | L.RelationType _, L.RelationType _, L.Local name ->
                          Option.iter (fun source_position ->
                            flows := ((owner, source_position), (callee, position))
                              :: !flows) (local_position name)
                      | _ -> ())
                  | Some (L.Variable (name, L.RelationType _)) ->
                      Option.iter (fun source_position ->
                        flows := ((owner, source_position), (callee, position))
                          :: !flows) (local_position name)
                  | _ -> ())
                  (callback_positions declaration)))
      ) (applications_in_rule rule)
    ) rules
  ) relation_list;
  match !invalid_target with
  | Some name ->
      Error (Diagnostic.error ~source:"lean" Util.Source.no_region
        ("typed callback target is not a translated relation: " ^ name))
  | None ->
      let changed = ref true in
      while !changed do
        changed := false;
        List.iter (fun (source, target) ->
          let source_values = Option.value ~default:StringSet.empty
            (KeyMap.find_opt source !targets) in
          let target_values = Option.value ~default:StringSet.empty
            (KeyMap.find_opt target !targets) in
          let combined = StringSet.union source_values target_values in
          if not (StringSet.equal combined target_values) then (
            targets := KeyMap.add target combined !targets;
            changed := true)) !flows
      done;
      let direct = List.concat_map (fun relation ->
        let owner = relation_name relation in
        List.concat_map (direct_edges relations owner) (relation_rules relation))
        relation_list in
      let callback = List.concat_map (fun (owner, key) ->
        Option.value ~default:StringSet.empty (KeyMap.find_opt key !targets)
        |> StringSet.elements
        |> List.map (fun target -> { source = owner; target; kind = Callback }))
        !invocations in
      let compare_edge left right =
        let compare_index name other =
          Int.compare (StringMap.find name indices) (StringMap.find other indices) in
        let by_source = compare_index left.source right.source in
        if by_source <> 0 then by_source else
        let by_target = compare_index left.target right.target in
        if by_target <> 0 then by_target else compare_kind left.kind right.kind in
      let edges = List.sort_uniq compare_edge (direct @ callback) in
      let adjacency = List.fold_left (fun map edge ->
        let old = Option.value ~default:StringSet.empty
          (StringMap.find_opt edge.source map) in
        StringMap.add edge.source (StringSet.add edge.target old) map)
        (List.fold_left (fun map relation ->
           StringMap.add (relation_name relation) StringSet.empty map)
           StringMap.empty relation_list) edges in
      let rec visit graph name (seen, finished) =
        if StringSet.mem name seen then seen, finished else
        let seen = StringSet.add name seen in
        let seen, finished = StringSet.fold
          (fun next state -> visit graph next state)
          (StringMap.find name graph) (seen, finished) in
        seen, name :: finished in
      let names = List.map relation_name relation_list in
      let _, finished = List.fold_left
        (fun state name -> visit adjacency name state)
        (StringSet.empty, []) names in
      let reversed = StringMap.fold (fun name dependencies result ->
        StringSet.fold (fun dependency result ->
          let previous = StringMap.find dependency result in
          StringMap.add dependency (StringSet.add name previous) result)
          dependencies result) adjacency
        (StringMap.map (fun _ -> StringSet.empty) adjacency) in
      let _, groups = List.fold_left (fun (seen, groups) name ->
        if StringSet.mem name seen then seen, groups else
        let seen, members = visit reversed name (seen, []) in
        let members = List.sort (fun left right ->
          Int.compare (StringMap.find left indices) (StringMap.find right indices))
          members in
        seen, members :: groups) (StringSet.empty, []) finished in
      let group_of = List.mapi (fun group members ->
        List.map (fun name -> name, group) members) groups
        |> List.concat |> List.to_seq |> StringMap.of_seq in
      let dependencies = List.mapi (fun id _ -> id, []) groups
        |> List.to_seq |> Hashtbl.of_seq in
      List.iter (fun edge ->
        let source = StringMap.find edge.source group_of in
        let target = StringMap.find edge.target group_of in
        if source <> target then
          let prior = Hashtbl.find dependencies source in
          if not (List.mem target prior) then
            Hashtbl.replace dependencies source (target :: prior)) edges;
      let rec emit done_ids remaining = match remaining with
        | [] -> []
        | _ ->
            let ready id = List.for_all (fun dependency ->
              List.mem dependency done_ids) (Hashtbl.find dependencies id) in
            let id = List.find ready remaining in
            id :: emit (id :: done_ids) (List.filter (( <> ) id) remaining) in
      let ordered_ids = emit [] (List.init (List.length groups) Fun.id) in
      let components = List.mapi (fun id original_id ->
        let members = List.nth groups original_id in
        let internal edge = List.mem edge.source members
          && List.mem edge.target members in
        let self = List.exists (fun edge -> internal edge
          && edge.source = edge.target) edges in
        { id; relations = members;
          recursive = List.length members > 1 || self;
          negative_cycle = List.exists (fun edge ->
            internal edge && edge.kind = Negative) edges }) ordered_ids in
      let invoked = List.fold_left (fun keys (_, key) ->
        if List.mem key keys then keys else key :: keys) [] !invocations in
      let callback_sites = invoked
        |> List.filter_map (fun ((name, position) as key) ->
             match StringMap.find_opt name relations with
             | None -> None
             | Some relation ->
                 Option.map (fun signature ->
                   { relation = name; parameter = position; signature;
                     targets = Option.value ~default:StringSet.empty
                       (KeyMap.find_opt key !targets) |> StringSet.elements;
                     has_external = true })
                   (List.assoc_opt position (callback_positions relation)))
        |> List.sort (fun left right ->
             let by_relation = Int.compare
               (StringMap.find left.relation indices)
               (StringMap.find right.relation indices) in
             if by_relation <> 0 then by_relation
             else Int.compare left.parameter right.parameter) in
      Ok { components; edges; callback_sites }

let json_quote value =
  let buffer = Buffer.create (String.length value + 2) in
  Buffer.add_char buffer '"';
  String.iter (function
    | '"' -> Buffer.add_string buffer "\\\""
    | '\\' -> Buffer.add_string buffer "\\\\"
    | '\n' -> Buffer.add_string buffer "\\n"
    | '\r' -> Buffer.add_string buffer "\\r"
    | '\t' -> Buffer.add_string buffer "\\t"
    | character -> Buffer.add_char buffer character) value;
  Buffer.add_char buffer '"';
  Buffer.contents buffer

let json_list render values =
  "[" ^ String.concat "," (List.map render values) ^ "]"

let render (analysis : analysis) : string =
  let component value =
    Printf.sprintf
      "{\"id\":%d,\"relations\":%s,\"recursive\":%s,\"negative_cycle\":%s}"
      value.id (json_list json_quote value.relations)
      (string_of_bool value.recursive) (string_of_bool value.negative_cycle) in
  let edge value =
    Printf.sprintf "{\"source\":%s,\"target\":%s,\"kind\":%s}"
      (json_quote value.source) (json_quote value.target)
      (json_quote (kind_name value.kind)) in
  let site value =
    Printf.sprintf
      "{\"relation\":%s,\"parameter\":%d,\"signature\":%s,\"targets\":%s,\"external\":%s}"
      (json_quote value.relation) value.parameter
      (json_quote (Translator.type_code value.signature))
      (json_list json_quote value.targets) (string_of_bool value.has_external) in
  "{\"components\":" ^ json_list component analysis.components
  ^ ",\"edges\":" ^ json_list edge analysis.edges
  ^ ",\"callback_sites\":" ^ json_list site analysis.callback_sites ^ "}"
