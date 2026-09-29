module S = Ast.SpecTec
module Mixfix = Domain.Mixfix
module StringMap = Map.Make (String)
module StringSet = Set.Make (String)
open Util.Source

let unions (sets : StringSet.t list) : StringSet.t =
  List.fold_left StringSet.union StringSet.empty sets

let function_reference (locals : string list) (id : S.id) : StringSet.t =
  if List.mem id.it locals then StringSet.empty else StringSet.singleton ("$" ^ id.it)

let rec expression (locals : string list) (exp : S.exp) : StringSet.t =
  let recurse : S.exp -> StringSet.t = expression locals in
  match exp.it with
  | BoolE _ | NumE _ | TextE _ | VarE _ | OptE None -> StringSet.empty
  | UnE (_, _, exp) | UpCastE (_, exp) | DownCastE (_, exp)
  | SubE (exp, _, _) | MatchE (exp, _) | OptE (Some exp)
  | LenE exp | DotE (exp, _) | IterE (exp, _) -> recurse exp
  | BinE (_, _, left, right) | CmpE (_, _, left, right)
  | ConsE (left, right) | CatE (left, right) | MemE (left, right)
  | IdxE (left, right) -> StringSet.union (recurse left) (recurse right)
  | TupleE exps | ListE exps -> unions (List.map recurse exps)
  | CaseE notation -> unions (List.map recurse (Mixfix.args notation))
  | StrE fields -> unions (List.map (fun (_, exp) -> recurse exp) fields)
  | SliceE (base, low, high) -> unions (List.map recurse [ base; low; high ])
  | UpdE (base, selector, value) ->
      unions [ recurse base; path locals selector; recurse value ]
  | CallE (id, _, arguments) ->
      StringSet.union (function_reference locals id)
        (unions (List.map (argument locals) arguments))

and path (locals : string list) (selector : S.path) : StringSet.t =
  match selector.it with
  | RootP -> StringSet.empty
  | DotP (selector, _) -> path locals selector
  | IdxP (selector, index) ->
      StringSet.union (path locals selector) (expression locals index)
  | SliceP (selector, low, high) ->
      unions [ path locals selector; expression locals low; expression locals high ]

and argument (locals : string list) (arg : S.arg) : StringSet.t =
  match arg.it with
  | ExpA exp -> expression locals exp
  | DefA id -> function_reference locals id

let rec premise (locals : string list) (prem : S.prem) : StringSet.t =
  match prem.it with
  | RulePr (id, notation, _) | IfHoldPr (id, notation) | IfNotHoldPr (id, notation) ->
      StringSet.add id.it (unions (List.map (expression locals) (Mixfix.args notation)))
  | IfPr exp | DebugPr exp -> expression locals exp
  | LetPr (left, right) -> StringSet.union (expression locals left) (expression locals right)
  | IterPr (prem, _) -> premise locals prem

let local_functions (parameters : S.param list) : string list =
  List.filter_map
    (fun (parameter : S.param) -> match parameter.it with
      | DefP (id, _, _, _) -> Some id.it
      | ExpP _ -> None)
    parameters

let clause (locals : string list) (source : S.clause) : StringSet.t =
  let (arguments, result, premises) : S.arg list * S.exp * S.prem list = source.it in
  unions (expression locals result :: List.map (argument locals) arguments
    @ List.map (premise locals) premises)

let rule (source : S.rule) : StringSet.t =
  let (_, conclusion, premises) : S.id * S.notexp * S.prem list = source.it in
  unions (List.map (expression []) (Mixfix.args conclusion)
    @ List.map (premise []) premises)

type definition = {
  name : string;
  dependencies : StringSet.t;
  regular_dependencies : StringSet.t;
  otherwise : bool;
}

let definition (source : S.def) : definition option =
  match source.it with
  | FuncDecD (id, _, parameters, _, clauses, otherwise, _) ->
      let locals : string list = local_functions parameters in
      let regular : StringSet.t = unions (List.map (clause locals) clauses) in
      Some { name = "$" ^ id.it; otherwise = Option.is_some otherwise;
        regular_dependencies = regular;
        dependencies =
          unions (regular :: List.map (clause locals) (Option.to_list otherwise)) }
  | RelD (id, _, _, groups, otherwise, _) ->
      let regular : StringSet.t =
        unions
          (List.concat_map
             (fun (group : S.rulegroup) -> List.map rule (snd group.it))
             groups)
      in
      Some { name = id.it; otherwise = Option.is_some otherwise;
        regular_dependencies = regular;
        dependencies =
          unions
            (regular
            :: List.map (fun (group : S.elsegroup) -> rule (snd group.it))
                 (Option.to_list otherwise)) }
  | TableDecD (id, parameters, _, rows, _) ->
      let locals : string list = local_functions parameters in
      let row (source : S.tablerow) : StringSet.t =
        let (arguments, result) : S.arg list * S.exp = source.it in
        unions (expression locals result :: List.map (argument locals) arguments)
      in
      let dependencies : StringSet.t = unions (List.map row rows) in
      Some { name = "$" ^ id.it; otherwise = false;
        regular_dependencies = dependencies; dependencies }
  | TypD _ | VarD _ | ExternTypD _ | ExternRelD _ | ExternDecD _ | BuiltinDecD _ -> None

(* Inspect IL dependencies before translation. Global function arguments are
   dependencies too; DefP names shadow global functions.
   Only the regular clauses matter: the negated regular relation is cyclic when
   they reach the definition, while recursion through the otherwise clause
   itself stays positive. *)
let recursive_otherwise (program : S.spec) : string list =
  let definitions : definition list = List.filter_map definition program in
  let graph : StringSet.t StringMap.t =
    List.fold_left
      (fun graph (definition : definition) ->
        StringMap.add definition.name definition.dependencies graph)
      StringMap.empty definitions
  in
  let recursive (definition : definition) : bool =
    let rec reaches (visited : StringSet.t) (pending : StringSet.t) : bool =
      match StringSet.choose_opt pending with
      | None -> false
      | Some name ->
          if name = definition.name then true
          else
            let pending : StringSet.t = StringSet.remove name pending in
            if StringSet.mem name visited then reaches visited pending
            else
              let visited : StringSet.t = StringSet.add name visited in
              match StringMap.find_opt name graph with
              | None -> reaches visited pending
              | Some dependencies ->
                  reaches visited (StringSet.union pending dependencies)
    in
    reaches StringSet.empty definition.regular_dependencies
  in
  List.filter_map
    (fun (definition : definition) ->
      if definition.otherwise && recursive definition then Some definition.name else None)
    definitions
