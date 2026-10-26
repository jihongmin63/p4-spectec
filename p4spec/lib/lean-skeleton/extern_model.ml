module L = Ast.Lean

let types_source ~ordered = {lean|class SpecTecExternTypes where
  json : Type
  archState : Type
  objectState : Type
|lean}
  ^ (if ordered then "" else {lean|  validArchState : archState → Prop
  validObjectState : objectState → Prop
|lean})
  ^ {lean|  decEqJson : DecidableEq json
  decEqArchState : DecidableEq archState
  decEqObjectState : DecidableEq objectState

instance [SpecTecExternTypes] : DecidableEq SpecTecExternTypes.json :=
  SpecTecExternTypes.decEqJson
instance [SpecTecExternTypes] : DecidableEq SpecTecExternTypes.archState :=
  SpecTecExternTypes.decEqArchState
instance [SpecTecExternTypes] : DecidableEq SpecTecExternTypes.objectState :=
  SpecTecExternTypes.decEqObjectState|lean}

(* This is an interface: an architecture supplies the predicates and static
   return-type environment. No result is selected by the translator. *)
let p4_source = {lean|-- The return-type relations are supplied by the static P4 typing environment.
-- The IL result datatype alone does not establish the P4 return type.
-- validArch covers the target's architecture and stored object invariants.
class SpecTecP4ExternModel where
  validTypingContext : typingContext → Prop
  validEvalContext : evalContext → Prop
  validArch : arch → Prop
  validObject : arch → objectId → Prop
  valueHasType : typeIR → value → Prop
  voidReturnType : typeIR → Prop
  staticReturnType : typingContext → nameIR → List nameIR → typeIR → Prop
  functionReturnType : evalContext → arch → nameIR → List nameIR → typeIR → Prop
  methodReturnType : evalContext → arch → objectId → nameIR → List nameIR → typeIR → Prop

variable [SpecTecP4ExternModel]

def externCallResultValid (expected : typeIR) : callResult → Prop
  | .RETURN (some value) => SpecTecP4ExternModel.valueHasType expected value
  | .RETURN none => SpecTecP4ExternModel.voidReturnType expected
  | .EXIT => True
  | .REJECT _ => True

def externStaticAllowed (ctx : typingContext) (name : nameIR)
    (args : List nameIR) (result : value) : Prop :=
  SpecTecP4ExternModel.validTypingContext ctx ∧
  ∃ expected : typeIR,
    SpecTecP4ExternModel.staticReturnType ctx name args expected ∧
    SpecTecP4ExternModel.valueHasType expected result

def externFunctionAllowed (ctx₀ : evalContext) (arch₀ : arch)
    (name : nameIR) (args : List nameIR) (ctx₁ : evalContext)
    (arch₁ : arch) (result : callResult) : Prop :=
  SpecTecP4ExternModel.validEvalContext ctx₀ ∧
  SpecTecP4ExternModel.validEvalContext ctx₁ ∧
  SpecTecP4ExternModel.validArch arch₀ ∧
  SpecTecP4ExternModel.validArch arch₁ ∧
  SpecTecExternTypes.validArchState arch₀.STATE ∧
  SpecTecExternTypes.validArchState arch₁.STATE ∧
  ∃ expected : typeIR,
    SpecTecP4ExternModel.functionReturnType ctx₀ arch₀ name args expected ∧
    externCallResultValid expected result

def externMethodAllowed (ctx₀ : evalContext) (arch₀ : arch)
    (object : objectId) (name : nameIR) (args : List nameIR)
    (ctx₁ : evalContext) (arch₁ : arch) (result : callResult) : Prop :=
  SpecTecP4ExternModel.validEvalContext ctx₀ ∧
  SpecTecP4ExternModel.validEvalContext ctx₁ ∧
  SpecTecP4ExternModel.validArch arch₀ ∧
  SpecTecP4ExternModel.validArch arch₁ ∧
  SpecTecExternTypes.validArchState arch₀.STATE ∧
  SpecTecExternTypes.validArchState arch₁.STATE ∧
  SpecTecP4ExternModel.validObject arch₀ object ∧
  SpecTecP4ExternModel.validObject arch₁ object ∧
  ∃ expected : typeIR,
    SpecTecP4ExternModel.methodReturnType ctx₀ arch₀ object name args expected ∧
    externCallResultValid expected result|lean}

let variable (index : int) (typ : L.type_ref) : L.term =
  L.Variable ("arg" ^ string_of_int index, typ)

let relation ?(type_parameters = []) (name : string) (argument_types : L.type_ref list)
    (predicate : string option) (notation : L.notation_part list option) :
    L.declaration =
  let binders : (string * L.type_ref) list =
    List.mapi (fun i typ -> "arg" ^ string_of_int i, typ) argument_types
  in
  let arguments = List.mapi variable argument_types in
  let premises = match predicate with
    | None -> []
    | Some predicate ->
        let predicate_arguments =
          if name = "$init_archState" || name = "$init_objectState" then
            (match List.rev arguments with
             | output :: _ -> [ output ]
             | [] -> invalid_arg "external function has no result")
          else arguments
        in
        [ L.Prop (L.Predicate (L.Native (predicate, predicate_arguments))) ]
  in
  let conclusion : L.application =
    { target = L.Global name;
      type_arguments = List.map (fun n -> L.TypeParameter n) type_parameters;
      instance_arguments = []; print_instance_arguments = []; arguments }
  in
  let rule : L.rule = { name = "allowed"; binders; premises; conclusion } in
  L.Relation
    { name; type_parameters; equality_parameters = [];
      print_parameters = []; argument_types; rules = [rule]; notation }

let relation_predicate (name : string) : string option =
  match name with
  | "ExternFunctionCall_eval_lctk" -> Some "SpecTec.externStaticAllowed"
  | "ExternFunctionCall_eval" -> Some "SpecTec.externFunctionAllowed"
  | "ExternMethodCall_eval" -> Some "SpecTec.externMethodAllowed"
  | _ -> None

let p4_type_dependencies =
  [ "typingContext"; "evalContext"; "arch"; "objectId"; "typeIR";
    "value"; "nameIR"; "callResult"; "archState" ]

let predicate_dependencies (predicate : string) : string list =
  match predicate with
  | "SpecTec.externStaticAllowed" | "SpecTec.externFunctionAllowed"
  | "SpecTec.externMethodAllowed" -> p4_type_dependencies
  | "SpecTecExternTypes.validArchState" -> ["archState"]
  | "SpecTecExternTypes.validObjectState" -> ["objectState"]
  | _ -> []

let uses_p4_model (declaration : L.declaration) : bool =
  match declaration with
  | L.Relation { rules; _ } ->
      List.exists (fun (rule : L.rule) ->
        List.exists (function
          | L.Prop (L.Predicate (L.Native (predicate, _))) ->
              predicate_dependencies predicate = p4_type_dependencies
          | _ -> false) rule.premises) rules
  | _ -> false

let validate_p4_model (lookup : string -> L.declaration option) : string option =
  let monomorphic_type = function
    | Some (L.ExternType _ | L.Structure _
           | L.Datatype { type_parameters = []; _ }
           | L.TypeAlias { type_parameters = []; _ }) -> true
    | _ -> false in
  match List.find_opt (fun name -> not (monomorphic_type (lookup name)))
    p4_type_dependencies with
  | Some name -> Some ("requires monomorphic type declaration " ^ name)
  | None ->
      match lookup "archState", lookup "arch", lookup "callResult" with
      | Some (L.ExternType "archState"),
        Some (L.Structure { fields; _ }), Some (L.Datatype datatype)
        when List.assoc_opt "STATE" fields = Some (L.Name "archState") ->
          let constructors = List.map (fun (constructor : L.constructor) ->
            constructor.name, constructor.arguments) datatype.constructors in
          if List.length constructors = 3
            && List.assoc_opt "RETURN" constructors =
               Some [ L.BuiltinType ("Option", [L.Name "value"]) ]
            && List.assoc_opt "EXIT" constructors = Some []
            && (match List.assoc_opt "REJECT" constructors with
                | Some [_] -> true | _ -> false)
          then None
          else Some "callResult must contain RETURN value?, EXIT, and REJECT"
      | _ -> Some "requires extern archState and an arch structure with STATE archState"

let expected_p4_arguments (name : string) : L.type_ref list option =
  let names values = List.map (fun name -> L.Name name) values in
  let arguments = L.BuiltinType ("List", [L.Name "nameIR"]) in
  match name with
  | "ExternFunctionCall_eval_lctk" ->
      Some (names ["typingContext"; "nameIR"] @ [arguments; L.Name "value"])
  | "ExternFunctionCall_eval" ->
      Some (names ["evalContext"; "arch"; "nameIR"] @ [arguments]
            @ names ["evalContext"; "arch"; "callResult"])
  | "ExternMethodCall_eval" ->
      Some (names ["evalContext"; "arch"; "objectId"; "nameIR"] @ [arguments]
            @ names ["evalContext"; "arch"; "callResult"])
  | _ -> None

let function_predicate (name : string) : string option =
  match name with
  | "init_archState" -> Some "SpecTecExternTypes.validArchState"
  | "init_objectState" -> Some "SpecTecExternTypes.validObjectState"
  | _ -> None
