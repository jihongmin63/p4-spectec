module L = Ast.Lean

let types_source = {lean|class SpecTecExternTypes where
  json : Type
  archState : Type
  objectState : Type
  validArchState : archState → Prop
  validObjectState : objectState → Prop
  decEqJson : DecidableEq json
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
(* Types appearing in the model class fields below. Their transitive extern
   dependencies are also parameters of InProgram, even when Atom is pure. *)
let p4_model_type_names =
  ["typingContext"; "evalContext"; "arch"; "objectId"; "typeIR"; "value"; "nameIR"]

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

let relation (name : string) (argument_types : L.type_ref list)
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
    { target = L.Global name; type_arguments = [];
      instance_arguments = []; print_instance_arguments = []; arguments }
  in
  let rule : L.rule = { name = "allowed"; binders; premises;
    catchable = []; conclusion } in
  L.Relation
    { name; type_parameters = []; equality_parameters = [];
      print_parameters = []; argument_types; input_positions = None;
      selection_policy = L.Nondeterministic;
      rules = [rule]; notation }

let relation_predicate (name : string) : string option =
  match name with
  | "ExternFunctionCall_eval_lctk" -> Some "SpecTec.externStaticAllowed"
  | "ExternFunctionCall_eval" -> Some "SpecTec.externFunctionAllowed"
  | "ExternMethodCall_eval" -> Some "SpecTec.externMethodAllowed"
  | _ -> None

let function_predicate (name : string) : string option =
  match name with
  | "init_archState" -> Some "SpecTecExternTypes.validArchState"
  | "init_objectState" -> Some "SpecTecExternTypes.validObjectState"
  | _ -> None
