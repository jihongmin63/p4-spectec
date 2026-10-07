(* A single total String permutation acts on every transparent field of the IR.
   Abstract extern values and relation references are deliberately fixed.  The
   shape helpers make nested recursion visible to Lean's structural checker. *)
module L = Ast.Lean
module StringMap = Map.Make (String)

exception Unsupported of string

let unsupported message = raise (Unsupported message)

type shape_kind =
  | Datatype of L.constructor list
  | Structure of (string * L.type_ref) list
  | ListShape of L.type_ref
  | OptionShape of L.type_ref
  | TupleShape of L.type_ref list

type shape = { typ : L.type_ref; name : string; kind : shape_kind }

let identifier = Identifier.print_identifier

let rec print_type (typ : L.type_ref) : string =
  match typ with
  | L.Name name -> "_root_.SpecTec." ^ identifier name
  | L.TypeParameter name -> identifier name
  | L.BuiltinType (name, []) -> "_root_." ^ identifier name
  | L.BuiltinType (name, args) ->
      "(" ^ String.concat " " (("_root_." ^ identifier name) :: List.map print_type args) ^ ")"
  | L.Applied (name, args) ->
      "(" ^ String.concat " " (("_root_.SpecTec." ^ identifier name) :: List.map print_type args) ^ ")"
  | L.TupleType args -> print_tuple_type args
  | L.RelationType (args, result) ->
      "(_root_.SpecTecRelationRef "
      ^ (if args = [] then "_root_.Unit" else print_tuple_type args)
      ^ " " ^ print_type result ^ ")"

and print_tuple_type = function
  | [] -> unsupported "FreshAlpha: empty tuple"
  | [ typ ] -> print_type typ
  | typ :: rest -> "(" ^ print_type typ ^ " × " ^ print_tuple_type rest ^ ")"

let rec substitute (bindings : (string * L.type_ref) list) (typ : L.type_ref) : L.type_ref =
  match typ with
  | L.TypeParameter name -> Option.value (List.assoc_opt name bindings) ~default:typ
  | L.BuiltinType (name, args) -> L.BuiltinType (name, List.map (substitute bindings) args)
  | L.Applied (name, args) -> L.Applied (name, List.map (substitute bindings) args)
  | L.TupleType args -> L.TupleType (List.map (substitute bindings) args)
  | L.RelationType (args, result) ->
      L.RelationType (List.map (substitute bindings) args, substitute bindings result)
  | L.Name _ -> typ

let rec declarations = function
  | L.Single declaration -> [ declaration ]
  | L.Mutual declarations -> declarations
  | L.DerivingDecidableEq group -> declarations group
  | L.ManualDecidableEq _ | L.ManualPrinter _ -> []

let data_name = function
  | L.Datatype datatype -> Some datatype.name
  | L.Structure { name; _ } | L.ExternType name -> Some name
  | L.TypeAlias alias -> Some alias.name
  | _ -> None

let arguments = function L.Applied (_, args) -> args | _ -> []

let instantiate name parameters typ =
  let args = arguments typ in
  if List.length args <> List.length parameters then
    unsupported ("FreshAlpha: type arity for " ^ name);
  List.combine parameters args

let normalize (types : L.declaration StringMap.t) : L.type_ref -> L.type_ref =
  let rec normalize trail typ =
    let args = List.map (normalize trail) in
    let typ = match typ with
      | L.BuiltinType (name, values) -> L.BuiltinType (name, args values)
      | L.Applied (name, values) -> L.Applied (name, args values)
      | L.TupleType values -> L.TupleType (args values)
      | L.RelationType (values, result) -> L.RelationType (args values, normalize trail result)
      | _ -> typ in
    match typ with
    | L.Name name | L.Applied (name, _) -> (
        match StringMap.find_opt name types with
        | Some (L.TypeAlias alias) ->
            if List.mem name trail then unsupported ("FreshAlpha: cyclic type alias " ^ name);
            let bindings = instantiate name alias.type_parameters typ in
            normalize (name :: trail) (substitute bindings alias.body)
        | _ -> typ)
    | _ -> typ
  in normalize []

let shape_name typ =
  match typ with
  | L.Name name -> "FreshRename_" ^ name
  | _ -> "FreshRename_shape_" ^ Digest.to_hex (Digest.string (Marshal.to_string typ []))

let children = function
  | Datatype constructors -> List.concat_map (fun (c : L.constructor) -> c.arguments) constructors
  | Structure fields -> List.map snd fields
  | ListShape typ | OptionShape typ -> [ typ ]
  | TupleShape types -> types

let rec type_size = function
  | L.Name _ | L.TypeParameter _ -> 1
  | L.BuiltinType (_, args) | L.Applied (_, args) | L.TupleType args ->
      1 + List.fold_left (fun total typ -> total + type_size typ) 0 args
  | L.RelationType (args, result) ->
      type_size result + List.fold_left (fun total typ -> total + type_size typ) 1 args

let collect (types : L.declaration StringMap.t) (normalize : L.type_ref -> L.type_ref)
    (root : L.type_ref) : shape list =
  let rec collect trail shapes typ =
    let typ = normalize typ in
    let trail = match typ with
      | L.Name name | L.Applied (name, _) -> (
          match List.assoc_opt name trail with
          | Some previous when type_size typ > type_size previous ->
              unsupported ("FreshAlpha: expanding non-uniform recursive type " ^ print_type typ)
          | Some _ -> trail
          | None -> (name, typ) :: trail)
      | _ -> trail in
    if List.exists (fun shape -> shape.typ = typ) shapes then shapes else
    let kind = match typ with
      | L.BuiltinType ("List", [ element ]) -> Some (ListShape element)
      | L.BuiltinType ("Option", [ element ]) -> Some (OptionShape element)
      | L.TupleType elements -> Some (TupleShape elements)
      | L.Name name | L.Applied (name, _) -> (
          match StringMap.find_opt name types with
          | Some (L.Datatype datatype) ->
              let bindings = instantiate name datatype.type_parameters typ in
              Some (Datatype (List.map (fun (c : L.constructor) ->
                { c with arguments = List.map (fun field -> normalize (substitute bindings field)) c.arguments;
                         result = normalize (substitute bindings c.result) }) datatype.constructors))
          | Some (L.Structure { fields; _ }) ->
              Some (Structure (List.map (fun (name, typ) -> name, normalize typ) fields))
          | _ -> None)
      | L.TypeParameter name -> unsupported ("FreshAlpha: unbound type parameter " ^ name)
      | _ -> None in
    match kind with
    | None -> shapes
    | Some kind ->
        let shapes = shapes @ [{typ; name = shape_name typ; kind}] in
        List.fold_left (collect trail) shapes (children kind)
  in collect [] [] root

let find_shape shapes typ = List.find_opt (fun shape -> shape.typ = typ) shapes

let rename shapes typ value =
  match typ, find_shape shapes typ with
  | L.BuiltinType ("String", []), _ -> "(ρ " ^ value ^ ")"
  | _, Some shape -> "(" ^ identifier shape.name ^ " ρ " ^ value ^ ")"
  | _ -> value

let tuple_pattern prefix elements =
  let rec loop index = function
    | [] -> unsupported "FreshAlpha: empty tuple pattern"
    | [ _ ] -> prefix ^ string_of_int index
    | _ :: rest -> "(" ^ prefix ^ string_of_int index ^ ", " ^ loop (index + 1) rest ^ ")"
  in loop 0 elements

let values prefix types = List.mapi (fun i typ -> typ, prefix ^ string_of_int i) types

(* Constructor result types identify the constructor's original owner even when
   the helper is a specialization of a generic datatype. *)
let constructor_name (constructor : L.constructor) =
  let owner = match constructor.result with
    | L.Name name | L.Applied (name, _) -> name
    | _ -> unsupported "FreshAlpha: constructor result is not a datatype" in
  "_root_.SpecTec." ^ identifier owner ^ "." ^ identifier constructor.name

let renamed_constructor shapes constructor fields =
  "(" ^ constructor_name constructor
  ^ String.concat "" (List.map (fun (typ, value) -> " " ^ rename shapes typ value) fields) ^ ")"

let identity_proof shapes owner fields =
  let helpers = fields |> List.filter_map (fun (typ, _) ->
      Option.map (fun shape -> identifier (shape.name ^ "_id")) (find_shape shapes typ))
      |> List.sort_uniq String.compare in
  if helpers = [] then "by rfl" else
  let direct_strings = List.exists (fun (typ, _) -> typ = L.BuiltinType ("String", [])) fields in
  "by simp only [" ^ String.concat ", "
    (identifier owner :: (if direct_strings then "id_eq" :: helpers else helpers)) ^ "]"

let branches shapes shape ~identity =
  let branch pattern fields result =
    "  | " ^ pattern ^ " => "
    ^ (if identity then identity_proof shapes shape.name fields else result) in
  match shape.kind with
  | Datatype [] -> "nomatch value"
  | Datatype constructors ->
      "match value with\n" ^ String.concat "\n" (List.map (fun (c : L.constructor) ->
        let fields = values "x" c.arguments in
        branch ("." ^ identifier c.name ^ String.concat "" (List.map (fun (_, v) -> " " ^ v) fields))
          fields (renamed_constructor shapes c fields)) constructors)
  | Structure fields ->
      let arguments = List.map snd fields in
      let fields = values "x" arguments in
      "match value with\n" ^ branch ("⟨" ^ String.concat ", " (List.map snd fields) ^ "⟩") fields
        ("⟨" ^ String.concat ", " (List.map (fun (typ, v) -> rename shapes typ v) fields) ^ "⟩")
  | ListShape element ->
      "match value with\n" ^ branch "[]" [] "[]" ^ "\n"
      ^ branch "head :: tail" [element, "head"; shape.typ, "tail"]
          (rename shapes element "head" ^ " :: " ^ rename shapes shape.typ "tail")
  | OptionShape element ->
      "match value with\n" ^ branch "_root_.Option.none" [] "_root_.Option.none" ^ "\n"
      ^ branch "_root_.Option.some item" [element, "item"]
          ("_root_.Option.some " ^ rename shapes element "item")
  | TupleShape elements ->
      let fields = values "x" elements in
      let rec nest = function
        | [] -> unsupported "FreshAlpha: empty tuple value"
        | [typ, v] -> rename shapes typ v
        | (typ, v) :: rest -> "(" ^ rename shapes typ v ^ ", " ^ nest rest ^ ")" in
      "match value with\n" ^ branch (tuple_pattern "x" elements) fields (nest fields)

let is_recursive shapes shape =
  let visited = ref [] in
  let rec reaches typ =
    if typ = shape.typ then true else
    if List.mem typ !visited then false else (
      visited := typ :: !visited;
      match find_shape shapes typ with
      | None -> false
      | Some next -> List.exists reaches (children next.kind))
  in List.exists reaches (children shape.kind)

let render_shape shapes shape ~identity =
  let termination = if is_recursive shapes shape then "\ntermination_by structural value" else "" in
  if identity then
    "theorem " ^ identifier (shape.name ^ "_id") ^ " (value : " ^ print_type shape.typ ^ ") : "
    ^ identifier shape.name ^ " _root_.id value = value :=\n  "
    ^ branches shapes shape ~identity ^ termination
  else
    "def " ^ identifier shape.name ^ " (ρ : _root_.String → _root_.String) (value : "
    ^ print_type shape.typ ^ ") : " ^ print_type shape.typ ^ " :=\n  "
    ^ branches shapes shape ~identity ^ termination

let name_helpers = {lean|
def FreshNameBijective.{freshAlphaU,freshAlphaV} {α : Sort freshAlphaU} {β : Sort freshAlphaV} (f : α → β) : Prop :=
  (∀ ⦃a b : α⦄, f a = f b → a = b) ∧ (∀ b : β, ∃ a : α, f a = b)

def FreshNameSwap (a b s : _root_.String) : _root_.String :=
  if s = a then b else if s = b then a else s

theorem FreshNameSwap.involutive (a b s : _root_.String) :
    FreshNameSwap a b (FreshNameSwap a b s) = s := by
  by_cases hsa : s = a <;> by_cases hsb : s = b <;> by_cases hab : a = b <;>
    simp_all [FreshNameSwap]

theorem FreshNameSwap.bijective (a b : _root_.String) :
    FreshNameBijective (FreshNameSwap a b) := by
  constructor
  · intro x y h
    have equal := congrArg (FreshNameSwap a b) h
    simpa only [FreshNameSwap.involutive] using equal
  · intro s
    exact ⟨FreshNameSwap a b s, FreshNameSwap.involutive a b s⟩

theorem FreshNameSwap.fixed (a b s : _root_.String) (ha : s ≠ a) (hb : s ≠ b) :
    FreshNameSwap a b s = s := by
  simp only [FreshNameSwap, ha, hb, ↓reduceIte]
|lean}

let alpha_interface = {lean|
def FreshEq_p4programIR (ρ : _root_.String → _root_.String)
    (expected output : p4programIR) : Prop :=
  FreshRename_p4programIR ρ expected = output

def FreshAlphaIR (allocated protectedNames : _root_.List _root_.String)
    (expected output : p4programIR) : Prop :=
  ∃ ρ : _root_.String → _root_.String, FreshNameBijective ρ ∧
    (∀ s, s ∉ allocated ∨ s ∈ protectedNames → ρ s = s) ∧
    FreshEq_p4programIR ρ expected output

theorem FreshAlphaIR.refl (allocated protectedNames : _root_.List _root_.String)
    (value : p4programIR) : FreshAlphaIR allocated protectedNames value value := by
  refine ⟨_root_.id, ⟨?_, ?_⟩, ?_, ?_⟩
  · intro a b equal
    exact equal
  · intro s
    exact ⟨s, rfl⟩
  · intro s _
    rfl
  · exact FreshRename_p4programIR_id value

theorem FreshNameSwap.allowed (allocated protectedNames : _root_.List _root_.String)
    (a b : _root_.String) (ha : a ∈ allocated) (hb : b ∈ allocated)
    (hpa : a ∉ protectedNames) (hpb : b ∉ protectedNames) :
    ∀ s, s ∉ allocated ∨ s ∈ protectedNames → FreshNameSwap a b s = s := by
  intro s fixed
  apply FreshNameSwap.fixed
  · intro equal
    subst s
    rcases fixed with outside | inside
    · exact outside ha
    · exact hpa inside
  · intro equal
    subst s
    rcases fixed with outside | inside
    · exact outside hb
    · exact hpb inside

theorem FreshAlphaIR.swap (allocated protectedNames : _root_.List _root_.String)
    (a b : _root_.String) (ha : a ∈ allocated) (hb : b ∈ allocated)
    (hpa : a ∉ protectedNames) (hpb : b ∉ protectedNames) (expected output : p4programIR)
    (equal : FreshEq_p4programIR (FreshNameSwap a b) expected output) :
    FreshAlphaIR allocated protectedNames expected output :=
  ⟨FreshNameSwap a b, FreshNameSwap.bijective a b,
    FreshNameSwap.allowed allocated protectedNames a b ha hb hpa hpb, equal⟩
|lean}

let nominal_alpha_interface = {lean|
abbrev FreshSpelling := _root_.SpecTecFresh.FreshId × _root_.String

/-- One identity bijection and one spelling bijection govern the entire
    output.  Repeated references therefore cannot be renamed independently,
    while strings not backed by an allocated identity remain fixed. -/
def FreshNominalAlphaIR
    (expectedAllocated outputAllocated : _root_.List FreshSpelling)
    (protectedNames : _root_.List _root_.String)
    (expected output : p4programIR) : Prop :=
  ∃ (ids : _root_.SpecTecFresh.AlphaRenaming)
    (spellings : _root_.String → _root_.String),
    FreshNameBijective spellings ∧
    (∀ fresh spelling, (fresh, spelling) ∈ expectedAllocated →
      ∃ outputSpelling,
        (ids.toFun fresh, outputSpelling) ∈ outputAllocated ∧
        spellings spelling = outputSpelling) ∧
    (∀ spelling,
      (∀ fresh, (fresh, spelling) ∉ expectedAllocated) ∨
        spelling ∈ protectedNames → spellings spelling = spelling) ∧
    FreshEq_p4programIR spellings expected output

theorem FreshNominalAlphaIR.refl
    (allocated : _root_.List FreshSpelling)
    (protectedNames : _root_.List _root_.String)
    (value : p4programIR) :
    FreshNominalAlphaIR allocated allocated protectedNames value value := by
  let identityIds : _root_.SpecTecFresh.AlphaRenaming :=
    { toFun := _root_.id, invFun := _root_.id,
      leftInv := by intro fresh; rfl,
      rightInv := by intro fresh; rfl }
  refine ⟨identityIds, _root_.id, ⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · intro left right equal
    exact equal
  · intro spelling
    exact ⟨spelling, rfl⟩
  · intro fresh spelling member
    exact ⟨spelling, member, rfl⟩
  · intro spelling fixed
    rfl
  · exact FreshRename_p4programIR_id value
|lean}

let render ?(nominal = false) (program : L.program) : string =
  let types = program |> List.concat_map declarations |> List.filter_map (fun declaration ->
    Option.map (fun name -> name, declaration) (data_name declaration))
    |> List.to_seq |> StringMap.of_seq in
  if not (StringMap.mem "p4programIR" types) then "" else
  let normalize = normalize types in
  let root = normalize (L.Name "p4programIR") in
  let shapes = collect types normalize root in
  (* Extern dependencies inside fixed relation references still require the type
     family instance to state the generated function's signature. *)
  let seen_extern_dependencies = ref [] in
  let rec has_extern typ =
    let typ = normalize typ in
    if List.mem typ !seen_extern_dependencies then false else (
      seen_extern_dependencies := typ :: !seen_extern_dependencies;
      match typ with
      | L.Name name | L.Applied (name, _) -> (
          match StringMap.find_opt name types with
          | Some (L.ExternType _) -> true
          | Some (L.Datatype datatype) ->
              let bindings = instantiate name datatype.type_parameters typ in
              List.exists has_extern
                (List.concat_map (fun (c : L.constructor) -> List.map (substitute bindings) c.arguments) datatype.constructors)
          | Some (L.Structure { fields; _ }) -> List.exists (fun (_, field) -> has_extern field) fields
          | _ -> false)
      | L.BuiltinType (_, args) | L.TupleType args -> List.exists has_extern args
      | L.RelationType (args, result) -> List.exists has_extern (result :: args)
      | L.TypeParameter _ -> false) in
  let functions identity = if shapes = [] then "" else
    "mutual\n\n" ^ String.concat "\n\n" (List.map (fun shape -> render_shape shapes shape ~identity) shapes) ^ "\n\nend\n\n" in
  let root_wrapper = match find_shape shapes root with
    | Some shape when shape.name = "FreshRename_p4programIR" -> ""
    | _ ->
        "def FreshRename_p4programIR (ρ : _root_.String → _root_.String) (value : p4programIR) : p4programIR :=\n  "
        ^ rename shapes root "value" ^ "\n\n"
        ^ "theorem FreshRename_p4programIR_id (value : p4programIR) : FreshRename_p4programIR _root_.id value = value :=\n  "
        ^ identity_proof shapes "FreshRename_p4programIR" [root, "value"] ^ "\n\n" in
  "section\n\n" ^ (if has_extern root then "variable [SpecTecExternTypes]\n\n" else "")
  ^ name_helpers ^ "\n\n" ^ functions false ^ functions true ^ root_wrapper
  ^ alpha_interface
  ^ (if nominal then "\n\n" ^ nominal_alpha_interface else "")
  ^ "\n\nend\n"
