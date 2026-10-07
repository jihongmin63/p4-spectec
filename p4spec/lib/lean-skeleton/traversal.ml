module L = Ast.Lean

let rec map_term_types (map : L.type_ref -> L.type_ref) (term : L.term) : L.term =
  let recurse : L.term -> L.term = map_term_types map in
  match term with
  | Variable (name, typ) -> L.Variable (name, map typ)
  | Number (value, typ) -> L.Number (value, map typ)
  | Constructor (reference, arguments) ->
      L.Constructor
        ({ reference with type_arguments = List.map map reference.type_arguments },
         List.map recurse arguments)
  | Apply application -> L.Apply (map_application_types map application)
  | Coerce (name, source, target, value) ->
      L.Coerce (name, map source, map target, recurse value)
  | MembershipTest (name, source, target, cases, exhaustive, value) ->
      L.MembershipTest (name, map source, map target, cases, exhaustive, recurse value)
  | Lambda (name, typ, body) -> L.Lambda (name, map typ, recurse body)
  | Native (name, arguments) -> L.Native (name, List.map recurse arguments)
  | Unary (operator, value) -> L.Unary (operator, recurse value)
  | Binary (operator, left, right) -> L.Binary (operator, recurse left, recurse right)
  | Typed (value, typ) -> L.Typed (recurse value, map typ)
  | Tuple (left, right) -> L.Tuple (recurse left, recurse right)
  | ListLiteral values -> L.ListLiteral (List.map recurse values)
  | StructureLiteral (typ, fields) ->
      L.StructureLiteral (map typ, List.map (fun (name, value) -> name, recurse value) fields)
  | StructureUpdate (typ, base, field, value) ->
      L.StructureUpdate (map typ, recurse base, field, recurse value)
  | Projection (name, field, value) -> L.Projection (name, field, recurse value)
  | Index (base, index) -> L.Index (recurse base, recurse index)
  | Decide (types, prop) ->
      L.Decide (List.map map types, map_prop_types map prop)
  | FunctionReference reference ->
      L.FunctionReference { reference with signature = map reference.signature }
  | Boolean _ | Text _ -> term

and map_prop_types (map : L.type_ref -> L.type_ref) (prop : L.prop) : L.prop =
  match prop with
  | Comparison (operator, left, right) ->
      L.Comparison (operator, map_term_types map left, map_term_types map right)
  | Membership (element, collection) ->
      L.Membership (map_term_types map element, map_term_types map collection)
  | IsTrue term -> L.IsTrue (map_term_types map term)
  | Predicate term -> L.Predicate (map_term_types map term)
  | Not prop -> L.Not (map_prop_types map prop)
  | And (left, right) -> L.And (map_prop_types map left, map_prop_types map right)
  | Or (left, right) -> L.Or (map_prop_types map left, map_prop_types map right)
  | Implies (left, right) -> L.Implies (map_prop_types map left, map_prop_types map right)
  | Iff (left, right) -> L.Iff (map_prop_types map left, map_prop_types map right)
  | Forall (name, typ, body) ->
      L.Forall (name, map typ, map_prop_types map body)

and map_application_types (map : L.type_ref -> L.type_ref)
    (application : L.application) : L.application =
  { application with type_arguments = List.map map application.type_arguments;
    instance_arguments = List.map map application.instance_arguments;
    print_instance_arguments =
      List.map map application.print_instance_arguments;
    arguments = List.map (map_term_types map) application.arguments }

let map_premise_types (map : L.type_ref -> L.type_ref) (premise : L.premise) :
    L.premise =
  match premise with
  | Holds application -> L.Holds (map_application_types map application)
  | NotHolds (application, at) -> L.NotHolds (map_application_types map application, at)
  | NotExists (binders, application, at) ->
      L.NotExists (List.map (fun (name, typ) -> name, map typ) binders,
        map_application_types map application, at)
  | Prop prop -> L.Prop (map_prop_types map prop)

let rec prop_terms (prop : L.prop) : L.term list =
  match prop with
  | Comparison (_, left, right) | Membership (left, right) -> [ left; right ]
  | IsTrue term -> [ term ]
  | Predicate term -> [ term ]
  | Not prop -> prop_terms prop
  | And (left, right) | Or (left, right) | Implies (left, right) | Iff (left, right) ->
      prop_terms left @ prop_terms right
  | Forall (_, _, body) -> prop_terms body

let term_children (term : L.term) : L.term list =
  match term with
  | Constructor (_, arguments) | Native (_, arguments) | ListLiteral arguments -> arguments
  | Apply application -> application.arguments
  | Coerce (_, _, _, value) | Lambda (_, _, value)
  | MembershipTest (_, _, _, _, _, value) -> [ value ]
  | Unary (_, value) | Typed (value, _) | Projection (_, _, value) -> [ value ]
  | Binary (_, left, right) | Tuple (left, right) | Index (left, right) -> [ left; right ]
  | StructureLiteral (_, fields) -> List.map snd fields
  | StructureUpdate (_, base, _, value) -> [ base; value ]
  | Decide (_, prop) -> prop_terms prop
  | Variable _ | Boolean _ | Number _ | Text _ | FunctionReference _ -> []

let premise_terms (premise : L.premise) : L.term list =
  match premise with
  | Holds application | NotHolds (application, _)
  | NotExists (_, application, _) -> application.arguments
  | Prop prop -> prop_terms prop

let rec term_applications (term : L.term) : L.application list =
  let nested : L.application list =
    List.concat_map term_applications (term_children term)
  in
  match term with L.Apply application -> application :: nested | _ -> nested

let premise_applications (premise : L.premise) : L.application list =
  let direct : L.application list =
    match premise with
    | L.Holds application | L.NotHolds (application, _)
    | L.NotExists (_, application, _) -> [ application ]
    | L.Prop _ -> []
  in
  direct @ List.concat_map term_applications (premise_terms premise)

let rec map_term_applications (map : L.application -> L.application)
    (term : L.term) : L.term =
  let recurse : L.term -> L.term = map_term_applications map in
  match term with
  | Variable _ | Boolean _ | Number _ | Text _ | FunctionReference _ -> term
  | Constructor (reference, arguments) ->
      L.Constructor (reference, List.map recurse arguments)
  | Apply application ->
      L.Apply
        (map
           { application with
             arguments = List.map recurse application.arguments })
  | Coerce (name, source, target, value) ->
      L.Coerce (name, source, target, recurse value)
  | MembershipTest (name, source, target, cases, exhaustive, value) ->
      L.MembershipTest
        (name, source, target, cases, exhaustive, recurse value)
  | Lambda (name, typ, body) -> L.Lambda (name, typ, recurse body)
  | Native (name, arguments) -> L.Native (name, List.map recurse arguments)
  | Unary (operator, value) -> L.Unary (operator, recurse value)
  | Binary (operator, left, right) ->
      L.Binary (operator, recurse left, recurse right)
  | Typed (value, typ) -> L.Typed (recurse value, typ)
  | Tuple (left, right) -> L.Tuple (recurse left, recurse right)
  | ListLiteral values -> L.ListLiteral (List.map recurse values)
  | StructureLiteral (typ, fields) ->
      L.StructureLiteral
        (typ, List.map (fun (name, value) -> name, recurse value) fields)
  | StructureUpdate (typ, base, field, value) ->
      L.StructureUpdate (typ, recurse base, field, recurse value)
  | Projection (name, field, value) ->
      L.Projection (name, field, recurse value)
  | Index (base, index) -> L.Index (recurse base, recurse index)
  | Decide (types, prop) ->
      L.Decide (types, map_prop_applications map prop)

and map_prop_applications (map : L.application -> L.application)
    (prop : L.prop) : L.prop =
  let recurse : L.prop -> L.prop = map_prop_applications map in
  let term : L.term -> L.term = map_term_applications map in
  match prop with
  | Comparison (operator, left, right) ->
      L.Comparison (operator, term left, term right)
  | Membership (element, collection) ->
      L.Membership (term element, term collection)
  | IsTrue value -> L.IsTrue (term value)
  | Predicate value -> L.Predicate (term value)
  | Not value -> L.Not (recurse value)
  | And (left, right) -> L.And (recurse left, recurse right)
  | Or (left, right) -> L.Or (recurse left, recurse right)
  | Implies (left, right) -> L.Implies (recurse left, recurse right)
  | Iff (left, right) -> L.Iff (recurse left, recurse right)
  | Forall (name, typ, body) -> L.Forall (name, typ, recurse body)

let map_premise_applications (map : L.application -> L.application)
    (premise : L.premise) : L.premise =
  let application (value : L.application) : L.application =
    map
      { value with
        arguments = List.map (map_term_applications map) value.arguments }
  in
  match premise with
  | Holds value -> L.Holds (application value)
  | NotHolds (value, at) -> L.NotHolds (application value, at)
  | NotExists (binders, value, at) ->
      L.NotExists (binders, application value, at)
  | Prop prop -> L.Prop (map_prop_applications map prop)
