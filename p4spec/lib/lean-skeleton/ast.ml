module SpecTec = Lang.Il

module Lean = struct
  type type_ref =
    | Name of string
    | TypeParameter of string
    | BuiltinType of string * type_ref list
    | Applied of string * type_ref list
    | Pair of type_ref * type_ref
    | RelationType of type_ref list * type_ref

  type constructor_ref = {
    type_name : string;
    constructor_name : string;
    type_arguments : type_ref list;
  }

  type reference = Global of string | Local of string

  type term =
    | Variable of string * type_ref
    | Constructor of constructor_ref * term list
    | Boolean of bool
    | Number of string * type_ref
    | Text of string
    | FunctionReference of reference
    | Apply of application
    | Coerce of string * type_ref * type_ref * term
    | MembershipTest of string * type_ref * type_ref * (string * int) list * bool * term
    | Lambda of string * type_ref * term
    | Native of string * term list
    | Unary of string * term
    | Binary of string * term * term
    | Typed of term * type_ref
    | Tuple of term * term
    | ListLiteral of term list
    | StructureLiteral of type_ref * (string * term) list
    | StructureUpdate of type_ref * term * string * term
    | Projection of string * string * term
    | Index of term * term
    | Decide of type_ref list * prop

  and comparison = Eq | Ne | Lt | Le | Gt | Ge

  and prop =
    | Comparison of comparison * term * term
    | Membership of term * term
    | IsTrue of term
    | Predicate of term
    | And of prop * prop
    | Or of prop * prop
    | Not of prop
    | Implies of prop * prop
    | Iff of prop * prop

  and application = {
    target : reference;
    type_arguments : type_ref list;
    instance_arguments : type_ref list;
    arguments : term list;
  }

  type premise =
    | Holds of application
    | NotHolds of application * Util.Source.region
    | NotExists of (string * type_ref) list * application * Util.Source.region
    | Prop of prop

  type notation_part = Hole | Literal of string

  type rule = {
    name : string;
    binders : (string * type_ref) list;
    premises : premise list;
    conclusion : application;
  }

  type constructor = {
    name : string;
    arguments : type_ref list;
    result : type_ref;
  }

  type builtin = {
    name : string;
    type_parameters : string list;
    equality_parameters : string list;
    parameters : type_ref list;
    result : type_ref;
    body : string;
  }

  type datatype = {
    name : string;
    type_parameters : string list;
    constructors : constructor list;
  }

  type type_alias = {
    name : string;
    type_parameters : string list;
    body : type_ref;
  }

  type declaration =
    | Datatype of datatype
    | TypeAlias of type_alias
    | Structure of { name : string; fields : (string * type_ref) list }
    | Relation of {
        name : string;
        type_parameters : string list;
        equality_parameters : string list;
        argument_types : type_ref list;
        rules : rule list;
        notation : notation_part list option;
      }
    | Builtin of builtin
    | Coercion of {
        name : string;
        source : type_ref;
        target : type_ref;
        type_parameters : string list;
        cases : (string * string * int) list;
      }
    | Membership of {
        name : string;
        source : type_ref;
        target : type_ref;
        type_parameters : string list;
        cases : (string * int) list;
        exhaustive : bool;
      }

  type located_declaration = {
    declaration : declaration;
    at : Util.Source.region;
  }

  type equality_shape_kind =
    | EqualityDatatype of constructor list
    | EqualityStructure of (string * type_ref) list
    | EqualityList of type_ref
    | EqualityOption of type_ref
    | EqualityPair of type_ref * type_ref

  type equality_shape = {
    equality_name : string;
    equality_type : type_ref;
    equality_kind : equality_shape_kind;
  }

  type manual_equality = {
    equality_type_parameters : string list;
    equality_shapes : equality_shape list;
    equality_instances : (type_ref * string) list;
  }

  type declaration_group =
    | Single of declaration
    | Mutual of declaration list
    | DerivingDecidableEq of declaration_group
    | ManualDecidableEq of manual_equality

  type program = declaration_group list
end
