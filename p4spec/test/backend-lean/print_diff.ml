module Value = Runtime.Value
open Util.Source

let bigint (value : int) : Bigint.t = Bigint.of_int value

let case (mixop : string) (arguments : Value.t list) (typ : string) : Value.t =
  Value.Make.(mixop <| arguments <<| typ)

let render (henv : P4.Unparse.HEnv.t) (label : string) (value : Value.t) : unit =
  let rendered : string = Format.asprintf "%a" (P4.Unparse.pp_value henv) value in
  Printf.printf "%s=%S\n" label rendered

let expect_structure_failure (henv : P4.Unparse.HEnv.t) (label : string)
    (value : Value.t) : unit =
  try
    let rendered : string =
      Format.asprintf "%a" (P4.Unparse.pp_value henv) value
    in
    failwith (Printf.sprintf "%s unexpectedly rendered as %S" label rendered)
  with
  | Failure message ->
      if message = "@pp_value: StructV not implemented" then
        Printf.printf "%s=<failure>\n" label
      else raise (Failure message)

let () =
  let (path, surface) : string * bool =
    match Array.to_list Sys.argv with
    | [ _; path ] -> path, false
    | [ _; "--surface"; path ] -> path, true
    | _ -> invalid_arg "usage: print_diff.exe [--surface] PRINT_SPEC"
  in
  let spec =
    match Pass.algo [ path ] with
    | Ok spec -> spec
    | Error diagnostic ->
        prerr_endline diagnostic.message;
        exit 1
  in
  let henv : P4.Unparse.HEnv.t = P4.Unparse.hints_of_spec_al spec in
  if surface then (
    render henv "surface_true" (case "TRUE" [] "booleanLiteral");
    render henv "surface_negative"
      (case "D int" [ Value.Make.int (bigint (-42)) ] "integerLiteral");
    render henv "surface_width"
      (case "nat W int"
         [ Value.Make.nat (bigint 8); Value.Make.int (bigint 255) ]
         "integerLiteral");
    exit 0);
  let empty_text_opt : Value.t = Value.Make.opt Runtime.Type.Typ.Make.text None in
  let empty_text_list : Value.t = Value.Make.list Runtime.Type.Typ.Make.text [] in
  let triple : Value.t =
    Value.Make.tuple
      (Lang.Il.TupleT
         [ Runtime.Type.Typ.Make.nat; Runtime.Type.Typ.Make.nat;
           Runtime.Type.Typ.Make.nat ]
      |> fun typ -> typ $ Util.Source.no_region)
      [ Value.Make.nat (bigint 1); Value.Make.nat (bigint 2);
        Value.Make.nat (bigint 3) ]
  in
  let pair : Value.t =
    Value.Make.tuple
      (Lang.Il.TupleT
         [ Runtime.Type.Typ.Make.nat; Runtime.Type.Typ.Make.nat ]
      |> fun typ -> typ $ Util.Source.no_region)
      [ Value.Make.nat (bigint 2); Value.Make.nat (bigint 3) ]
  in
  let nested_tuple : Value.t =
    Value.Make.tuple
      (Lang.Il.TupleT
         [ Runtime.Type.Typ.Make.nat;
           Lang.Il.TupleT
             [ Runtime.Type.Typ.Make.nat; Runtime.Type.Typ.Make.nat ]
           $ Util.Source.no_region ]
      |> fun typ -> typ $ Util.Source.no_region)
      [ Value.Make.nat (bigint 1); pair ]
  in
  render henv "default"
    (case "SHOW bool int text? text* (nat, nat, nat) (nat, (nat, nat))"
       [ Value.Make.bool true; Value.Make.int (bigint (-7)); empty_text_opt;
         empty_text_list; triple; nested_tuple ]
       "defaultCase");
  render henv "tag" (case "_TAG text" [ Value.Make.text "visible" ] "defaultCase");
  render henv "cursor"
    (case "CUR text text" [ Value.Make.text "first"; Value.Make.text "second" ]
       "hinted");
  render henv "fuse" (case "FUSE text" [ Value.Make.text "x" ] "hinted");
  render henv "brack" (case "BRACK text" [ Value.Make.text "x" ] "hinted");
  render henv "empty_hint"
    (case "EMPTY text" [ Value.Make.text "x" ] "hinted");
  render henv "parent_origin"
    (case "CHILD text" [ Value.Make.text "x" ] "child");
  render henv "wrapper"
    (case "WRAP text" [ Value.Make.text "x" ] "wrapper");
  render henv "wrapper_leaf"
    (case "WRAP text"
       [ case "LEAF text" [ Value.Make.text "x" ] "leaf" ]
       "wrapper");
  render henv "flat_triple" triple;
  render henv "wrapper_triple"
    (case "WRAP text" [ triple ] "wrapper");
  render henv "triple_holder"
    (case "TRIPLE_HOLD wrapper"
       [ case "WRAP text" [ triple ] "wrapper" ]
       "tripleHolder");
  render henv "forwarded"
    (case "FORWARDED text" [ Value.Make.text "x" ] "forwarded");
  render henv "flat_triple_alias" triple;
  render henv "first_print"
    (case "FIRST_PRINT text*" [ Value.Make.list Runtime.Type.Typ.Make.text
       [ Value.Make.text "a" ] ] "firstPrint");
  render henv "second_print"
    (case "SECOND_PRINT text*" [ Value.Make.list Runtime.Type.Typ.Make.text
       [ Value.Make.text "b" ] ] "secondPrint");
  let print_leaf : Value.t = case "PRINT_LEAF" [] "printTree" in
  render henv "print_tree"
    (case "PRINT_NODE printBox<printTree>"
       [ case "PRINT_BOX printTree" [ print_leaf ] "printBox" ]
       "printTree");
  let recursive : Value.t =
    let leaf =
      case "A recB*"
        [ Value.Make.list
            (Runtime.Type.Typ.Make.var ("recB" $ Util.Source.no_region) []) [] ]
        "recA"
    in
    let branch =
      case "B recA?"
        [ Value.Make.opt
            (Runtime.Type.Typ.Make.var ("recA" $ Util.Source.no_region) [])
            (Some leaf) ]
        "recB"
    in
    case "A recB*"
      [ Value.Make.list
          (Runtime.Type.Typ.Make.var ("recB" $ Util.Source.no_region) [])
          [ branch ] ]
      "recA"
  in
  render henv "recursive" recursive;
  render henv "negative_int" (Value.Make.int (bigint (-42)));
  render henv "escaped_text" (Value.Make.text "\"\\\n\t\r\b\195\169");
  let bad : Value.t =
    Value.Make.str
      (Runtime.Type.Typ.Make.var ("bad" $ Util.Source.no_region) []) []
  in
  expect_structure_failure henv "bad" bad;
  expect_structure_failure henv "bad_wrapper"
    (case "BAD bad" [ bad ] "badWrapper");
  render henv "skips_bad" (case "SKIP bad" [ bad ] "skipsBad")
