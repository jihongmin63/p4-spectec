(** Case data and logical contracts. Interpreter observations are not proofs. *)
type expectation = Case_manifest.expectation = Accept | Reject | AbortReject
type case = {
  source : string;
  expectation : expectation;
  expected : string option;
  value : Runtime.Value.t;
}

let translate_value = Case_value.translate
let name index = "case_" ^ string_of_int index

let proposition index expectation =
  let name = name index in
  match expectation with
  | Accept ->
      "Program_ok " ^ name ^ "_input " ^ name ^ "_expected ∧\n"
      ^ "  ∀ output : p4programIR, Program_ok " ^ name
      ^ "_input output → output = " ^ name ^ "_expected"
  | Reject | AbortReject ->
      "¬ (∃ output : p4programIR, Program_ok " ^ name ^ "_input output)"

let goal index case = "def " ^ name index ^ " : Prop := " ^ proposition index case.expectation

let data ?(noncomputable = false) env index case =
  let name = name index in
  let declaration = if noncomputable then "noncomputable def " else "def " in
  let input = Case_value.translate env (Ast.Lean.Name "p4program") case.value
    |> Printer.print_term [] in
  let expected = match case.expectation, case.expected with
    | Accept, Some expected -> declaration ^ name ^ "_expected : p4programIR := " ^ expected ^ "\n"
    | (Reject | AbortReject), None -> ""
    | _ -> invalid_arg "case expectation and oracle disagree" in
  let note = match case.expectation with
    | AbortReject -> " (interpreter abort; rejection to prove)"
    | Accept | Reject -> "" in
  "-- " ^ name ^ ": " ^ Printf.sprintf "%S" case.source ^ note ^ "\n"
  ^ declaration ^ name ^ "_input : p4program := " ^ input ^ "\n" ^ expected

let context semantics = String.split_on_char '\n' semantics
  |> List.filter (String.starts_with ~prefix:"variable [")
  |> List.sort_uniq String.compare |> String.concat "\n"

let wrap ?(context = "") body =
  "namespace SpecTec\n\n" ^ (if context = "" then "" else context ^ "\n\n")
  ^ body ^ "\n\nend SpecTec"

let render ?(start = 0) spec cases =
  let env = Translator.build_env spec in
  List.mapi (fun index case -> let index = start + index in
      data env index case ^ goal index case) cases
  |> String.concat "\n\n" |> wrap
