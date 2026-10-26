let ( let* ) = Result.bind

type options = {
  paths_spec : string list;
  includes_p4 : string list;
  cases : (Case_obligation.expectation * string * string option) list;
  keep_going : bool;
  ordered : bool;
  executable : bool;
  obligations_only : bool;
  dump_output : string option;
  check_rejection : string option;
  batch_cases : string option;
  case_range : (int * int) option;
  emit_modules : string option;
  emit_cases : string option;
  module_split_bytes : int option;
}

let usage =
  "Usage: lean-skeleton [--relation-semantics ordered|declarative] [--executable] [--keep-going] [--obligations-only] \
   [--case P4 EXPECTED | --reject-case P4 | --manifest TSV]... \
   [--case-range START COUNT] \
   [--emit-modules DIR | --emit-cases DIR] [--module-split-bytes N] \
   [--dump-output P4 | --check-rejection P4 | --batch-cases PATHS] \
   [-I DIR]... <spec-path>..."

let read_manifest = Case_manifest.read

let parse_options arguments =
  let rec loop options = function
    | [] -> Ok { options with
        paths_spec = List.rev options.paths_spec;
        includes_p4 = List.rev options.includes_p4;
        cases = List.rev options.cases }
    | "--relation-semantics" :: mode :: rest when mode = "ordered" || mode = "declarative" ->
        loop { options with ordered = mode = "ordered" } rest
    | "--relation-semantics" :: _ ->
        Error "--relation-semantics requires ordered or declarative"
    | "--keep-going" :: rest -> loop { options with keep_going = true } rest
    | "--executable" :: rest -> loop { options with executable = true } rest
    | "--obligations-only" :: rest ->
        loop { options with obligations_only = true } rest
    | "--emit-modules" :: directory :: rest when directory <> "" ->
        loop { options with emit_modules = Some directory } rest
    | "--emit-cases" :: directory :: rest when directory <> "" ->
        loop { options with emit_cases = Some directory } rest
    | "--module-split-bytes" :: bytes :: rest ->
        (match int_of_string_opt bytes with
        | Some bytes when bytes > 0 ->
            loop { options with module_split_bytes = Some bytes } rest
        | _ -> Error "--module-split-bytes requires a positive integer")
    | "--case" :: path :: expected :: rest ->
        loop { options with cases =
          (Case_obligation.Accept, path, Some expected) :: options.cases } rest
    | "--reject-case" :: path :: rest ->
        loop { options with cases =
          (Case_obligation.Reject, path, None) :: options.cases } rest
    | "--dump-output" :: path :: rest ->
        loop { options with dump_output = Some path } rest
    | "--check-rejection" :: path :: rest ->
        loop { options with check_rejection = Some path } rest
    | "--batch-cases" :: path :: rest ->
        loop { options with batch_cases = Some path } rest
    | "--case-range" :: start :: count :: rest ->
        (match int_of_string_opt start, int_of_string_opt count with
        | Some start, Some count when start >= 0 && count > 0 ->
            loop { options with case_range = Some (start, count) } rest
        | _ -> Error "--case-range requires a nonnegative start and positive count")
    | "--manifest" :: path :: rest ->
        let* cases = read_manifest path in
        loop { options with cases = List.rev_append cases options.cases } rest
    | "-I" :: path :: rest ->
        loop { options with includes_p4 = path :: options.includes_p4 } rest
    | ("--case" | "--reject-case" | "--manifest" | "--dump-output" |
       "--check-rejection" | "--batch-cases" | "--case-range" |
       "--emit-modules" | "--emit-cases" | "--module-split-bytes" | "-I") :: [] -> Error usage
    | argument :: _ when String.starts_with ~prefix:"-" argument ->
        Error ("Unknown option: " ^ argument ^ "\n" ^ usage)
    | path :: rest ->
        loop { options with paths_spec = path :: options.paths_spec } rest
  in
  loop { paths_spec = []; includes_p4 = []; cases = [];
         ordered = true; executable = false; keep_going = false; obligations_only = false; dump_output = None;
         check_rejection = None; batch_cases = None; case_range = None;
         emit_modules = None; emit_cases = None; module_split_bytes = None } arguments

let parse_case includes_p4 (expectation, source, expected_path) =
  let* value =
    try Ok (P4.Parse.parse_file_fresh includes_p4 source)
    with P4.Error.ParseError (at, message) ->
      Error (Diagnostic.error ~source:"p4" at message) in
  let* expected = match expected_path with
    | None -> Ok None
    | Some path ->
        (match Case_manifest.read_expected path with
        | Ok expected -> Ok (Some expected)
        | Error message -> Error (Diagnostic.error ~source:"oracle" Util.Source.no_region message)) in
  Ok { Case_obligation.source; expectation; expected; value }

let rec parse_cases includes_p4 = function
  | [] -> Ok []
  | entry :: rest ->
      let* case = parse_case includes_p4 entry in
      let* others = parse_cases includes_p4 rest in
      Ok (case :: others)

let run_program paths_spec includes_p4 path =
  let open Runtime.Sim.Signature in
  let diagnostic message =
    Diagnostic.error ~source:"oracle" Util.Source.no_region message in
  let lift = function
    | Ok value -> Ok value
    | Error error -> Error (diagnostic (P4spectec.Error.to_string error)) in
  let* spec_sim = lift (P4spectec.spec_of_mode SL_mode paths_spec) in
  let* simulator = lift (P4spectec.build_sim ~det:true spec_sim) in
  let (module Simulator : SIM) = simulator in
  Ok (Simulator.Interp.eval_program "Program_ok" includes_p4 path)

let oracle_output paths_spec spec_il includes_p4 path =
  let open Runtime.Sim.Signature in
  let diagnostic message =
    Diagnostic.error ~source:"oracle" Util.Source.no_region message in
  let* outcome = run_program paths_spec includes_p4 path in
  match outcome with
  | Pass [ value ] ->
      (try
        let env = Translator.build_env spec_il in
        let term = Case_obligation.translate_value env
          (Ast.Lean.Name "p4programIR") value in
        Ok (Printer.print_term [] term)
      with Translator.Unsupported_il diagnostic -> Error diagnostic)
  | Pass values ->
      Error (diagnostic (Printf.sprintf
        "Program_ok returned %d outputs; expected one" (List.length values)))
  | Fail (`Syntax diagnostic) -> Error diagnostic
  | Fail (`Runtime failure) -> Error (diagnostic_of_failure failure)

let check_rejection paths_spec includes_p4 path =
  let open Runtime.Sim.Signature in
  let* outcome = run_program paths_spec includes_p4 path in
  match outcome with
  | Fail (`Runtime (Unmatch _)) -> Ok "rejected"
  | Pass _ ->
      Error (Diagnostic.error ~source:"oracle" Util.Source.no_region
        ("Program_ok accepted " ^ path))
  | Fail (`Syntax diagnostic) -> Error diagnostic
  | Fail (`Runtime failure) -> Error (diagnostic_of_failure failure)

let read_batch_paths path =
  try
    let channel = open_in path in
    Fun.protect ~finally:(fun () -> close_in channel) (fun () ->
      let rec read paths = match input_line channel with
        | line ->
            let line = String.trim line in
            read (if line = "" then paths else line :: paths)
        | exception End_of_file -> Ok (List.rev paths)
      in
      read [])
  with Sys_error message ->
    Error (Diagnostic.error ~source:"oracle" Util.Source.no_region message)

let scan_batch paths_spec spec_il includes_p4 list_path =
  let open Runtime.Sim.Signature in
  let diagnostic message =
    Diagnostic.error ~source:"oracle" Util.Source.no_region message in
  let lift = function
    | Ok value -> Ok value
    | Error error -> Error (diagnostic (P4spectec.Error.to_string error)) in
  let* paths = read_batch_paths list_path in
  let* spec_sim = lift (P4spectec.spec_of_mode SL_mode paths_spec) in
  let* simulator = lift (P4spectec.build_sim ~det:true spec_sim) in
  let (module Simulator : SIM) = simulator in
  let env = Translator.build_env spec_il in
  let one_line text =
    String.map (function '\n' | '\r' | '\t' -> ' ' | char -> char) text in
  List.iter (fun path ->
    (* Each oracle input starts with an initialized runtime and empty caches. *)
    Interface.P4.Builtin_P4.init ();
    Simulator.Interp.clear ();
    let status, detail =
      try match Simulator.Interp.eval_program "Program_ok" includes_p4 path with
      | Pass [ value ] ->
          let term = Case_obligation.translate_value env
            (Ast.Lean.Name "p4programIR") value
            |> Printer.print_term [] in
          if String.contains term '\n' || String.contains term '\t' then
            "translation-error", "Lean output contains a tab or newline"
          else "accept", term
      | Pass values -> "bad-arity", string_of_int (List.length values)
      | Fail (`Runtime (Unmatch _)) -> "reject", ""
      | Fail (`Syntax diagnostic) ->
          "syntax", snd (Diagnostic.region_msg diagnostic)
      | Fail (`Runtime failure) ->
          "abort", snd (Diagnostic.region_msg (diagnostic_of_failure failure))
      with
      | Translator.Unsupported_il diagnostic ->
          "translation-error", snd (Diagnostic.region_msg diagnostic)
      | exn -> "crash", Printexc.to_string exn
    in
    print_endline (status ^ "\t" ^ path ^ "\t" ^ one_line detail);
    flush stdout) paths;
  Ok ()

let () =
  let arguments : string list = Array.to_list Sys.argv |> List.tl in
  let options = match parse_options arguments with
    | Ok options -> options
    | Error message -> prerr_endline message; exit 2
  in
  if options.executable &&
     (not options.ordered || options.obligations_only || options.emit_cases <> None ||
      options.dump_output <> None || options.check_rejection <> None || options.batch_cases <> None) then (
    prerr_endline "--executable requires ordered translation; it cannot combine with declarative, obligations-only, case export or oracle modes";
    exit 2);
  if options.paths_spec = [] ||
     (options.obligations_only && options.cases = []) then (
    prerr_endline usage;
    exit 2);
  if options.emit_cases <> None &&
     (options.cases = [] || not options.ordered || options.keep_going ||
      options.obligations_only || options.emit_modules <> None) then (
    prerr_endline "--emit-cases requires cases and complete ordered semantics; it cannot combine with --emit-modules or --obligations-only";
    exit 2);
  if options.keep_going && options.cases <> [] && not options.obligations_only then (
    prerr_endline
      "--keep-going cannot emit case propositions; use --obligations-only";
    exit 2);
  if options.emit_modules <> None && options.obligations_only then (
    prerr_endline "--emit-modules requires translated semantics";
    exit 2);
  if options.module_split_bytes <> None && options.emit_modules = None && options.emit_cases = None then (
    prerr_endline "--module-split-bytes requires --emit-modules or --emit-cases";
    exit 2);
  if options.case_range <> None && options.cases = [] then (
    prerr_endline "--case-range requires cases";
    exit 2);
  (match options.case_range with
  | Some (start, _) when start >= List.length options.cases ->
      prerr_endline "--case-range starts beyond the last case";
      exit 2
  | _ -> ());
  if (options.dump_output <> None || options.check_rejection <> None ||
      options.batch_cases <> None) &&
     (options.cases <> [] || options.obligations_only || options.keep_going ||
      options.emit_modules <> None || options.emit_cases <> None || options.module_split_bytes <> None ||
      options.case_range <> None ||
      List.length (List.filter Option.is_some
        [options.dump_output; options.check_rejection; options.batch_cases]) > 1) then (
    prerr_endline "oracle checks cannot be combined with cases or translation options";
    exit 2);
  let result, collected_report =
    Diagnostic.collect (fun () ->
        let* spec_il = Pass.elab options.paths_spec in
        match options.dump_output, options.check_rejection, options.batch_cases with
        | None, None, Some path ->
            let* () = scan_batch options.paths_spec spec_il
              options.includes_p4 path in
            Ok ("", [])
        | Some path, None, None ->
            let* output = oracle_output options.paths_spec spec_il
              options.includes_p4 path in
            Ok (output, [])
        | None, Some path, None ->
            let* result = check_rejection options.paths_spec
              options.includes_p4 path in
            Ok (result, [])
        | None, None, None ->
        if options.emit_cases <> None then (
          let* semantics = Pipeline.transpile ~ordered:true spec_il in
          let entries = Case_manifest.select options.case_range options.cases in
          try
            Case_export.emit ?module_split_bytes:options.module_split_bytes
              ~directory:(Option.get options.emit_cases) ~spec:spec_il ~semantics
              ~entries ~load:(fun entry -> match parse_case options.includes_p4 entry with
                | Ok case -> case | Error diagnostic -> raise (Translator.Unsupported_il diagnostic)) ();
            Ok (Printf.sprintf "Exported %d case propositions to %s" (List.length entries)
              (Option.get options.emit_cases), [])
          with
          | Translator.Unsupported_il diagnostic -> Error diagnostic
          | Sys_error message | Invalid_argument message ->
              Error (Diagnostic.error ~source:"cases" Util.Source.no_region message)
          | Unix.Unix_error (error, _, path) ->
              Error (Diagnostic.error ~source:"cases" Util.Source.no_region
                (path ^ ": " ^ Unix.error_message error)))
        else (
        let selected, start = match options.case_range with
          | None -> options.cases, 0
          | Some (start, count) ->
              List.filteri (fun index _ -> index >= start && index < start + count)
                options.cases,
              start
        in
        let* cases = parse_cases options.includes_p4 selected in
        let* obligations =
          try Ok (if cases = [] then "" else Case_obligation.render ~start spec_il cases)
          with Translator.Unsupported_il diagnostic -> Error diagnostic
        in
        if options.obligations_only then Ok (obligations, [])
        else if options.keep_going then
          let (lean_code, diagnostics) : string * Diagnostic.t list =
            Pipeline.transpile_all ~ordered:options.ordered ~executable:options.executable spec_il
          in
          Ok (Printer.append_obligations lean_code obligations,
              diagnostics)
        else
          let* lean_code = Pipeline.transpile ~ordered:options.ordered ~executable:options.executable spec_il in
          Ok (Printer.append_obligations lean_code obligations,
              []))
        | _ -> assert false)
  in
  let report : Diagnostic.Report.t =
    match result with
    | Ok (_, diagnostics) ->
        List.fold_left
          (fun report diagnostic ->
            Diagnostic.Report.merge report
              (Diagnostic.Report.singleton diagnostic))
          collected_report diagnostics
    | Error diagnostic ->
        Diagnostic.Report.merge collected_report
          (Diagnostic.Report.singleton diagnostic)
  in
  if not (Diagnostic.Report.is_empty report) then
    prerr_endline
      (Diagnostic.Render.render_report ~ansi:Diagnostic.Ansi.plain report);
  match result with
  | Ok (lean_code, _) ->
      (match options.emit_modules with
      | None -> if lean_code <> "" then print_endline lean_code
      | Some directory ->
          (try Module_writer.emit ?batch_bytes:options.module_split_bytes
            ~directory lean_code
          with
          | Sys_error message | Invalid_argument message ->
              prerr_endline message; exit 1
          | Unix.Unix_error (error, _, _) ->
              prerr_endline (Unix.error_message error); exit 1));
      if List.exists (fun (diagnostic : Diagnostic.t) -> diagnostic.severity = Diagnostic.Error)
          (Diagnostic.Report.to_sorted_list report) then exit 1
  | Error _ -> exit 1
