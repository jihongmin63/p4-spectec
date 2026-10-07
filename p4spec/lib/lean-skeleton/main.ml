let ( let* ) = Result.bind

type options = {
  paths_spec : string list;
  includes_p4 : string list;
  cases : (Case_obligation.expectation * string * string option) list;
  keep_going : bool;
  obligations_only : bool;
  dump_output : string option;
  check_rejection : string option;
}

let usage =
  "Usage: lean-skeleton [--keep-going] [--obligations-only] \
   [--case P4 EXPECTED | --reject-case P4 | --manifest TSV]... \
   [--dump-output P4 | --check-rejection P4] \
   [-I DIR]... <spec-path>..."

let read_manifest path =
  try
    let channel = open_in path in
    Fun.protect ~finally:(fun () -> close_in channel) (fun () ->
      let rec read line_number cases =
        match input_line channel with
        | line ->
            let line = String.trim line in
            if line = "" || String.starts_with ~prefix:"#" line then
              read (line_number + 1) cases
            else
              let entry = match String.split_on_char '\t' line with
                | ["accept"; source; expected]
                  when source <> "" && expected <> "" ->
                    Some (Case_obligation.Accept, source, Some expected)
                | ["reject"; source] when source <> "" ->
                    Some (Case_obligation.Reject, source, None)
                | _ -> None
              in
              (match entry with
              | None ->
                  Error (Printf.sprintf "%s:%d: expected accept<TAB>path<TAB>expected or reject<TAB>path"
                    path line_number)
              | Some (expectation, source, expected) ->
                  let relative name = if Filename.is_relative name then
                    Filename.concat (Filename.dirname path) name else name in
                  read (line_number + 1)
                    ((expectation, relative source, Option.map relative expected)
                     :: cases))
        | exception End_of_file -> Ok (List.rev cases)
      in
      read 1 [])
  with Sys_error message -> Error message

let parse_options arguments =
  let rec loop options = function
    | [] -> Ok { options with
        paths_spec = List.rev options.paths_spec;
        includes_p4 = List.rev options.includes_p4;
        cases = List.rev options.cases }
    | "--keep-going" :: rest -> loop { options with keep_going = true } rest
    | "--obligations-only" :: rest ->
        loop { options with obligations_only = true } rest
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
    | "--manifest" :: path :: rest ->
        let* cases = read_manifest path in
        loop { options with cases = List.rev_append cases options.cases } rest
    | "-I" :: path :: rest ->
        loop { options with includes_p4 = path :: options.includes_p4 } rest
    | ("--case" | "--reject-case" | "--manifest" | "--dump-output" |
       "--check-rejection" | "-I") :: [] -> Error usage
    | argument :: _ when String.starts_with ~prefix:"-" argument ->
        Error ("Unknown option: " ^ argument ^ "\n" ^ usage)
    | path :: rest ->
        loop { options with paths_spec = path :: options.paths_spec } rest
  in
  loop { paths_spec = []; includes_p4 = []; cases = [];
         keep_going = false; obligations_only = false; dump_output = None;
         check_rejection = None } arguments

let read_expected path =
  try
    let channel = open_in_bin path in
    Fun.protect ~finally:(fun () -> close_in channel) (fun () ->
      let expected = really_input_string channel (in_channel_length channel)
        |> String.trim in
      if expected = "" then Error ("empty expected output: " ^ path)
      else Ok expected)
  with Sys_error message -> Error message

let rec parse_cases includes_p4 = function
  | [] -> Ok []
  | (expectation, source, expected_path) :: rest ->
      let* value =
        try Ok (P4.Parse.parse_file_fresh includes_p4 source)
        with P4.Error.ParseError (at, message) ->
          Error (Diagnostic.error ~source:"p4" at message)
      in
      let* expected = match expected_path with
        | None -> Ok None
        | Some path ->
            (match read_expected path with
            | Ok expected -> Ok (Some expected)
            | Error message ->
                Error (Diagnostic.error ~source:"oracle" Util.Source.no_region message))
      in
      let* others = parse_cases includes_p4 rest in
      Ok ({ Case_obligation.source; expectation; expected; value } :: others)

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

let () =
  let arguments : string list = Array.to_list Sys.argv |> List.tl in
  let options = match parse_options arguments with
    | Ok options -> options
    | Error message -> prerr_endline message; exit 2
  in
  if options.paths_spec = [] ||
     (options.obligations_only && options.cases = []) then (
    prerr_endline usage;
    exit 2);
  if options.keep_going && options.cases <> [] && not options.obligations_only then (
    prerr_endline
      "--keep-going cannot emit case propositions; use --obligations-only";
    exit 2);
  if (options.dump_output <> None || options.check_rejection <> None) &&
     (options.cases <> [] || options.obligations_only || options.keep_going ||
      (options.dump_output <> None && options.check_rejection <> None)) then (
    prerr_endline "oracle checks cannot be combined with cases or translation options";
    exit 2);
  let result, collected_report =
    Diagnostic.collect (fun () ->
        let* spec_il = Pass.elab options.paths_spec in
        match options.dump_output, options.check_rejection with
        | Some path, None ->
            let* output = oracle_output options.paths_spec spec_il
              options.includes_p4 path in
            Ok (output, [])
        | None, Some path ->
            let* result = check_rejection options.paths_spec
              options.includes_p4 path in
            Ok (result, [])
        | None, None ->
        let* cases = parse_cases options.includes_p4 options.cases in
        let* obligations =
          try Ok (if cases = [] then "" else Case_obligation.render spec_il cases)
          with Translator.Unsupported_il diagnostic -> Error diagnostic
        in
        if options.obligations_only then Ok (obligations, [])
        else if options.keep_going then
          let (lean_code, diagnostics) : string * Diagnostic.t list =
            Pipeline.transpile_all spec_il
          in
          Ok ((if obligations = "" then lean_code else lean_code ^ "\n\n" ^ obligations),
              diagnostics)
        else
          let* lean_code = Pipeline.transpile spec_il in
          Ok ((if obligations = "" then lean_code else lean_code ^ "\n\n" ^ obligations),
              [])
        | Some _, Some _ -> assert false)
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
      print_endline lean_code;
      if List.exists (fun (diagnostic : Diagnostic.t) -> diagnostic.severity = Diagnostic.Error)
          (Diagnostic.Report.to_sorted_list report) then exit 1
  | Error _ -> exit 1
