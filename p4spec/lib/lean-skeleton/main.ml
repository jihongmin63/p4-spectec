let ( let* ) = Result.bind

type options = {
  paths_spec : string list;
  includes_p4 : string list;
  cases : (Case_obligation.expectation * string * string option) list;
  keep_going : bool;
  fresh_exact_counter : bool;
  fresh_rollback : bool;
  obligations_only : bool;
  dump_output : string option;
  check_rejection : string option;
  batch_cases : string option;
  case_range : (int * int) option;
  dump_relation_graph : bool;
  relation_roots : string list;
}

let usage =
  "Usage: lean-skeleton [--keep-going] [--fresh-exact-counter | --fresh-rollback] [--obligations-only] \
   [--case P4 EXPECTED | --reject-case P4 | --manifest TSV]... \
   [--case-range START COUNT] \
   [--dump-output P4 | --check-rejection P4 | --batch-cases PATHS | \
    --dump-relation-graph] [--relation-root NAME]... \
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
                | ["abort-reject"; source] when source <> "" ->
                    Some (Case_obligation.AbortReject, source, None)
                | _ -> None
              in
              (match entry with
              | None ->
                  Error (Printf.sprintf "%s:%d: expected accept<TAB>path<TAB>expected, reject<TAB>path, or abort-reject<TAB>path"
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
    | "--fresh-exact-counter" :: rest ->
        loop { options with fresh_exact_counter = true } rest
    | "--fresh-rollback" :: rest -> loop { options with fresh_rollback = true } rest
    | "--dump-relation-graph" :: rest ->
        loop { options with dump_relation_graph = true } rest
    | "--relation-root" :: name :: rest when name <> "" ->
        loop { options with relation_roots = name :: options.relation_roots } rest
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
       "--relation-root" | "-I") :: [] -> Error usage
    | argument :: _ when String.starts_with ~prefix:"-" argument ->
        Error ("Unknown option: " ^ argument ^ "\n" ^ usage)
    | path :: rest ->
        loop { options with paths_spec = path :: options.paths_spec } rest
  in
  loop { paths_spec = []; includes_p4 = []; cases = [];
         keep_going = false; fresh_exact_counter = false; fresh_rollback = false;
         obligations_only = false; dump_output = None;
         check_rejection = None; batch_cases = None; case_range = None;
         dump_relation_graph = false; relation_roots = [] } arguments

let read_expected path =
  try
    let compressed = Filename.check_suffix path ".gz" in
    let channel = if compressed then
      Unix.open_process_args_in "gzip" [|"gzip"; "-dc"; "--"; path|]
    else open_in_bin path in
    let buffer = Buffer.create 4096 in
    let bytes = Bytes.create 16384 in
    let rec read () =
      let count = input channel bytes 0 (Bytes.length bytes) in
      if count > 0 then (Buffer.add_subbytes buffer bytes 0 count; read ()) in
    read ();
    let status = if compressed then Unix.close_process_in channel
      else (close_in channel; Unix.WEXITED 0) in
    match status with
    | Unix.WEXITED 0 ->
        let expected = Buffer.contents buffer |> String.trim in
        if expected = "" then Error ("empty expected output: " ^ path)
        else Ok expected
    | _ -> Error ("cannot decompress expected output: " ^ path)
  with
  | Sys_error message -> Error message
  | Unix.Unix_error (error, _, _) -> Error (Unix.error_message error)

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
      Ok ({ Case_obligation.source; expectation; expected; value;
            fresh_context = None } :: others)

let program_oracle paths_spec includes_p4 =
  let open Runtime.Sim.Signature in
  let diagnostic message =
    Diagnostic.error ~source:"oracle" Util.Source.no_region message in
  let lift = function
    | Ok value -> Ok value
    | Error error -> Error (diagnostic (P4spectec.Error.to_string error)) in
  let* spec_sim = lift (P4spectec.spec_of_mode SL_mode paths_spec) in
  let* simulator = lift (P4spectec.build_sim ~det:true spec_sim) in
  let (module Simulator : SIM) = simulator in
  Ok (fun path ->
    Interface.P4.Builtin_P4.init ();
    Simulator.Interp.eval_program "Program_ok" includes_p4 path)

let run_program paths_spec includes_p4 path =
  let* evaluate = program_oracle paths_spec includes_p4 in
  Ok (evaluate path)

let rec text_values (value : Runtime.Value.t) =
  let recurse values = List.concat_map text_values values in
  match value.it with
  | TextV name -> [value.note.vid, name]
  | StructV fields -> recurse (List.map snd fields)
  | CaseV notation -> recurse (Domain.Mixfix.args notation)
  | TupleV values | ListV values -> recurse values
  | OptV (Some value) -> text_values value
  | BoolV _ | NumV _ | OptV None | FuncV _ | ExternV _ -> []

let fresh_context env evaluate (case : Case_obligation.case) =
  let open Runtime.Sim.Signature in
  let diagnostic message =
    Diagnostic.error ~source:"oracle" Util.Source.no_region message in
  let outcome, allocated = Interface.P4.with_fresh_allocations (fun () ->
    evaluate case.source) in
  match outcome with
  | Pass [value] ->
      (try
        let observed = Case_obligation.translate_value env
          (Ast.Lean.Name "p4programIR") value |> Printer.print_term [] in
        if case.expected <> Some observed then
          Error (diagnostic ("expected output differs from the exact interpreter for "
            ^ case.source ^ "; capture it with --dump-output before nominal case generation"))
        else
          let allocation_ids = Hashtbl.create (List.length allocated) in
          List.iter (fun (value : Runtime.Value.t) ->
            Hashtbl.replace allocation_ids value.note.vid ()) allocated;
          let allocated_names = List.concat_map text_values allocated |> List.map snd in
          let ordinary_output = text_values value |> List.filter_map (fun (id, name) ->
            if Hashtbl.mem allocation_ids id then None else Some name) in
          let protected = List.map snd (text_values case.value) @ ordinary_output
            |> List.sort_uniq String.compare in
          Ok { case with fresh_context = Some (allocated_names, protected) }
      with Translator.Unsupported_il diagnostic -> Error diagnostic)
  | Pass values -> Error (diagnostic (Printf.sprintf
      "Program_ok returned %d outputs; expected one" (List.length values)))
  | Fail (`Syntax diagnostic) -> Error diagnostic
  | Fail (`Runtime failure) -> Error (diagnostic_of_failure failure)

let enrich_fresh_cases paths_spec spec_il includes_p4 cases =
  if not (List.exists (fun (case : Case_obligation.case) ->
    case.expectation = Accept) cases) then Ok cases else
  let* evaluate = program_oracle paths_spec includes_p4 in
  let env = Translator.build_env spec_il in
  let rec enrich = function
    | [] -> Ok []
    | (case : Case_obligation.case) :: rest ->
        let* case = match case.expectation with
          | Accept -> fresh_context env evaluate case
          | Reject | AbortReject -> Ok case in
        let* rest = enrich rest in
        Ok (case :: rest)
  in enrich cases

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
    (* Interp.clear resets caches, but not the interface's fresh_typeId counter. *)
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
  if options.paths_spec = [] ||
     (options.obligations_only && options.cases = []) then (
    prerr_endline usage;
    exit 2);
  if options.fresh_exact_counter && options.fresh_rollback then (
    prerr_endline "--fresh-exact-counter and --fresh-rollback are distinct modes";
    exit 2);
  if options.relation_roots <> []
     && (options.fresh_exact_counter || options.fresh_rollback) then (
    prerr_endline
      "--relation-root is available only in the default relation-local mode";
    exit 2);
  if options.relation_roots <> [] && options.keep_going then (
    prerr_endline "--relation-root cannot be combined with --keep-going";
    exit 2);
  if options.keep_going && options.cases <> [] && not options.obligations_only then (
    prerr_endline
      "--keep-going cannot emit case propositions; use --obligations-only";
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
     (options.cases <> [] || options.obligations_only || options.keep_going
      || options.fresh_exact_counter || options.fresh_rollback ||
      options.case_range <> None || options.relation_roots <> [] ||
      List.length (List.filter Option.is_some
        [options.dump_output; options.check_rejection; options.batch_cases]) > 1) then (
    prerr_endline "oracle checks cannot be combined with cases or translation options";
    exit 2);
  if options.dump_relation_graph &&
     (options.cases <> [] || options.obligations_only || options.keep_going
      || options.fresh_exact_counter || options.fresh_rollback || options.case_range <> None
      || options.relation_roots <> []
      || options.dump_output <> None || options.check_rejection <> None
      || options.batch_cases <> None) then (
    prerr_endline
      "--dump-relation-graph cannot be combined with cases, oracle checks, or translation modes";
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
        | None, None, None when options.dump_relation_graph ->
            let* graph = Pipeline.relation_graph spec_il in
            Ok (graph, [])
        | None, None, None ->
        let selected, start = match options.case_range with
          | None -> options.cases, 0
          | Some (start, count) ->
              List.filteri (fun index _ -> index >= start && index < start + count)
                options.cases,
              start
        in
        let* cases = parse_cases options.includes_p4 selected in
        (* Both nominal modes compare accepted results up to one whole-output
           alpha renaming.  Exact-counter remains concrete by construction. *)
        let* cases = if not options.fresh_exact_counter then
          enrich_fresh_cases options.paths_spec spec_il options.includes_p4 cases
          else Ok cases in
        let* obligations =
          try Ok (if cases = [] then "" else Case_obligation.render ~start spec_il cases)
          with Translator.Unsupported_il diagnostic -> Error diagnostic
        in
        let mode = if options.fresh_rollback then Pipeline.FreshRollback
          else if options.fresh_exact_counter then Pipeline.FreshExactCounter
          else Pipeline.RelationLocal in
        if options.obligations_only then Ok (obligations, [])
        else if options.keep_going then
          let (lean_code, diagnostics) : string * Diagnostic.t list =
            Pipeline.transpile_all ~mode spec_il
          in
          Ok ((if obligations = "" then lean_code else lean_code ^ "\n\n" ^ obligations),
              diagnostics)
        else
          let* lean_code = Pipeline.transpile ~mode
            ~relation_roots:(List.rev options.relation_roots) spec_il in
          Ok ((if obligations = "" then lean_code else lean_code ^ "\n\n" ^ obligations),
              [])
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
      if lean_code <> "" then print_endline lean_code;
      if List.exists (fun (diagnostic : Diagnostic.t) -> diagnostic.severity = Diagnostic.Error)
          (Diagnostic.Report.to_sorted_list report) then exit 1
  | Error _ -> exit 1
