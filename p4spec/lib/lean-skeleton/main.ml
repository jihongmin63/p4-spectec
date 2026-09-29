let ( let* ) = Result.bind

let () =
  let arguments : string list = Array.to_list Sys.argv |> List.tl in
  let keep_going : bool = List.mem "--keep-going" arguments in
  (match List.find_opt
      (fun argument ->
        String.starts_with ~prefix:"--" argument && argument <> "--keep-going")
      arguments with
  | Some argument ->
      prerr_endline ("Unknown option: " ^ argument);
      exit 2
  | None -> ());
  let paths_spec : string list =
    List.filter (fun argument -> argument <> "--keep-going") arguments
  in
  if paths_spec = [] then (
    prerr_endline "Usage: lean-skeleton [--keep-going] <spec-path>...";
    exit 2);
  let result, collected_report =
    Diagnostic.collect (fun () ->
        let* spec_il = Pass.elab paths_spec in
        if keep_going then
          let (lean_code, diagnostics) : string * Diagnostic.t list =
            Pipeline.transpile_all spec_il
          in
          Ok (lean_code, diagnostics)
        else
          let* lean_code = Pipeline.transpile spec_il in
          Ok (lean_code, []))
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
