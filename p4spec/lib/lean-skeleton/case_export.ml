(** Stream an indexed corpus into an atomic, independently importable package. *)
let write path text =
  let channel = open_out_bin path in
  Fun.protect ~finally:(fun () -> close_out channel) (fun () -> output_string channel text)

let rec mkdir path =
  if not (Sys.file_exists path) then (mkdir (Filename.dirname path); Unix.mkdir path 0o755)

let rec remove_owned path =
  if (Unix.lstat path).Unix.st_kind = Unix.S_DIR then (
    Array.iter (fun name -> remove_owned (Filename.concat path name)) (Sys.readdir path);
    Unix.rmdir path)
  else Unix.unlink path

let quote_tsv value =
  if String.exists (fun c -> c = '\t' || c = '\n' || c = '\r' || c = '"') value then
    "\"" ^ String.concat "\"\"" (String.split_on_char '"' value) ^ "\"" else value

let url value =
  let buffer = Buffer.create (String.length value) in
  String.iter (fun c -> if Char.code c < 33 || String.contains "<>|()[]#%\\\"" c then
      Buffer.add_string buffer (Printf.sprintf "%%%02X" (Char.code c))
    else Buffer.add_char buffer c) value;
  Buffer.contents buffer

let md value = String.concat "\\|" (String.split_on_char '|' value)

let emit ?module_split_bytes ~directory ~spec ~semantics ~entries ~load () =
  if Sys.file_exists directory &&
      (not (Sys.is_directory directory) || Sys.readdir directory <> [||]) then
    invalid_arg ("case output directory is not empty: " ^ directory);
  let parent = Filename.dirname directory in
  mkdir parent;
  let stage = Filename.temp_file ~temp_dir:parent ".typecheck-cases-" ".stage" in
  Sys.remove stage;
  Unix.mkdir stage 0o755;
  try
    Module_writer.emit ?batch_bytes:module_split_bytes
      ~directory:(Filename.concat stage "semantics") semantics;
    let cases_path = Filename.concat stage "cases" in
    Unix.mkdir cases_path 0o755;
    let env = Translator.build_env spec in
    let context = Case_obligation.context semantics in
    let options = "set_option autoImplicit false\nset_option maxRecDepth 16384\nset_option maxHeartbeats 0\n\n" in
    let table = Buffer.create 4096 and report = Buffer.create 4096 in
    Buffer.add_string table "case_id\texpectation\tsource\toracle\tdata_module\tgoal_module\tgoal_kind\n";
    Buffer.add_string report "# Type-check corpus translations\n\nEach proposition is a proof target. Declaration checking does not prove it.\nAccepted targets preserve exact IRs, including fresh names, and output uniqueness.\nRejected targets assert absence of a successful output. An abort-reject is a rejection conjecture; an interpreter abort does not establish it.\n\n| ID | Recorded result | P4 source | Data | Proposition | Logical target |\n|---:|---|---|---|---|---|\n";
    List.iter (fun (index, entry) ->
      let case : Case_obligation.case = load entry in
      let data_name = Printf.sprintf "Case%04dData" index in
      let goal_name = Printf.sprintf "Case%04d" index in
      write (Filename.concat cases_path (data_name ^ ".lean"))
        ("import SpecTecAll\n\n" ^ options ^ Case_obligation.wrap ~context
          (Case_obligation.data ~noncomputable:true env index case) ^ "\n");
      write (Filename.concat cases_path (goal_name ^ ".lean"))
        ("import " ^ data_name ^ "\n\n" ^ options ^ Case_obligation.wrap ~context
          ("-- Proof target: " ^ Case_manifest.goal_kind case.expectation ^ "\n" ^ Case_obligation.goal index case) ^ "\n");
      let _, source, oracle = entry in
      let source = Unix.realpath source in
      let oracle = match oracle with Some path -> Unix.realpath path | None -> "" in
      Buffer.add_string table (String.concat "\t" (List.map quote_tsv
        [string_of_int index; Case_manifest.label case.expectation; source; oracle;
         data_name ^ ".lean"; goal_name ^ ".lean"; Case_manifest.goal_kind case.expectation]) ^ "\n");
      let target = Case_obligation.proposition index case.expectation
        |> String.split_on_char '\n' |> String.concat " " in
      Buffer.add_string report (Printf.sprintf "| %d | %s | [%s](%s) | [%s](cases/%s.lean) | [%s](cases/%s.lean) | `%s` |\n"
        index (Case_manifest.label case.expectation) (md (Filename.basename source)) (url source)
        data_name data_name goal_name goal_name (md target))) entries;
    write (Filename.concat stage "index.tsv") (Buffer.contents table);
    write (Filename.concat stage "index.md") (Buffer.contents report);
    Unix.rename stage directory
  with exn -> remove_owned stage; raise exn
