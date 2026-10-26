(* Adapted from 7c1d9da1: preserve declaration-group boundaries instead of
   splitting reified semantic programs, evaluators, or inversion theorems. *)

type phase = Core | Support | Between | Declaration of int | Cases
type component = { source : string; context : string }

let marker line =
  match String.split_on_char ':' line with
  | [ "-- SpecTecModule"; "decl"; boundary; number ] ->
      Option.map (fun index -> boundary, index) (int_of_string_opt number)
  | _ -> None

let write_file path contents =
  let channel = open_out_bin path in
  Fun.protect ~finally:(fun () -> close_out channel) (fun () ->
    output_string channel contents)

let emit ?(batch_size = 32) ?(batch_bytes = 2_000_000)
    ~(directory : string) (source : string) : unit =
  if batch_size < 1 then invalid_arg "module batch size must be positive";
  if batch_bytes < 1 then invalid_arg "module byte budget must be positive";
  if Sys.file_exists directory then (
    if not (Sys.is_directory directory) then
      invalid_arg ("module output is not a directory: " ^ directory);
    if Sys.readdir directory <> [||] then
      invalid_arg ("module output directory is not empty: " ^ directory))
  else Unix.mkdir directory 0o755;
  let core = Buffer.create 16384 in
  let support = Buffer.create 1024 in
  let body = Buffer.create 4096 in
  let cases = Buffer.create 4096 in
  let context = Buffer.create 256 in
  let component_context = ref "" in
  let components = ref [] in
  let phase = ref Core in
  let add buffer line = Buffer.add_string buffer line; Buffer.add_char buffer '\n' in
  let add_context line =
    if String.starts_with ~prefix:"variable [" line then add context line in
  List.iter (fun line ->
    match marker line with
    | Some ("begin", index) when !phase = Support || !phase = Between ->
        if index <> List.length !components then
          invalid_arg "nonsequential declaration module marker";
        component_context := Buffer.contents context;
        Buffer.clear body;
        phase := Declaration index
    | Some ("end", index) when !phase = Declaration index ->
        components := { source = Buffer.contents body;
                        context = !component_context } :: !components;
        phase := Between
    | Some _ -> invalid_arg "malformed declaration module marker order"
    | None ->
        (match !phase, line with
        | Core, "namespace SpecTec" -> phase := Support
        | (Support | Between), "end SpecTec" -> phase := Cases
        | Core, _ -> add core line
        | Support, _ -> add support line; add_context line
        | Between, "" -> ()
        | Between, _ -> invalid_arg ("unexpected code between declaration groups: " ^ line)
        | Declaration _, _ -> add body line; add_context line
        | Cases, _ -> add cases line))
    (String.split_on_char '\n' source);
  if !phase <> Cases then
    invalid_arg "generated Lean source has no closing SpecTec namespace";
  let path name = Filename.concat directory (name ^ ".lean") in
  let options = "set_option autoImplicit false\n"
    ^ "set_option linter.unusedVariables false\n"
    ^ "set_option linter.unusedSectionVars false\n"
    ^ "set_option maxHeartbeats 0\n"
    ^ (String.split_on_char '\n' source
       |> List.filter (String.starts_with ~prefix:"set_option maxRecDepth ")
       |> String.concat "\n") ^ "\n\n" in
  write_file (path "SpecTecCore") (Buffer.contents core);
  write_file (path "SpecTecSupport")
    ("import SpecTecCore\n\n" ^ options ^ "namespace SpecTec\n\n"
     ^ Buffer.contents support ^ "\nend SpecTec\n");
  let rec batches acc current count bytes = function
    | [] -> List.rev (if current = [] then acc else List.rev current :: acc)
    | component :: rest when count = batch_size ||
        (count > 0 && bytes + String.length component.source > batch_bytes) ->
        batches (List.rev current :: acc) [component] 1
          (String.length component.source) rest
    | component :: rest ->
        batches acc (component :: current) (count + 1)
          (bytes + String.length component.source) rest in
  let batches = batches [] [] 0 0 (List.rev !components) in
  let previous = ref "SpecTecSupport" in
  List.iteri (fun index batch ->
    let name = "SpecTecDecl" ^ Printf.sprintf "%04d" index in
    let contents = String.concat "\n\n" (List.map (fun component -> component.source) batch) in
    let inherited_context = (List.hd batch).context in
    write_file (path name)
      ("import " ^ !previous ^ "\n\n" ^ options
       ^ "namespace SpecTec\n\n" ^ inherited_context ^ "\n" ^ contents
       ^ "\nend SpecTec\n");
    previous := name) batches;
  write_file (path "SpecTecAll") ("import " ^ !previous ^ "\n");
  write_file (path "SpecTecProofs") ("import SpecTecAll\n");
  write_file (path "SpecTecCases")
    ("import SpecTecAll\n\n" ^ options ^ Buffer.contents cases)
