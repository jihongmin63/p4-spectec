type phase = Core | Support | Between | Sem of int | Eval of int
  | Inv of int | Cases

type component = {
  semantics : Buffer.t;
  evaluation : Buffer.t;
  inversions : Buffer.t;
}

let marker line =
  match String.split_on_char ':' line with
  | ["-- SpecTecModule"; kind; boundary; number] ->
      Option.map (fun index -> kind, boundary, index) (int_of_string_opt number)
  | _ -> None

let write_file path contents =
  let channel = open_out_bin path in
  Fun.protect ~finally:(fun () -> close_out channel) (fun () ->
    output_string channel contents)

let starts prefix value = String.starts_with ~prefix value

let split_large_component ~(budget : int) (source : string) : string list =
  if String.length source <= budget then [source] else
  let lines = Array.of_list (String.split_on_char '\n' source) in
  let length = Array.length lines in
  let first predicate =
    let rec find index =
      if index = length then invalid_arg "large SCC has no expected boundary"
      else if predicate lines.(index) then index else find (index + 1) in
    find 0 in
  let local_start = first (fun line ->
    starts "namespace «" line && String.ends_with ~suffix:":Semantics»" line) in
  let local_name = String.sub lines.(local_start) 10
    (String.length lines.(local_start) - 10) in
  let local_end = first (String.equal ("end " ^ local_name)) in
  if local_end <= local_start then invalid_arg "malformed large SCC namespace";
  let slice first last = Array.to_list (Array.sub lines first (last - first)) in
  let prefix = slice 0 local_start in
  let sectioned = List.exists (String.equal "section") prefix in
  let finish = if sectioned then "\nend\n" else "" in
  let pack ~boundary body =
    let body = Array.of_list body in
    let count = Array.length body in
    let block first last = Array.sub body first (last - first)
      |> Array.to_list |> String.concat "\n" in
    let rec blocks start index acc =
      if index = count then List.rev
        (List.filter (fun block -> block <> "")
          (block start index :: acc))
      else if index > start && boundary body index then
        blocks index (index + 1) (block start index :: acc)
      else blocks start (index + 1) acc in
    let blocks = blocks 0 0 [] in
    let rec group chunks current bytes = function
      | [] -> List.rev (if current = [] then chunks else
          String.concat "\n" (List.rev current) :: chunks)
      | block :: rest ->
          let size = String.length block in
          if current <> [] && bytes + size > budget then
            group (String.concat "\n" (List.rev current) :: chunks)
              [block] size rest
          else group chunks (block :: current) (bytes + size) rest in
    group [] [] 0 blocks in
  let local_body = slice (local_start + 1) local_end in
  let local_boundary values index =
    let line = values.(index) in
    starts "def rule_" line || starts "inductive InProgram" line in
  let local_chunks = pack ~boundary:local_boundary local_body in
  let public_end = if sectioned then
      let rec last_nonempty index =
        if index <= local_end then invalid_arg "missing SCC section end"
        else if String.trim lines.(index) = "" then last_nonempty (index - 1)
        else index in
      let index = last_nonempty (length - 1) in
      if lines.(index) <> "end" then invalid_arg "missing SCC section end";
      index
    else length in
  let public_body = slice (local_end + 1) public_end in
  let public_boundary values index =
    let line = values.(index) in
    let previous = values.(index - 1) in
    starts "@[" line ||
    ((starts "def " line || starts "theorem " line ||
      starts "abbrev " line || starts "instance " line) &&
     not (starts "@[" previous)) in
  let public_chunks = pack ~boundary:public_boundary public_body in
  let preamble = String.concat "\n" prefix in
  let local_chunks = List.map (fun body ->
    preamble ^ "\n" ^ lines.(local_start) ^ "\n" ^ body
    ^ "\nend " ^ local_name ^ finish) local_chunks in
  let public_chunks = List.map (fun body ->
    preamble ^ "\n" ^ body ^ finish) public_chunks in
  local_chunks @ public_chunks

let split_inversion_component ~(budget : int) (source : string) : string list =
  if String.length source <= budget then [source] else
  let lines = Array.of_list (String.split_on_char '\n' source) in
  let length = Array.length lines in
  let first =
    let rec seek index =
      if index = length then invalid_arg "inversion module has no declaration"
      else if starts "theorem " lines.(index) ||
              starts "def " lines.(index) then index
      else seek (index + 1) in
    seek 0 in
  let footer_start =
    let rec seek index =
      if index < first then length
      else if String.trim lines.(index) = "" then seek (index - 1)
      else if lines.(index) = "end" then index else length in
    seek (length - 1) in
  let slice start stop = Array.sub lines start (stop - start)
    |> Array.to_list |> String.concat "\n" in
  let prefix = slice 0 first in
  let footer = slice footer_start length in
  let stop = footer_start in
  let rec blocks start index acc =
    if index = stop then List.rev (slice start stop :: acc)
    else if index > start &&
        (starts "theorem " lines.(index) || starts "def " lines.(index)) then
      blocks index (index + 1) (slice start index :: acc)
    else blocks start (index + 1) acc in
  let blocks = blocks first first [] in
  let overhead = String.length prefix + String.length footer + 4 in
  let rec group acc current bytes = function
    | [] -> List.rev (if current = [] then acc else
        (prefix ^ "\n" ^ String.concat "\n" (List.rev current)
         ^ "\n" ^ footer) :: acc)
    | block :: rest when current <> [] &&
        overhead + bytes + String.length block > budget ->
        let chunk = prefix ^ "\n" ^ String.concat "\n" (List.rev current)
          ^ "\n" ^ footer in
        group (chunk :: acc) [block] (String.length block) rest
    | block :: rest ->
        group acc (block :: current) (bytes + String.length block) rest in
  group [] [] 0 blocks

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
  let support = Buffer.create 16384 in
  let cases = Buffer.create 4096 in
  let components = ref [] in
  let phase = ref Core in
  let add buffer line = Buffer.add_string buffer line; Buffer.add_char buffer '\n' in
  let component index =
    match List.nth_opt !components index with
    | Some value -> value
    | None -> invalid_arg "nonsequential SCC module marker" in
  let lines = String.split_on_char '\n' source in
  let first_component = lines |> List.mapi (fun index line -> index, line)
    |> List.find_opt (fun (_, line) -> marker line = Some ("sem", "begin", 0))
    |> Option.map fst
    |> Option.value ~default:(List.length lines) in
  let root_namespace = lines |> List.mapi (fun index line -> index, line)
    |> List.filter_map (fun (index, line) ->
         if index < first_component && line = "namespace SpecTec"
         then Some index else None)
    |> List.rev |> function
       | index :: _ -> index
       | [] -> invalid_arg "missing root SpecTec namespace" in
  List.iteri (fun line_index line ->
    match marker line with
    | Some ("sem", "begin", index) when !phase = Support || !phase = Between ->
        if index <> List.length !components then
          invalid_arg "nonsequential SCC module marker";
        components := !components @ [{ semantics = Buffer.create 4096;
                                     evaluation = Buffer.create 4096;
                                     inversions = Buffer.create 1024 }];
        phase := Sem index
    | Some ("sem", "end", index) when !phase = Sem index ->
        phase := Between
    | Some ("eval", "begin", index) when !phase = Between ->
        ignore (component index);
        phase := Eval index
    | Some ("eval", "end", index) when !phase = Eval index ->
        phase := Between
    | Some ("inv", "begin", index) when !phase = Between ->
        ignore (component index);
        phase := Inv index
    | Some ("inv", "end", index) when !phase = Inv index ->
        phase := Between
    | Some _ -> invalid_arg "malformed SCC module marker order"
    | None ->
        (match !phase, line with
        | Core, "namespace SpecTec" when line_index = root_namespace ->
            phase := Support;
            add support line
        | (Support | Between), "end SpecTec" -> phase := Cases
        | Core, _ -> add core line
        | Support, _ -> add support line
        | Between, "" -> ()
        | Between, _ -> invalid_arg ("unexpected code between SCC modules: " ^ line)
        | Sem index, _ -> add (component index).semantics line
        | Eval index, _ -> add (component index).evaluation line
        | Inv index, _ -> add (component index).inversions line
        | Cases, _ -> add cases line))
    lines;
  if !phase <> Cases then invalid_arg "generated Lean source has no closing SpecTec namespace";
  let path name = Filename.concat directory (name ^ ".lean") in
  let options = "set_option autoImplicit false\n"
    ^ "set_option linter.unusedVariables false\n"
    ^ "set_option linter.unusedSectionVars false\n"
    ^ "set_option maxHeartbeats 0\n\n" in
  write_file (path "SpecTecCore") (Buffer.contents core);
  write_file (path "SpecTecSupport")
    ("import SpecTecCore\n\n" ^ options ^ Buffer.contents support
     ^ "\nend SpecTec\n");
  let component_bytes component =
    Buffer.length component.semantics + Buffer.length component.evaluation in
  let rec batches acc current count bytes = function
    | [] -> List.rev (if current = [] then acc else List.rev current :: acc)
    | component :: rest when count = batch_size ||
        (count > 0 && bytes + component_bytes component > batch_bytes) ->
        batches (List.rev current :: acc) [component] 1
          (component_bytes component) rest
    | component :: rest ->
        batches acc (component :: current) (count + 1)
          (bytes + component_bytes component) rest
  in
  let batches = batches [] [] 0 0 !components in
  List.iteri (fun index batch ->
    let number = Printf.sprintf "%04d" index in
    let sem_name = "SpecTecScc" ^ number in
    let eval_name = "SpecTecEval" ^ number in
    let sem_import = if index = 0 then "SpecTecSupport"
      else "SpecTecScc" ^ Printf.sprintf "%04d" (index - 1) in
    let semantics = String.concat "\n\n" (List.map (fun component ->
        Buffer.contents component.semantics ^ "\n\n"
        ^ Buffer.contents component.evaluation) batch) in
    let fragments = match batch with
      | [component] -> split_large_component ~budget:batch_bytes
          (Buffer.contents component.semantics)
          |> (function [_] -> [semantics] | fragments -> fragments)
      | _ -> [semantics] in
    let sem_import = if List.length fragments = 1 then sem_import else
      let previous = ref sem_import in
      List.iteri (fun part contents ->
        let name = "SpecTecPart" ^ number ^ "_"
          ^ Printf.sprintf "%04d" part in
        write_file (path name)
          ("import " ^ !previous ^ "\n\n" ^ options
           ^ "namespace SpecTec\n\n" ^ contents ^ "\nend SpecTec\n");
        previous := name) fragments;
      !previous in
    write_file (path sem_name)
      (if List.length fragments = 1 then
         "import " ^ sem_import ^ "\n\n" ^ options
         ^ "namespace SpecTec\n\n" ^ semantics ^ "\nend SpecTec\n"
       else "import " ^ sem_import ^ "\n\n" ^ options ^ "namespace SpecTec\n\n"
         ^ Buffer.contents (List.hd batch).evaluation ^ "\nend SpecTec\n");
    write_file (path eval_name) ("import " ^ sem_name ^ "\n"))
    batches;
  let aggregate_import = match List.length batches with
    | 0 -> "SpecTecSupport"
    | count -> "SpecTecEval" ^ Printf.sprintf "%04d" (count - 1) in
  write_file (path "SpecTecAll") ("import " ^ aggregate_import ^ "\n");
  let semantic_import = match List.length batches with
    | 0 -> "SpecTecSupport"
    | count -> "SpecTecScc" ^ Printf.sprintf "%04d" (count - 1) in
  let proof_budget = min batch_bytes 1_000_000 in
  let inversion_components = List.filter_map (fun component ->
    let contents = Buffer.contents component.inversions in
    if String.trim contents = "-- no declarations" then None
    else Some contents) !components
    |> List.concat_map (split_inversion_component ~budget:proof_budget) in
  let rec inversion_batches acc current bytes = function
    | [] -> List.rev (if current = [] then acc else List.rev current :: acc)
    | contents :: rest when current <> [] &&
        bytes + String.length contents > proof_budget ->
        inversion_batches (List.rev current :: acc) [contents]
          (String.length contents) rest
    | contents :: rest ->
        inversion_batches acc (contents :: current)
          (bytes + String.length contents) rest in
  let inversion_batches = inversion_batches [] [] 0 inversion_components in
  List.iteri (fun index batch ->
    let name = "SpecTecInversion" ^ Printf.sprintf "%04d" index in
    let previous = if index = 0 then semantic_import else
      "SpecTecInversion" ^ Printf.sprintf "%04d" (index - 1) in
    write_file (path name)
      ("import " ^ previous ^ "\n\n" ^ options ^ "namespace SpecTec\n\n"
       ^ String.concat "\n\n" batch ^ "\nend SpecTec\n"))
    inversion_batches;
  let proof_import = match List.length inversion_batches with
    | 0 -> semantic_import
    | count -> "SpecTecInversion" ^ Printf.sprintf "%04d" (count - 1) in
  write_file (path "SpecTecProofs") ("import " ^ proof_import ^ "\n");
  write_file (path "SpecTecCases")
    ("import SpecTecAll\n\n" ^ options ^ Buffer.contents cases)
