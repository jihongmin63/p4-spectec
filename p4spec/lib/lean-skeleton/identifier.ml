let lean_keywords : string list =
  [ "Type"; "Prop"; "Sort"; "abbrev"; "at"; "axiom"; "by"; "calc"; "class"; "def"; "deriving"; "do"; "else";
    "end"; "example"; "export"; "extends"; "false"; "for"; "fun";
    "from"; "have"; "if"; "import"; "in"; "inductive"; "instance"; "let"; "macro";
    "match"; "mutual"; "namespace"; "noncomputable"; "notation";
    "opaque"; "open"; "partial"; "private"; "protected"; "public";
    "repeat"; "return"; "set_option"; "show"; "structure"; "syntax"; "then"; "theorem";
    "true"; "universe"; "unsafe"; "variable"; "where"; "while";
    "with" ]

let is_letter (character : char) : bool =
  (character >= 'a' && character <= 'z')
  || (character >= 'A' && character <= 'Z')

let is_digit (character : char) : bool =
  character >= '0' && character <= '9'

let contains_closing_quote (name : string) : bool =
  let rec search (index : int) : bool =
    index + 1 < String.length name
    &&
    ((name.[index] = '\194' && name.[index + 1] = '\187')
    || search (index + 1))
  in
  search 0

let name_of_var (id : Lang.Il.id) (iters : Lang.Il.iter list) : string =
  id.it ^ String.concat "" (List.map Lang.Il.Print.string_of_iter iters)

let print_identifier (name : string) : string =
  if contains_closing_quote name then
    invalid_arg ("Lean identifier contains closing quote: " ^ name);
  let valid_start : bool =
    String.length name > 0 && (is_letter name.[0] || name.[0] = '_')
  in
  let valid_rest : bool =
    String.for_all
      (fun character ->
        is_letter character || is_digit character
        || List.mem character [ '_'; '\''; '!'; '?' ])
      name
  in
  if valid_start && valid_rest && name <> "_" && not (List.mem name lean_keywords)
  then name
  else "«" ^ name ^ "»"
