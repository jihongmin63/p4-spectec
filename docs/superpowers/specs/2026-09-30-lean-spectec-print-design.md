# Lean SpecTec `$print_` Design

## Goal

Translate the P4-specific SpecTec builtin `$print_<X>(X) : text` into Lean
with the same successful outputs and failure domain as
`Interface.P4.Unparse.pp_value`. Generate custom printers only for the type
closure reached from the concrete `name`, `tableCustomName`,
`annotationToken`, and `expression` call sites.

The generated code must remain executable by reduction so that concrete
results are provable with `rfl` or `decide`. It must not use `sorry`,
`admit`, `axiom`, or `opaque`, and it must not turn an OCaml failure into an
arbitrary Lean result.

## Chosen Approach

Use a partial typeclass:

```lean
class SpecTecPrint (α : Type) where
  print? : α → Option String
```

The builtin itself is an inductive relation with one success rule requiring
`SpecTecPrint.print? value = some result`. A value for which `pp_value`
would fail receives `none`, so there is no corresponding `$print_` proof.
This keeps calls compatible with the backend's existing partial-builtin
translation and propagates printer requirements through generic relations in
the same way that `DecidableEq` requirements are propagated today.

Two alternatives were rejected:

- A total `α → String` class cannot represent `StructV` and other failing
  cases without inventing a result.
- Monomorphic relations per call-site type duplicate the large mutually
  recursive surface syntax closure and do not support generic types such as
  `pair<K,V>` cleanly.

## Exact Rendering Model

The generated prelude provides total base printers and small rendering
combinators. Base printers cover `Bool`, `Nat`, `Int`, and `String`.
`String` is escaped by traversing its UTF-8 bytes and reproducing OCaml
`Bytes.unsafe_escape`: quote, backslash, newline, tab, carriage return, and
backspace receive their named escapes; bytes outside ASCII 32--126 receive a
zero-padded three-digit decimal escape.

The current backend already represents SpecTec `text` as Lean `String`.
Consequently, arbitrary invalid UTF-8 OCaml byte strings are not representable
in Lean. The implementation is byte-for-byte equal on the representable
domain (valid UTF-8), including every byte at or above 128. This existing
representation restriction is the only new explicit assumption.

Variant constructors carry a normalized print-format tree in the Lean AST.
The tree distinguishes the cases that matter to OCaml's option-valued
assembly:

- an absent fragment;
- a present literal, including a present empty string;
- an argument hole;
- a sequence that fills absent children with `""` before joining;
- an assembly that drops absent children before joining;
- a fuse that concatenates both sides after replacing absence with `""`.

This distinction preserves doubled spaces and empty arguments. Default
formats come from the original mixfix tree: atoms are lower-cased with
`Atom.render_atom`, Tag atoms are absent, and arguments remain present even
when they print as `""`. Print hints are normalized from
`Hints.Alter.init`; `%` cursors advance, `%n` cursors do not, `#` fuses, and
brackets and sequences retain their distinct OCaml behavior. `OtherH` is a
present literal produced by `El.Print.string_of_exp`, matching the OCaml
fallback.

Lists join printed elements with one space without dropping empty strings,
options print `none` as `""`, and tuples print all semantic tuple elements
inside parentheses separated by `", "`. The Lean AST retains tuple arity
instead of collapsing it irreversibly to a binary product, while the printer
still renders the corresponding right-nested Lean product type and term.

## Type Closure and Recursive Generation

`order.ml` discovers concrete calls to `$print_` in translated relation
bodies, excludes the builtin relation's own generic conclusion, expands type
aliases, and walks only the data needed to print those roots. A structure is
included but its fields are not traversed because OCaml fails immediately on
`StructV`.

For every reachable datatype SCC, generate:

- one partial function per datatype;
- one helper per reachable nested `List`, `Option`, or semantic tuple shape;
- one `SpecTecPrint` instance per named type.

Functions in a recursive SCC form a Lean `mutual` block and recursive members
use `termination_by structural`, following the existing manual `DecidableEq`
generator. Datatype printers pattern-match on constructors, recursively print
only fields referenced by the stored format tree, and then evaluate that tree.
This is required because an OCaml hint may deliberately skip a value that
`pp_value` could not print. Structure printers return `none`. Generic datatypes
receive `SpecTecPrint` parameters for their type parameters; unsupported
generic recursion fails with a source-located diagnostic rather than silently
broadening the result relation.

The global instance-requirement pass tracks `DecidableEq` and
`SpecTecPrint` separately. It closes requirements through calls and supplies
the corresponding implicit instance placeholders at each application.

## Included Variants and Hint Identity

Elaboration assigns every typcase a `typorigin`. A constructor expression is
first built with that origin type, and an upcast to a containing variant does
not change the runtime value or its note. Therefore `pp_value` looks up a hint
under the original variant type, not the containing type.

When elaboration expands `(from X)`/plain variant inclusion, it copies the
origin typcase, including its hints and `typorigin`, into the containing
variant. The Lean translator will attach that copied origin format to the
containing constructor. Thus an upcast Lean constructor uses the same hint as
the unchanged OCaml runtime value even though its Lean datatype constructor
belongs to the containing type.

## Errors and Diagnostics

- Base and generated printers return `none` exactly for modeled OCaml
  failures, especially structures.
- The `$print_` relation has no failure constructor.
- Unsupported type shapes or non-uniform recursive instantiations raise the
  backend's source-located `Unsupported_il` diagnostic.
- The implementation adds no catch-all relation rule and no hidden logical
  assumption.

## Verification

Add `print.watsup` and `print-proof.lean` to `@backend-lean`. The fixture
covers default variants, Tag atoms, sequential and numbered holes, fuse and
bracket hints, empty option/list spacing, negative integers, byte escaping
for quote/backslash/control/non-ASCII input, tuples, structures with no
result, generic types, included variants, and mutually nested recursion.

A scratch OCaml executable constructs the same runtime values and obtains
all expected strings through `P4.Unparse.pp_value`; those outputs are copied
as literal Lean expectations. Verification then runs the focused target,
the full `@backend-lean` alias, `@speclang`, and the full-spec translation and
Lean check. The final report compares root diagnostics, translated relation
and function counts, and Lean check time against the recorded baseline
(144 roots, 11/259 relations, 410/701 functions, zero Lean errors, about
67--70 seconds on Lean 4.34.1).
