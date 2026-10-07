# Lean Skeleton

The executable translates elaborated SpecTec IL into Lean source. Its path is:

1. `main.ml` parses CLI options, elaborates the requested spec paths, and collects diagnostics.
2. `pipeline.ml` selects strict translation or best-effort translation, then sequences the backend stages.
3. `translator.ml` lowers IL declarations into the Lean AST in `ast.ml`.
4. `order.ml` resolves declaration dependencies, groups mutual definitions, and removes invalid dependency chains in best-effort mode.
5. `printer.ml` renders the ordered Lean AST as source.

## Module Responsibilities

- `ast.ml` defines the source alias and the Lean intermediate representation.
- `translator.ml` handles IL types, expressions, premises, relations, tables, and declarations. Tables become row-selector definitions paired with relation rules. `builtin.ml` provides total builtins as Lean definitions and `builtin_relation.ml` provides partial or value-comparing builtins as relations.
- `order.ml` validates and orders Lean declarations. `traversal.ml` provides recursive operations over the Lean AST used by ordering and translation.
- `printer.ml` serializes declarations and terms. It collects all translated relations into one `Atom` and `InProgram`, emits user-facing `Prop` wrappers and rule introduction theorems, and turns relation values into calls in that same program. `wfs_backend.ml` contains the shared Lean `Rule`, `Program`, and well-founded semantics definitions. `identifier.ml` escapes names for Lean syntax.
- `main.ml` owns command-line behavior; `pipeline.ml` owns the translation-to-printing flow.

Translation stops at the first translation or ordering error. `--keep-going` retains independent declarations and reports rejected declarations.

## Relation semantics

Each source rule contributes a member of the shared `InProgram` relation. Positive relation premises become positive atoms, explicit negative premises become negative atoms, and pure propositions become side conditions. The shared WFS backend interprets the entire program; a public relation is `SpecTecWFS.Holds InProgram` of its atom. Its rule theorems are proved from `InProgram` constructors and `SpecTecWFS.Holds.rule`.

For a function with `otherwise`, translation creates `regular inputs result`, `enabled inputs`, and the public result atom. Any regular result establishes `enabled`, even when the result is unknown. The fallback rule requires `SpecTecWFS.Fails InProgram (enabled inputs)`, so an undetermined enabled atom does not select the fallback. Function arguments are `SpecTecRelationRef` values; their applications use `Atom.relation_call`, and named functions have dispatch rules in the same program.

The `$union_set`, `$unions_set`, `$diff_set`, and `$intersect_set` builtins
translate only when their key type expands to `text`. Their Lean definitions
are monomorphic over `String` and normalize every input, because SpecTec
exposes the duplicate-free `Value.compare` order of set elements as a list;
only its text ordering is reproduced exactly by Lean `String` ordering.
