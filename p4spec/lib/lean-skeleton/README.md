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

## P4 type-checking proof obligations

The executable also parses P4 files with the repository's P4 parser and turns
each parsed `p4program` value into a Lean term. The term is translated using the
constructor signatures of the elaborated SpecTec IL, including the parser's
internal list nodes whose runtime type annotations differ from the declared
SpecTec type. An accepted case supplies a fixed `p4programIR` answer. Its
proposition requires both `Program_ok input expected` and that every possible
`Program_ok` output equals `expected`. A rejected case requires
`¬ (∃ output : p4programIR, Program_ok input output)`. The generated definitions
contain no proofs.

`p4spec/test/backend-lean/discover_typecheck.py` inventories the repository's
SL static-semantics suites. They record 1,948 P4 cases: 1,282 expected to
pass, 550 expected to fail, and 116 excluded. The p4c boot suite covers the
same 1,918 p4c files; 34 of its negative results say `(unknown)` and therefore
cannot serve as rejection evidence. The parse-only and STF simulation suites
are outside this type-checking inventory. Run the script with `--list` for
every source path, recorded outcome, and originating suite.

The proof-ready starter corpus is in `p4spec/test/backend-lean/typecheck-cases.tsv`.
It contains 35 cases: 18 accepted and 17 rejected. Each one occurs in the
inventory and has been checked directly against deterministic `Program_ok`.
The accepted cases have fixed
Lean output terms in `p4spec/test/backend-lean/oracles/`, captured from the
repository's deterministic SL interpreter running `Program_ok`. Existing
`.expected` files record only pass, fail, or exclude status; the test runners
discard the actual P4 IR output. The p4c `*_outputs` files are compiler
artifacts, not SpecTec `p4programIR` answers. The corpus spans micro,
regression, and p4c sample/error tests. The remaining inventory cases are
candidates for later oracle capture and direct rejection checks.

The manifest uses tab-separated `accept<TAB>P4<TAB>expected-Lean-term` or
`reject<TAB>P4`; paths are relative to the manifest file. Blank lines and
lines starting with `#` are ignored. The fixed answer files make changes to
the interpreter's output visible before any Lean proof is attempted.

From the repository root, compare every answer file with the current SL
interpreter and check every rejected case:

```sh
python3 p4spec/test/backend-lean/discover_typecheck.py
python3 p4spec/test/backend-lean/verify_oracles.py \
  --exe _build/default/p4spec/lib/lean-skeleton/main.exe \
  --manifest p4spec/test/backend-lean/typecheck-cases.tsv \
  --spec spec --include p4c/p4include
```

From the repository root, generate the current corpus's propositions with:

```sh
dune exec p4spec/lib/lean-skeleton/main.exe -- \
  --obligations-only -I p4c/p4include \
  --manifest p4spec/test/backend-lean/typecheck-cases.tsv spec \
  > typecheck-obligations.lean
```

Use `--case FILE EXPECTED` and `--reject-case FILE` for individual inputs.
`--dump-output FILE` prints the deterministic SL interpreter's `Program_ok`
output as a Lean term, for creating or auditing an answer file.
`--check-rejection FILE` succeeds only when `Program_ok` fails by relation
nonmatch; syntax errors and interpreter aborts fail the check. Without
`--obligations-only`, the executable appends the propositions to the translated
specification. The resulting Lean file can then be extended with proof
theorems for the generated `case_N` propositions.

At present, strict translation of the full `spec` directory stops at the
stateful builtin `$fresh_typeId`, so the corpus propositions can be generated
but cannot yet be type-checked together with a complete Lean translation of
`Program_ok`. `--keep-going` is therefore disallowed with cases: it can omit
`Program_ok` and produce dangling propositions. The small
`case-obligation.watsup` fixture in `p4spec/test/backend-lean` exercises the
complete parse, translate, proposition, and Lean type-checking path.
