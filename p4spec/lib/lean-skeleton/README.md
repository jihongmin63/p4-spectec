# Lean translation

The backend lowers SpecTec declarations through a typed Lean IR, orders their
dependencies, and renders Lean source. `translator.ml` handles IL data and
expressions, `order.ml` validates dependency groups, and `printer.ml` emits code.
The shared ordered execution contract lives in `lean/SpecTecExecution.lean`.

Build with the project opam environment and Dune. Lean checks use Lean 4.34.1.

Run `dune exec p4spec/lib/lean-skeleton/main.exe -- <spec-path>`.
Use `--keep-going` to report unsupported declarations and retain independent ones.

Ordered execution is the default; `--relation-semantics declarative` selects
the inductive compatibility API. Only matching failure allows fallback; abort
stops the call. Shared fresh supply retains allocations from failed attempts.
