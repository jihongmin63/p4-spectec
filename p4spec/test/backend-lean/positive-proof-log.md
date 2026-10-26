# Positive case proof log

Shared semantics compilation failed after 307.04 seconds because a generated
`Call` constructor tag exceeded Lean's native runtime limit. No individual case
was attempted in this run. The subsequent
[kernel-mode run](positive-kernel-proof-log.md) proved all ten selected cases.

Started (UTC): 2026-10-26T05:28:59.763387+00:00. Status: **failed**.

Commit: `c469e1b7457237c9ce630c17158206c1ef655452`. Lean: `Lean (version 4.34.1, x86_64-unknown-linux-gnu, commit 5045d0056413266e57c625dcd7c365b10e377c52, Release)`.

Target: `Program_ok input expected`, with the exact recorded oracle and initial fresh supply 0.
This proves acceptance only; the corpus proposition also asks for uniqueness, which this runner does not prove.
Probe mode: native evaluation. Only a kernel-checked `runEval_sound … rfl` theorem counts as proved.

Order: source bytes, then path. Selected: 10/1334. Proved: **0**.

Command:

```sh
/usr/bin/python3 p4spec/test/backend-lean/prove_positive_cases.py --exe _build/default/p4spec/lib/lean-skeleton/main.exe --spec spec -I p4c/p4include --limit 10 --output p4spec/test/backend-lean/generated/positive-first10-20261026 --report p4spec/test/backend-lean/positive-proof-log.md
```

Artifacts: `/home/p4-spectec/p4spec/test/backend-lean/generated/positive-first10-20261026` (generated Lean, phase output, commands, timings, hashes and `results.json`).

| ID | Bytes | Source | Result | Fuel | Seconds |
|---:|---:|---|---|---:|---:|
| 6 | 30 | `p4c/testdata/p4_16_errors/annotation.p4` | pending |  | 0.00 |
| 366 | 35 | `p4c/testdata/p4_16_errors/issue4144.p4` | pending |  | 0.00 |
| 939 | 47 | `p4c/testdata/p4_16_samples/issue1342.p4` | pending |  | 0.00 |
| 1540 | 55 | `p4c/testdata/p4_16_samples/pragma-pkginfo.p4` | pending |  | 0.00 |
| 465 | 61 | `p4c/testdata/p4_16_errors/spec-issue1297-string-cat-err-2-anno.p4` | pending |  | 0.00 |
| 1906 | 64 | `testdata/regression/pos/issue-232.p4` | pending |  | 0.00 |
| 329 | 67 | `p4c/testdata/p4_16_errors/issue3363.p4` | pending |  | 0.00 |
| 1907 | 79 | `testdata/regression/pos/issue-251.p4` | pending |  | 0.00 |
| 466 | 82 | `p4c/testdata/p4_16_errors/spec-issue1297-string-cat-err-3-anno.p4` | pending |  | 0.00 |
| 1371 | 102 | `p4c/testdata/p4_16_samples/lvalue-parens.p4` | pending |  | 0.00 |

Setup/run error (full output is in the artifact directory):

```text
command failed: lean -o /home/p4-spectec/p4spec/test/backend-lean/generated/positive-first10-20261026/Semantics.olean /home/p4-spectec/p4spec/test/backend-lean/generated/positive-first10-20261026/Semantics.lean
/home/p4-spectec/p4spec/test/backend-lean/generated/positive-first10-20261026/Semantics.lean:41790:4: error: failed to compile definition, compiler IR check failed at `SpecTec.«$partition_parameterListIR:clause:1:exec»._lam_2`. Error: tag for constructor 'SpecTec.Call.«$partition_parameterListIR»' is too big, this is a limitation of the current runtime
/home/p4-spectec/p4spec/test/backend-lean/generated/positive-first10-20261026/Semantics.lean:41795:4: error(lean.dependsOnNoncomputable): failed to compile definition, consider marking it as 'noncomputable' because it depends on '«$partition_parameterListIR:clause:1:exec»', which is 'noncomputable'
/home/p4-spectec/p4spec/test/backend-lean/generated/positive-first10-20261026/Semantics.lean:41800:4: error: failed to compile definition, compiler IR check failed at `SpecTec.«$partition_parameterListIR:clause:2:exec»._lam_2`. Error: tag for constructor 'SpecTec.Call.«$partition_parameterListIR»' is too big, this is a limitation of the current runtime
/home/p4-spectec/p4spec/test/backend-lean/generated/positive-first10-20261026/Semantics.lean:41805:4: error(lean.dependsOnNoncomputable): failed to compile definition, consider marking it as 'noncomputable' because it depends on '«$partition_parameterListIR:clause:2:exec»', which is 'noncomputable'
/home/p4-spectec/p4spec/test/backend-lean/generated/positive-first10-20261026/Semantics.lean:41810:4: error: failed to compile definition, compiler IR check failed at `SpecTec.«$partition_parameterListIR:clause:3:exec»._lam_3`. Error: tag for constructor 'SpecTec.Call.«$partition_parameterListIR»' is too big, this is a limitation of the current runtime
/home/p4-spectec/p4spec/test/backend-lean/generated/positive-first10-20261026/Semantics.lean:41815:4: error(lean.dependsOnNoncomputable): failed to compile definition, consider marking it as 'noncomputable' because it depends on '«$partition_parameterListIR:clause:3:exec»', which is 'noncomputable'
/home/p4-spectec/p4spec/test/backend-lean/generated/positive-first10-20261026/Semantics.lean:41820:4: error(lean.dependsOnNoncomputable): failed to compile definition, consider marking it as 'noncomputable' because it depends on '«$partition_parameterListIR:clause:1»', which is 'noncomputable'
/home/p4-spectec/p4spec/test/backend-lean/generated/positive-first10-20261026/Semantics.lean:41825:4: error(lean.dependsOnNoncomputable): failed to compile definition, consider marking it as 'noncomputable' because it depends on '«$partition_parameterListIR:clause:1:exec»', which is 'noncomputable'
/home/p4-spectec/p4spec/test/backend-lean/generated/positive-first10-20261026/Semantics.lean:41840:4: error: failed to compile definition, compiler IR check failed at `«$align_parameterListIR:case_1:iter:1:clause:1:exec»`. Error: tag for constructor 'SpecTec.Call.«$align_parameterListIR:case_1:iter:1»' is too big, this is a limitation of the current runtime
/home/p4-spectec/p4spec/test/backend-lean/generated/positive-first10-20261026/Semantics.lean:41845:4: error(lean.dependsOnNoncomputable): failed to compile definition, consider marking it as 'noncomputable' because it depends on '«$align_parameterListIR:case_1:iter:1:clause:1:exec»', which is 'noncomputable'
/home/p4-spectec/p4spec/test/backend-lean/generated/positive-first10-20261026/Semantics.lean:41850:4: error(lean.dependsOnNoncomputable): failed to compile definition, consider marking it as 'noncomputable' because it depends on '«$align_parameterListIR:case_1:iter:1:clause:1»', which is 'noncomputable'
/home/p4-spectec/p4spec/test/backend-lean/generated/positive-first10-20261026/Semantics.lean:41855:4: error(lean.dependsOnNoncomputable): failed to compile definition, consider marking it as 'noncomputable' because it depends on '«$align_parameterListIR:
```
