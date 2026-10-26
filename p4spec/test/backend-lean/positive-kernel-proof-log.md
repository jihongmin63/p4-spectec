# Positive case proof log

All ten smallest accepted inputs were proved. Shared semantics checking took
445.13 seconds; the ten case pipelines took 403.42 seconds in total. Six cases
completed with fuel 128 and four with fuel 512. The
[initial native attempt](positive-proof-log.md) failed before reaching cases;
kernel reduction avoids that runtime constructor-tag limit.

The revision below is Git HEAD at run start. Kernel-mode changes were in the
working tree; `results.json` records the runner SHA-256, which was checked against
the final script, together with source and oracle hashes.

Started (UTC): 2026-10-26T05:39:09.752525+00:00. Status: **complete**.

Commit: `2aa1e404a7013897e28b95087018d7c8c956f0ce`. Lean: `Lean (version 4.34.1, x86_64-unknown-linux-gnu, commit 5045d0056413266e57c625dcd7c365b10e377c52, Release)`.

Target: `Program_ok input expected`, with the exact recorded oracle and initial fresh supply 0.
This proves acceptance only; the corpus proposition also asks for uniqueness, which this runner does not prove.
Probe mode: kernel reduction. Only a kernel-checked `runEval_sound … rfl` theorem counts as proved.

Order: source bytes, then path. Selected: 10/1334. Proved: **10**.

Command:

```sh
ELAN_TOOLCHAIN=leanprover/lean4:v4.34.1 /usr/bin/python3 p4spec/test/backend-lean/prove_positive_cases.py --exe _build/default/p4spec/lib/lean-skeleton/main.exe --spec spec -I p4c/p4include --kernel-only --limit 10 --timeout 60 --output p4spec/test/backend-lean/generated/positive-kernel-first10-20261026 --report p4spec/test/backend-lean/positive-kernel-proof-log.md
```

Artifacts: `/home/p4-spectec/p4spec/test/backend-lean/generated/positive-kernel-first10-20261026` (generated Lean, phase output, commands, timings, hashes and `results.json`).

| ID | Bytes | Source | Result | Fuel | Seconds |
|---:|---:|---|---|---:|---:|
| 6 | 30 | `p4c/testdata/p4_16_errors/annotation.p4` | proved | 128 | 4.18 |
| 366 | 35 | `p4c/testdata/p4_16_errors/issue4144.p4` | proved | 512 | 99.53 |
| 939 | 47 | `p4c/testdata/p4_16_samples/issue1342.p4` | proved | 128 | 8.57 |
| 1540 | 55 | `p4c/testdata/p4_16_samples/pragma-pkginfo.p4` | proved | 128 | 4.17 |
| 465 | 61 | `p4c/testdata/p4_16_errors/spec-issue1297-string-cat-err-2-anno.p4` | proved | 128 | 4.77 |
| 1906 | 64 | `testdata/regression/pos/issue-232.p4` | proved | 512 | 112.55 |
| 329 | 67 | `p4c/testdata/p4_16_errors/issue3363.p4` | proved | 128 | 19.43 |
| 1907 | 79 | `testdata/regression/pos/issue-251.p4` | proved | 512 | 100.34 |
| 466 | 82 | `p4c/testdata/p4_16_errors/spec-issue1297-string-cat-err-3-anno.p4` | proved | 128 | 4.29 |
| 1371 | 102 | `p4c/testdata/p4_16_samples/lvalue-parens.p4` | proved | 512 | 45.59 |

Case 6 (proved):

```text
'SpecTec.case_6_by_runEval' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Case 366 (proved):

```text
'SpecTec.case_366_by_runEval' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Case 939 (proved):

```text
'SpecTec.case_939_by_runEval' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Case 1540 (proved):

```text
'SpecTec.case_1540_by_runEval' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Case 465 (proved):

```text
'SpecTec.case_465_by_runEval' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Case 1906 (proved):

```text
'SpecTec.case_1906_by_runEval' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Case 329 (proved):

```text
'SpecTec.case_329_by_runEval' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Case 1907 (proved):

```text
'SpecTec.case_1907_by_runEval' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Case 466 (proved):

```text
'SpecTec.case_466_by_runEval' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Case 1371 (proved):

```text
'SpecTec.case_1371_by_runEval' depends on axioms: [propext, Classical.choice, Quot.sound]
```
