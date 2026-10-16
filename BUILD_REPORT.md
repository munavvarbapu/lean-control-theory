# Verification report

Local verification completed on **16 October 2026 (UTC)**.

| Check | Result |
| --- | --- |
| Lean version | 4.24.0, release build |
| Lean commit | `797c613eb9b6d4ec95db23e3e00af9ac6657f24b` |
| mathlib commit | `f897ebcf72cd16f89ab4577d0c826cd14afaafc7` |
| `lake build` | Passed |
| Substantive mathematical modules | 10 |
| Library modules including the root import | 11 |
| Named theorem declarations | 64 |
| Principal theorem axiom reports | 14 passed |
| Proof-placeholder and project-axiom source scan | Passed |
| Full `python3 scripts/check.py` run | Passed, exit code 0 |

The principal results depend only on `propext`, `Classical.choice`, and
`Quot.sound`. These are the usual logical foundations used throughout
mathlib. No principal result depends on `sorryAx` or a project-defined axiom.

The complete audit output is in
[`verification/lean-audit.txt`](verification/lean-audit.txt).
[`verification/source-sha256.txt`](verification/source-sha256.txt) records
the checked source and build-configuration file hashes.

The local execution environment required a compatibility wrapper for
executable-path lookup because of its process namespace. The wrapper did
not change the Lean compiler, kernel, mathlib sources, or theorem sources.
A standard Lean installation does not need that wrapper.

The included GitHub Actions workflow has been prepared for publication.
This report records the local checks; it does not claim a hosted CI run.
