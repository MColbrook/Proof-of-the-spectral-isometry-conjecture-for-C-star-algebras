# Verification

The release was checked on Linux on VT_gauss on 28 October 2026, using Lean
4.35.0-rc3 and the resolved dependencies in `lake-manifest.json`. The six kernel
checkers are bundled with this toolchain.

The reproducible verification entry point is:

```sh
bash scripts/verify.sh
```

Use `--components` to select all 68 principal and supporting statements. Both
configurations permit only `propext`, `Classical.choice` and `Quot.sound`.
The Challenge modules contain deliberate statement-only `sorry` declarations;
the proof library and Solution contain none.

`AxiomReport.lean` reports dependencies for 507 public declarations. All 507
reports passed `scripts/check_axioms.py`, which rejects every axiom outside
the permitted set. Numerical bounds use proof-producing tactics whose results
are checked by Lean. No unproved custom axiom or native-execution proof oracle
supports the checked solutions.

## Completed checks

| Actual checking command | Result | Output |
| --- | --- | --- |
| `lake build` | Passed, 4,381 jobs. | [Build](reports/build.txt) |
| `lake env lean AxiomReport.lean` | Passed, 507 reports; only the permitted axioms or a subset. | [Axiom reports](reports/axioms.txt) |
| `lake comparator --config comparator.json --paranoid` | All six kernels accepted the three principal statements and their proofs. | [Principal results](reports/comparator.txt) |
| `lake comparator --config comparator-components.json --paranoid` | All six kernels accepted all 68 principal and supporting statements and their proofs. | [Extended suite](reports/components.txt) |
| `python3 scripts/check_project.py` and `--components` | Passed on Python 3.10.12 after installing the pinned dependencies in a virtual environment. | [Project setup](reports/project.txt) |
| `bash -n scripts/verify.sh` and `bash -n scripts/verify-comparator.sh` | Passed on Linux. | [Shell syntax](reports/project.txt) |

Each recorded command exited with status 0. The axiom-output parser also exited
with status 0. Comparator reported `Your solution is okay!` for both
configurations, with acceptance from Lean paranoid, lean4lean, nanoda, con-leche,
con-ron and Lean default. The retained output includes the con-leche and con-ron
notes about their in-process model of `Lean.Syntax` and its 30 generated records.

The reports contain actual command output from the cleaned project. The
reproducible workflow produces new logs for the checkout being tested.

The workflow retains actual commands and output under `verification-output/` and as
GitHub Actions artifacts. Build files and local logs are excluded from Git.
The scripts require Linux sandbox support and do not disable the sandbox.

AI assistance was for the Lean formalization, verification and review, not
writing the manuscript. Reviewers consulted the manuscript as the source for
statement-fidelity checks.

Separate AI reviews checked statement fidelity, proof dependencies, preservation
of mathematical tokens and import order during module cleanup, and release
documentation. These reviewers share model and workspace context; they are not
human or blinded reviewers. The fresh builds, axiom reports and kernel checks
provide the machine verification independently of those reviews.

The verified scope is the statements encoded in the two Challenge modules and
the supporting Lean development. No independent human proof review or Palomar
registration is claimed. Source alignment, attribution and the scope of cited
literature results are recorded in `formalization.yaml`.
