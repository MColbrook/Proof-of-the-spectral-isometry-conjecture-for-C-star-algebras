# A proof of the spectral isometry conjecture for $C^*$-algebras

A Lean formalization of the spectral isometry theorem for arbitrary complex
unital C*-algebras.

This project formalizes the paper
[*Spectral isometries of unital C\*-algebras*](docs/References.md)
by Matthew J. Colbrook and George Stepaniants.

Every unital surjective complex-linear map preserving the spectral radius is
an algebraic Jordan isomorphism: it is bijective and preserves squares.
The development also proves the entire-group proposition and the normalization
corollary, which expresses a surjective spectral isometry as a unital Jordan
isomorphism multiplied by the central unitary element `T(1)`.

## Principal results

| Declaration | Result |
| --- | --- |
| `SpectralIsometry.main_result` | Unital surjective spectral isometries are Jordan isomorphisms. |
| `SpectralIsometry.entire_group` | An entire spectral-isometric exponential group has a derivation as its generator. |
| `SpectralIsometry.normalization` | A surjective spectral isometry is `T(1)` times a unital Jordan isomorphism. |

[Challenge.lean](Challenge.lean) records the statements.
[Solution.lean](Solution.lean) supplies the proofs.
The supporting library is in [SpectralIsometry/](SpectralIsometry/).

## Build and verify

The project uses Lean **4.35.0-rc3**. Install
[elan](https://github.com/leanprover/elan) and use the dependencies recorded in
`lake-manifest.json`.

```sh
lake exe cache get
lake build
lake env lean AxiomReport.lean
lake comparator --config comparator.json --paranoid
```

For the complete Linux verification workflow, including metadata, axiom reports
and sandboxed kernel checks, use Python 3.10 or newer:

```sh
python3 -m venv .venv
source .venv/bin/activate
python3 -m pip install -r scripts/requirements.txt
bash scripts/verify.sh
```

The extended supporting-statement suite is available with
`bash scripts/verify.sh --components`. GitHub Actions runs the principal
verification workflow on pushes and pull requests.

## Palomar

Publish the contents of this directory as the root of a public GitHub repository,
then use the [Palomar submission form](https://submit.palomar-registry.org/).
The standard files `comparator.json` and `formalization.yaml` are at the
repository root. See [submission instructions](docs/Submission.md).

## Authors and licence

Matthew J. Colbrook and George Stepaniants.

AI assistance was used for the Lean formalization, verification and review,
as disclosed in [formalization.yaml](formalization.yaml). It was not used to
write the manuscript. The formalization builds on Mathlib and the OpenAI
operator-algebra formalization; see [attribution](docs/Attribution.md).

Licensed under [Apache-2.0](LICENSE). Third-party notices are retained in
[NOTICE](NOTICE) and [vendor/](vendor/).
