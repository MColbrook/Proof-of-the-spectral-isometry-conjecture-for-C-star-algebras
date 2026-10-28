# Attribution

The project formalizes *Spectral isometries of unital C*-algebras*, an unpublished
manuscript by Matthew J. Colbrook and George Stepaniants.

## Mathlib

[Mathlib](https://github.com/leanprover-community/mathlib4) is used under
Apache-2.0. Its resolved version is recorded in the Lake manifest. The proof
uses its spectral-radius formula, C*-spectral theory, continuous functional
calculus, complex analysis, measure theory and proof-producing tactics.

Important reused developments include:

- Jireh Loreaux's Gelfand formula, C*-spectral theory, functional calculus and
  commutative C*-algebra results.
- Yury Kudryashov's Liouville and complex-analysis developments.
- Bhavik Mehta and Yaël Dillies' geometric separation results.
- Johan Commelin and Kim Morrison's convex-combination and Carathéodory results.
- Eric Wieser's derivative rules for the involution, and the calculus library
  developed by Jeremy Avigad, Sébastien Gouëzel, Yury Kudryashov and others.
- Heather Macbeth's normed-ring inverse and Neumann-series infrastructure.

The original contributor notices remain authoritative in the dependency sources.

## Operator-algebra developments

The [OpenAI mathematics formalization](https://github.com/openai/math/tree/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean)
and its contributors supply the operator-algebra proofs in `vendor/OAI/`.
These Apache-2.0 compatibility ports provide universal GNS representations,
preduals, Kaplansky density, normal traces, finite/properly infinite central
decomposition and projection/isometry structure. Their mathematical proof
bodies are preserved. Module headers, public visibility and the prelude were
adapted for the selected Lean and Mathlib versions.

The original licence is retained in [vendor/LICENSE](../vendor/LICENSE).
The spectral-isometry arguments and their assembly are developed in this project.

## Automation and review

Codex AI agents assisted with the Lean formalization, module organization,
verification and separate statement and proof reviews. AI assistance was not
used to write the manuscript. Reviewers consulted the manuscript as the source
for statement-fidelity checks. The human authors and responsible
maintainers are Matthew J. Colbrook and George Stepaniants. The structured
production and review account is in [formalization.yaml](../formalization.yaml).
