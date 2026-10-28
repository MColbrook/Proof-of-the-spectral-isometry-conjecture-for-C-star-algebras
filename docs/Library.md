# Library guide

The public theorem namespace is `SpectralIsometry`.

| Module or family | Content |
| --- | --- |
| `SpectralIsometry.Basic` | Definitions, spectral estimates, automatic continuity, convex hulls, trace bounds and exponential identities. |
| `SpectralIsometry.Bidual*` | The universal von Neumann model, canonical bidual identification, preduals and extensions of operators. |
| `SpectralIsometry.StrongStar*` | Bounded strong* convergence and functional calculus. |
| `SpectralIsometry.Nilpotent*` | Support projections and bounded square-zero approximation. |
| `SpectralIsometry.Finite*` | Finite central summands, trace moments and quotient Jordan maps. |
| `SpectralIsometry.SquareZero*` and `SpectralIsometry.Corner*` | Square-zero preservation and properly infinite corner families. |
| `SpectralIsometry.EntireGroup` | Assembly of the entire-group proposition. |
| `SpectralIsometry.MainReduction*` | Transported inner automorphisms and the commutative reduction. |
| `SpectralIsometry.Normalization*` | Central unitary normalization. |
| `SpectralIsometry.MainTheorems` | The three principal results under their original hypotheses. |
| `SpectralIsometry.CenterTrace*` and `SpectralIsometry.GlobalCenterValuedTrace` | Faithful normal centre-valued traces. |
| `SpectralIsometry.Bounded*` and `SpectralIsometry.UniversalNeighborhoodNetAlgebra` | The algebra of bounded convergent nets and square-zero lifts. |

`SpectralIsometry.lean` imports the supporting library. `Solution.lean` exports
the three principal declarations. `AxiomReport.lean` consolidates the dependency
reports so mathematical source files contain no progress-printing commands.

`Verification/ComponentChallenge.lean` contains the additional supporting
statements selected by `comparator-components.json`. It is independent of the
proof library, just as the principal `Challenge.lean` is.
