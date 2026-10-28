module
public import SpectralIsometry.GenericWeightedFamilyResult
public import SpectralIsometry.ProperInfiniteCopiesBridge

/-!
# Generic Proper Weighted Family

Supporting results for spectral isometries of complex unital C*-algebras.
-/

 

@[expose] public section
set_option autoImplicit false
noncomputable section
open Filter Topology OAI.HochschildCorners OAI.BoundedHochschild.KadisonRingrose

namespace SpectralIsometry.WeightedFamilyResult
open StrongStarApproximation
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local instance (priority := 3000) properCanonicalOrder (M : VonNeumannAlgebra H) :
    PartialOrder M := CStarAlgebra.spectralOrder M
local instance (priority := 3000) properCanonicalLE (M : VonNeumannAlgebra H) : LE M :=
  (properCanonicalOrder M).toLE
local instance (priority := 3000) properCanonicalStarOrder (M : VonNeumannAlgebra H) :
    StarOrderedRing M := CStarAlgebra.spectralOrderedRing M

theorem proper_corner_family_result (M : VonNeumannAlgebra H) (p : M)
    (hp : IsStarProjection p) (hproper : ProperlyInfiniteProjection p)
    (R : ℂ → Corner p hp →L[ℂ] Corner p hp)
    (hR : ∀ z : ℂ, SquareZeroPreserver.PreservesSquareZero (R z).toLinearMap)
    (honto : ∀ z : ℂ, Function.Surjective (R z))
    (hseq : ∀ (z : ℂ) (a : ℕ → Corner p hp) (b : Corner p hp), (∀ n, ‖a n‖≤1) →
      StrongStarTendsto (fun n => ((a n:M):H →L[ℂ] H)) atTop ((b:M):H →L[ℂ] H) →
      StrongStarTendsto (fun n => ((R z (a n):M):H →L[ℂ] H)) atTop ((R z b:M):H →L[ℂ] H))
    (hhol : Differentiable ℂ (fun z : ℂ => R z 1))
    (hreal : ∀ z : ℂ, ∀ ζ∈spectrum ℂ (R z 1:M), ζ.im=0)
    (hzero : R 0 1=1) : UnitalSquares R := by
  obtain ⟨r,s,hr,hs,hrs⟩ :=
    SquareZeroPreserver.exists_corner_isometries_of_properlyInfinite (M:=M) hp hproper
  exact corner_family_result M p hp R hR honto r s hr hs hrs hseq hhol hreal hzero

end SpectralIsometry.WeightedFamilyResult

