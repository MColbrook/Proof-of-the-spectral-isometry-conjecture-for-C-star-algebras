module
public import SpectralIsometry.SquareFamilyAssembly
public import SpectralIsometry.FiniteBidualDecomposition

/-!
# Central Split Family Assembly

Supporting results for spectral isometries of complex unital C*-algebras.
-/

 

@[expose] public section
set_option autoImplicit false
noncomputable section
open OAI.HochschildCorners OAI.BoundedHochschild.KadisonRingrose

namespace SpectralIsometry.SquareFamilyAssembly

universe u
variable {M X : Type u} [CStarAlgebra M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

local instance splitCanonicalOrder : PartialOrder M := CStarAlgebra.spectralOrder M
local instance splitCanonicalLE : LE M := (splitCanonicalOrder (M:=M)).toLE
local instance splitCanonicalStarOrder : StarOrderedRing M :=
  CStarAlgebra.spectralOrderedRing M

theorem of_central_split (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (V : ℂ → M →L[ℂ] M)
    (hblocks : ∀ (p q : M) (hp : IsStarProjection p) (hq : IsStarProjection q)
      (hpc : ∀ a : M, p*a=a*p) (hqc : ∀ a : M, q*a=a*q) (hsum : p+q=1),
      ProperlyInfiniteProjection p → FiniteAlgebra (Corner q hq) →
        SquaresFamily V) : SquaresFamily V := by
  obtain ⟨p,q,hp,hq,hpc,hqc,hsum,_hpq,hproper,hfinite⟩ :=
    FiniteBidualDecomposition.exists_central_split (M:=M) (X:=X) e
  exact hblocks p q hp hq hpc hqc hsum hproper hfinite

end SpectralIsometry.SquareFamilyAssembly

