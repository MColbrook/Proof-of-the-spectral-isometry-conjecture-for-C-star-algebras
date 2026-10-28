module

public import SpectralIsometry.GlobalCenterValuedTrace

/-!
# Center Valued Trace Concrete

Supporting results for spectral isometries of complex unital C*-algebras.
-/

 

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace SpectralIsometry.CenterValuedTraceConcrete

open OAI.BoundedHochschild.KadisonRingrose
open GlobalCenterValuedTrace

universe u

attribute [local instance] BidualFoundation.CoefficientPredual.complexNormedSpaceSelf
  BidualFoundation.CoefficientPredual.dualNormedGroup
  BidualFoundation.CoefficientPredual.dualNormedSpace
  BidualFoundation.CoefficientPredual.coefficientNormedGroup
  BidualFoundation.CoefficientPredual.coefficientNormedSpace

local instance orderedM (M : Type u) [CStarAlgebra M] : PartialOrder M :=
  CStarAlgebra.spectralOrder M
local instance starOrderedM (M : Type u) [CStarAlgebra M] : StarOrderedRing M :=
  CStarAlgebra.spectralOrderedRing M

theorem finite_vonNeumann_has_center_trace {H : Type u}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (M : VonNeumannAlgebra H) (hf : FiniteAlgebra M) :
    Nonempty (FaithfulNormalCenterTrace
      (BidualFoundation.CoefficientPredual.concretePredualIsometry M)) :=
  exists_faithful_normal_center_trace
    (BidualFoundation.CoefficientPredual.concretePredualIsometry M) hf

theorem positive_faithful {M X : Type u} [CStarAlgebra M]
    [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
    {e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M} (T : FaithfulNormalCenterTrace e)
    (a : M) (ha : 0≤a)
    (hTa : T.map a=0) : a=0 := by
  obtain ⟨b,hb⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp ha
  have hb0 : b=0 := T.faithful b (by rw [←hb]; exact hTa)
  rw [hb,hb0,star_zero,zero_mul]

end SpectralIsometry.CenterValuedTraceConcrete

