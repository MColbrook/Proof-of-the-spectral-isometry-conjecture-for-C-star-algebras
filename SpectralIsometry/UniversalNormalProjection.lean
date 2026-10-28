module

public import SpectralIsometry.BidualFoundation
public import OAI.Analysis.BoundedHochschild.NormalVectors
public import Mathlib.Analysis.CStarAlgebra.Projection

/-!
# Universal Normal Projection

Supporting results for spectral isometries of complex unital C*-algebras.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace SpectralIsometry.BidualFoundation.UniversalNormalProjection

open UniversalWeakClosure OAI.HochschildNormalPart
open OAI.BoundedHochschild.KadisonRingrose

universe u
variable {M X : Type u} [CStarAlgebra M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)

attribute [local instance] UniversalWeakClosure.orderedA UniversalWeakClosure.starOrderedA
attribute [local instance 2000] UniversalWeakClosure.complexOrder UniversalWeakClosure.complexStarOrder

def projection : Hilbert M →L[ℂ] Hilbert M :=
  normalProjection e (universalGNSRepresentation (M:=M))

theorem projection_isStarProjection : IsStarProjection (projection e) :=
  isStarProjection_starProjection (U:=normalVectors e (universalGNSRepresentation (M:=M)))

theorem projection_mem : projection e ∈ (algebra M : Set (Hilbert M →L[ℂ] Hilbert M)) := by
  change projection e ∈ (weakClosure (universalGNSRepresentation (M:=M)).range :
    Set (Hilbert M →L[ℂ] Hilbert M))
  rw [weakClosure_coe]
  intro T hT
  have hh (a : M) : T*universalGNSRepresentation a=universalGNSRepresentation a*T :=
    (hT (universalGNSRepresentation a) ⟨a,rfl⟩).symm
  exact (normalProjection_commutant e (universalGNSRepresentation (M:=M)) T hh).symm

theorem projection_commutes_original (a : M) :
    Commute (projection e) (universalGNSRepresentation a) :=
  normalProjection_mul e (universalGNSRepresentation (M:=M)) a

set_option backward.isDefEq.respectTransparency.types false in
/-- Centrality is derived from commutation with the represented algebra and
its commutant, rather than a postulated central-kernel classification. -/
theorem projection_central (x : algebra M) :
    Commute (projection e) (x : Hilbert M →L[ℂ] Hilbert M) := by
  let S : StarSubalgebra ℂ (Hilbert M →L[ℂ] Hilbert M) :=
    (universalGNSRepresentation (M:=M)).range
  have hx : (x : Hilbert M →L[ℂ] Hilbert M) ∈
      Set.centralizer (Set.centralizer (S : Set (Hilbert M →L[ℂ] Hilbert M))) := by
    have hh := x.property
    change (x : Hilbert M →L[ℂ] Hilbert M) ∈
      (weakClosure S :
        Set (Hilbert M →L[ℂ] Hilbert M)) at hh
    rwa [weakClosure_coe] at hh
  have hp : projection e ∈ Set.centralizer
      (S : Set (Hilbert M →L[ℂ] Hilbert M)) := by
    rintro T ⟨a,rfl⟩
    exact (projection_commutes_original e a).symm.eq
  exact hx (projection e) hp

theorem projection_fixes_normal_coefficient (η ξ : Hilbert M)
    (h : coefficient (universalGNSRepresentation (M:=M)) η ξ ∈ normalDual e) :
    coefficient (universalGNSRepresentation (M:=M)) η (projection e ξ)=
      coefficient (universalGNSRepresentation (M:=M)) η ξ :=
  normalProjection_fixes_normal e (universalGNSRepresentation (M:=M)) η ξ h

end SpectralIsometry.BidualFoundation.UniversalNormalProjection

