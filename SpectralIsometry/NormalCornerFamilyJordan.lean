module

public import SpectralIsometry.CornerNormalWeightedAssembly
public import SpectralIsometry.CornerHolomorphicWeight
public import SpectralIsometry.UnitalProjectionJordan

/-!
# Normal Corner Family Jordan

Supporting results for spectral isometries of complex unital C*-algebras.
-/

 

@[expose] public section
set_option autoImplicit false
noncomputable section

open Filter Topology
open OAI.HochschildCorners
open SpectralIsometry.StrongStarApproximation
open SpectralIsometry.BidualFoundation.CoefficientPredual
open SpectralIsometry.ConcreteCorner

namespace SpectralIsometry.SquareZeroPreserver

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local instance familyComplexNormedSpaceSelf : NormedSpace ℂ ℂ := NormedField.toNormedSpace
local instance familyCoefficientNormedGroup (M : VonNeumannAlgebra H) :
    NormedAddCommGroup (coefficientPredual M) :=
  SpectralIsometry.BidualFoundation.CoefficientPredual.coefficientNormedGroup M
local instance familyCoefficientNormedSpace (M : VonNeumannAlgebra H) :
    NormedSpace ℂ (coefficientPredual M) :=
  SpectralIsometry.BidualFoundation.CoefficientPredual.coefficientNormedSpace M

theorem corner_family_preserves_squares
    (M : VonNeumannAlgebra H) (p : M) (hp : IsStarProjection p)
    (R : ℂ → Corner p hp →L[ℂ] Corner p hp)
    (hR : ∀ z : ℂ, PreservesSquareZero (R z).toLinearMap)
    (honto : ∀ z : ℂ, Function.Surjective (R z))
    (r s : Corner p hp) (hr : star r*r=1) (hs : star s*s=1) (hrs : star r*s=0)
    (hseq : ∀ (z : ℂ) (a : ℕ → Corner p hp) (b : Corner p hp), (∀ n, ‖a n‖ ≤ 1) →
      StrongStarTendsto (fun n => ((a n : M) : H →L[ℂ] H)) atTop ((b : M) : H →L[ℂ] H) →
      StrongStarTendsto (fun n => ((R z (a n) : M) : H →L[ℂ] H)) atTop ((R z b : M) : H →L[ℂ] H))
    (hhol : Differentiable ℂ (fun z : ℂ => R z 1))
    (hreal : ∀ z : ℂ, ∀ ζ ∈ spectrum ℂ (R z 1 : M), ζ.im = 0)
    (hzero : R 0 1 = 1) :
    (∀ z : ℂ, R z 1 = 1) ∧ ∀ (z : ℂ) (a : Corner p hp), R z (a^2) = (R z a)^2 := by
  have hcentral (z : ℂ) : ∀ a : Corner p hp, Commute (R z 1) a :=
    central_weight_of_corner_bounded_strongStar_continuity M p hp (R z)
      (hR z) (honto z) r s hr hs hrs (hseq z)
  have hunit : ∀ z : ℂ, R z 1 = 1 :=
    holomorphic_central_weight_eq_one M p hp (fun z => R z 1) hhol hcentral hreal hzero
  refine ⟨hunit,?_⟩
  intro z a
  obtain ⟨hr',hs',hrs'⟩ := transport_unit_isometries M p hp r s hr hs hrs
  have hproj := all_weighted_projection_relations_of_bounded_strongStar_continuity
    (model M p hp) (model M p hp) (transport M p hp (R z))
    (transport_preservesSquareZero M p hp (R z) (hR z))
    ((equivalence M p hp).symm r) ((equivalence M p hp).symm s) hr' hs' hrs'
    (transport_bounded_sequence_continuity M p hp (R z) (hseq z))
  have hmodelunit : transport M p hp (R z) 1 = 1 := by
    apply (equivalence M p hp).injective
    change equivalence M p hp (transport M p hp (R z) 1) = equivalence M p hp 1
    rw [equivalence_transport_weight,hunit z,map_one]
  have hsq := square_preserving_of_unital_projection_relations
    (concretePredualIsometry (model M p hp)) (transport M p hp (R z)) hmodelunit hproj
  have hh := congrArg (equivalence M p hp) (hsq ((equivalence M p hp).symm a))
  simpa only [equivalence_transport,map_pow,(equivalence M p hp).apply_symm_apply] using hh

end SpectralIsometry.SquareZeroPreserver

