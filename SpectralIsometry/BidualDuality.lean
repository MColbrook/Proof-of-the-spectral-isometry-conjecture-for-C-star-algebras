module

public import SpectralIsometry.BidualRestrictionEquiv
public import SpectralIsometry.GenericDualIsometry

/-!
# Bidual Duality

Supporting results for spectral isometries of complex unital C*-algebras.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace SpectralIsometry.BidualFoundation.UniversalWeakClosure

open Filter Topology
open scoped InnerProductSpace
open OAI.BoundedHochschild.KadisonRingrose

universe u
variable (A : Type u) [CStarAlgebra A]

attribute [local instance] CoefficientPredual.complexNormedSpaceSelf
attribute [local instance] orderedA starOrderedA
attribute [local instance 2000] complexOrder complexStarOrder
attribute [local instance] predualNormedGroup predualNormedSpace

/-- Reuses Mathlib's continuous-linear arrow equivalence. The norm proof uses
both directions of the already established restriction isometry. -/
def restrictionDualEquiv (hDense : ContractionStrongDense A) :
    StrongDual ℂ (StrongDual ℂ A) ≃ₗᵢ[ℂ] StrongDual ℂ (predual A) :=
  GenericDual.dualIsometryEquiv (restrictionEquiv A hDense)

theorem restrictionDualEquiv_apply (hDense : ContractionStrongDense A)
    (F : StrongDual ℂ (StrongDual ℂ A)) (Φ : predual A) :
    restrictionDualEquiv A hDense F Φ = F (restriction A Φ) :=
  GenericDual.dualIsometryEquiv_apply (restrictionEquiv A hDense) F Φ

/-- Exact Banach-bidual realization in the universal weak closure, after the
finite contraction density premise has been proved. -/
def bidualIsometry (hDense : ContractionStrongDense A) :
    StrongDual ℂ (StrongDual ℂ A) ≃ₗᵢ[ℂ] algebra A :=
  (restrictionDualEquiv A hDense).trans
    (CoefficientPredual.predualEvaluationEquiv (algebra A)).symm

/-- This is the exact pairing that identifies the concrete predual with A*;
it will also identify the two weak-star convergence notions. -/
theorem bidualIsometry_pairing (hDense : ContractionStrongDense A)
    (F : StrongDual ℂ (StrongDual ℂ A)) (Φ : predual A) :
    (Φ : StrongDual ℂ (algebra A)) (bidualIsometry A hDense F) =
      F (restriction A Φ) := by
  let J := CoefficientPredual.predualEvaluationEquiv (algebra A)
  change J (J.symm (restrictionDualEquiv A hDense F)) Φ = _
  exact (congrArg (fun G : StrongDual ℂ (predual A) => G Φ)
    (J.apply_symm_apply (restrictionDualEquiv A hDense F))).trans
      (restrictionDualEquiv_apply A hDense F Φ)

theorem bidualIsometry_canonical (hDense : ContractionStrongDense A) (a : A) :
    bidualIsometry A hDense (NormedSpace.inclusionInDoubleDual ℂ A a) = inclusion A a := by
  let J := CoefficientPredual.predualEvaluationEquiv (algebra A)
  apply J.injective
  change J (J.symm (restrictionDualEquiv A hDense
    (NormedSpace.inclusionInDoubleDual ℂ A a))) = J (inclusion A a)
  refine (J.apply_symm_apply (restrictionDualEquiv A hDense
    (NormedSpace.inclusionInDoubleDual ℂ A a))).trans ?_
  apply ContinuousLinearMap.ext
  intro Φ
  rfl

/-- This wrapper retains only the original C*-algebra hypothesis. -/
def canonicalBidualIsometry : StrongDual ℂ (StrongDual ℂ A) ≃ₗᵢ[ℂ] algebra A :=
  bidualIsometry A (contractionStrongDense A)

theorem canonicalBidualIsometry_apply (a : A) :
    canonicalBidualIsometry A (NormedSpace.inclusionInDoubleDual ℂ A a) = inclusion A a :=
  bidualIsometry_canonical A (contractionStrongDense A) a

theorem canonicalBidualIsometry_pairing
    (F : StrongDual ℂ (StrongDual ℂ A)) (Φ : predual A) :
    (Φ : StrongDual ℂ (algebra A)) (canonicalBidualIsometry A F) =
      F (restriction A Φ) :=
  bidualIsometry_pairing A (contractionStrongDense A) F Φ

/-- Unique norm-preserving extension of each functional on A to the concrete
coefficient predual. Positivity and traciality require separate proofs. -/
def canonicalPredualEquiv : predual A ≃ₗᵢ[ℂ] StrongDual ℂ A :=
  restrictionEquiv A (contractionStrongDense A)

theorem canonicalPredualEquiv_restrict (φ : StrongDual ℂ A) :
    restriction A ((canonicalPredualEquiv A).symm φ) = φ :=
  (canonicalPredualEquiv A).apply_symm_apply φ

theorem canonicalBidualIsometry_symm_pairing (T : algebra A) (φ : StrongDual ℂ A) :
    (canonicalBidualIsometry A).symm T φ =
      (((canonicalPredualEquiv A).symm φ : predual A) :
        StrongDual ℂ (algebra A)) T := by
  let Φ := (canonicalPredualEquiv A).symm φ
  calc
    (canonicalBidualIsometry A).symm T φ =
        (canonicalBidualIsometry A).symm T (restriction A Φ) :=
      congrArg ((canonicalBidualIsometry A).symm T)
        (canonicalPredualEquiv_restrict A φ).symm
    _ = (Φ : StrongDual ℂ (algebra A))
        (canonicalBidualIsometry A ((canonicalBidualIsometry A).symm T)) :=
      (canonicalBidualIsometry_pairing A ((canonicalBidualIsometry A).symm T) Φ).symm
    _ = (Φ : StrongDual ℂ (algebra A)) T :=
      congrArg (fun m : algebra A => (Φ : StrongDual ℂ (algebra A)) m)
        ((canonicalBidualIsometry A).apply_symm_apply T)

end SpectralIsometry.BidualFoundation.UniversalWeakClosure

