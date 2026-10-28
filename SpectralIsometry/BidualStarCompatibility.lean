module

public import SpectralIsometry.BidualDuality
public import SpectralIsometry.GenericPredualStar

/-!
# Bidual Star Compatibility

Supporting results for spectral isometries of complex unital C*-algebras.
-/

 

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace SpectralIsometry.BidualFoundation.UniversalWeakClosure
universe u
attribute [local instance] CoefficientPredual.complexNormedSpaceSelf
attribute [local instance] orderedA starOrderedA
attribute [local instance 2000] complexOrder complexStarOrder
attribute [local instance] predualNormedGroup predualNormedSpace

variable {A : Type u} [CStarAlgebra A]

def bidualStarPairing (F : StrongDual ℂ (StrongDual ℂ A)) (φ : StrongDual ℂ A) : ℂ :=
  star (F (CoefficientPredual.functionalStar φ))

private def canonicalStarPullback (Φ : predual A) : predual A :=
  CoefficientPredual.starPullback (algebra A) Φ

private theorem canonicalStarPullback_restrict (Φ : predual A) :
    restriction A (canonicalStarPullback Φ) = CoefficientPredual.functionalStar (restriction A Φ) := by
  apply ContinuousLinearMap.ext
  intro a
  change star ((Φ : StrongDual ℂ (algebra A)) (star (inclusion A a))) =
    star ((Φ : StrongDual ℂ (algebra A)) (inclusion A (star a)))
  exact congrArg (fun m : algebra A => star ((Φ : StrongDual ℂ (algebra A)) m))
    (map_star (inclusion A) a).symm

theorem starPairing_restriction (F : StrongDual ℂ (StrongDual ℂ A)) (Φ : predual A) :
    (Φ : StrongDual ℂ (algebra A)) (star (canonicalBidualIsometry A F)) =
      bidualStarPairing F (restriction A Φ) := by
  let Ψ := canonicalStarPullback Φ
  calc
    (Φ : StrongDual ℂ (algebra A)) (star (canonicalBidualIsometry A F)) =
        star ((Ψ : StrongDual ℂ (algebra A)) (canonicalBidualIsometry A F)) :=
      (star_star _).symm
    _ = star (F (restriction A Ψ)) := congrArg star (canonicalBidualIsometry_pairing A F Ψ)
    _ = bidualStarPairing F (restriction A Φ) :=
      congrArg (fun φ : StrongDual ℂ A => star (F φ)) (canonicalStarPullback_restrict Φ)

theorem canonicalBidualIsometry_starPairing
    (F : StrongDual ℂ (StrongDual ℂ A)) (φ : StrongDual ℂ A) :
    (canonicalBidualIsometry A).symm (star (canonicalBidualIsometry A F)) φ =
      bidualStarPairing F φ := by
  let Φ := (canonicalPredualEquiv A).symm φ
  have hrestrict : restriction A Φ = φ := canonicalPredualEquiv_restrict A φ
  calc
    (canonicalBidualIsometry A).symm (star (canonicalBidualIsometry A F)) φ =
        (Φ : StrongDual ℂ (algebra A)) (star (canonicalBidualIsometry A F)) :=
      canonicalBidualIsometry_symm_pairing A _ φ
    _ = bidualStarPairing F (restriction A Φ) := starPairing_restriction F Φ
    _ = bidualStarPairing F φ := congrArg (bidualStarPairing F) hrestrict

end SpectralIsometry.BidualFoundation.UniversalWeakClosure

