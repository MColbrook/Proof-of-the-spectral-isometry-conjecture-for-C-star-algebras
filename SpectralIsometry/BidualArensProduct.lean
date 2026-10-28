module

public import SpectralIsometry.BidualDuality
public import SpectralIsometry.GenericPredualPullback

/-!
# Bidual Arens Product

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

/-- For fixed `a`, this evaluates `φ (a * b)` as a functional of `b`. -/
def arensLeftSections (φ : StrongDual ℂ A) : A →L[ℂ] StrongDual ℂ A :=
  (ContinuousLinearMap.compL ℂ A A ℂ φ).comp (ContinuousLinearMap.mul ℂ A)

/-- For fixed `b`, this evaluates `φ (a * b)` as a functional of `a`. -/
def arensRightSections (φ : StrongDual ℂ A) : A →L[ℂ] StrongDual ℂ A :=
  (ContinuousLinearMap.compL ℂ A A ℂ φ).comp (ContinuousLinearMap.mul ℂ A).flip

@[simp] theorem arensLeftSections_apply (φ : StrongDual ℂ A) (a b : A) :
    arensLeftSections φ a b = φ (a * b) := rfl

@[simp] theorem arensRightSections_apply (φ : StrongDual ℂ A) (b a : A) :
    arensRightSections φ b a = φ (a * b) := rfl

def firstArensPairing (F G : StrongDual ℂ (StrongDual ℂ A)) (φ : StrongDual ℂ A) : ℂ :=
  F (G.comp (arensLeftSections φ))

def secondArensPairing (F G : StrongDual ℂ (StrongDual ℂ A)) (φ : StrongDual ℂ A) : ℂ :=
  G (F.comp (arensRightSections φ))

private def arensLeftPullback (Φ : predual A) (m : algebra A) : predual A :=
  CoefficientPredual.leftMulPullback (algebra A) Φ m

private def arensRightPullback (Φ : predual A) (m : algebra A) : predual A :=
  CoefficientPredual.rightMulPullback (algebra A) Φ m

private theorem arensLeftPullback_restrict (Φ : predual A) (a : A) :
    restriction A (arensLeftPullback Φ (inclusion A a)) =
      arensLeftSections (restriction A Φ) a := by
  apply ContinuousLinearMap.ext
  intro b
  change (Φ : StrongDual ℂ (algebra A)) (inclusion A a * inclusion A b) =
    (Φ : StrongDual ℂ (algebra A)) (inclusion A (a * b))
  exact congrArg (Φ : StrongDual ℂ (algebra A)) ((inclusion A).map_mul a b).symm

private theorem arensRightPullback_restrict (Φ : predual A) (b : A) :
    restriction A (arensRightPullback Φ (inclusion A b)) =
      arensRightSections (restriction A Φ) b := by
  apply ContinuousLinearMap.ext
  intro a
  change (Φ : StrongDual ℂ (algebra A)) (inclusion A a * inclusion A b) =
    (Φ : StrongDual ℂ (algebra A)) (inclusion A (a * b))
  exact congrArg (Φ : StrongDual ℂ (algebra A)) ((inclusion A).map_mul a b).symm

theorem firstArensPairing_restriction (F G : StrongDual ℂ (StrongDual ℂ A))
    (Φ : predual A) :
    firstArensPairing F G (restriction A Φ) =
      (Φ : StrongDual ℂ (algebra A)) (canonicalBidualIsometry A F * canonicalBidualIsometry A G) := by
  let Ψ := arensRightPullback Φ (canonicalBidualIsometry A G)
  have hsections : G.comp (arensLeftSections (restriction A Φ)) = restriction A Ψ := by
    apply ContinuousLinearMap.ext
    intro a
    calc
      G.comp (arensLeftSections (restriction A Φ)) a =
          G (arensLeftSections (restriction A Φ) a) := rfl
      _ = G (restriction A (arensLeftPullback Φ (inclusion A a))) :=
        congrArg G (arensLeftPullback_restrict Φ a).symm
      _ = ((arensLeftPullback Φ (inclusion A a) : predual A) :
          StrongDual ℂ (algebra A)) (canonicalBidualIsometry A G) :=
        (canonicalBidualIsometry_pairing A G (arensLeftPullback Φ (inclusion A a))).symm
      _ = restriction A Ψ a := rfl
  exact (congrArg F hsections).trans (canonicalBidualIsometry_pairing A F Ψ).symm

theorem secondArensPairing_restriction (F G : StrongDual ℂ (StrongDual ℂ A))
    (Φ : predual A) :
    secondArensPairing F G (restriction A Φ) =
      (Φ : StrongDual ℂ (algebra A)) (canonicalBidualIsometry A F * canonicalBidualIsometry A G) := by
  let Ψ := arensLeftPullback Φ (canonicalBidualIsometry A F)
  have hsections : F.comp (arensRightSections (restriction A Φ)) = restriction A Ψ := by
    apply ContinuousLinearMap.ext
    intro b
    calc
      F.comp (arensRightSections (restriction A Φ)) b =
          F (arensRightSections (restriction A Φ) b) := rfl
      _ = F (restriction A (arensRightPullback Φ (inclusion A b))) :=
        congrArg F (arensRightPullback_restrict Φ b).symm
      _ = ((arensRightPullback Φ (inclusion A b) : predual A) :
          StrongDual ℂ (algebra A)) (canonicalBidualIsometry A F) :=
        (canonicalBidualIsometry_pairing A F (arensRightPullback Φ (inclusion A b))).symm
      _ = restriction A Ψ b := rfl
  exact (congrArg G hsections).trans (canonicalBidualIsometry_pairing A G Ψ).symm

/-- The coordinate product of the concrete canonical model agrees with the
first Arens product's defining successive-evaluation formula. -/
theorem canonicalBidualIsometry_firstArensPairing
    (F G : StrongDual ℂ (StrongDual ℂ A)) (φ : StrongDual ℂ A) :
    (canonicalBidualIsometry A).symm
      (canonicalBidualIsometry A F * canonicalBidualIsometry A G) φ = firstArensPairing F G φ := by
  let Φ := (canonicalPredualEquiv A).symm φ
  have hrestrict : restriction A Φ = φ := canonicalPredualEquiv_restrict A φ
  calc
    (canonicalBidualIsometry A).symm
        (canonicalBidualIsometry A F * canonicalBidualIsometry A G) φ =
        (Φ : StrongDual ℂ (algebra A))
          (canonicalBidualIsometry A F * canonicalBidualIsometry A G) :=
      canonicalBidualIsometry_symm_pairing A _ φ
    _ = firstArensPairing F G (restriction A Φ) := (firstArensPairing_restriction F G Φ).symm
    _ = firstArensPairing F G φ := congrArg (firstArensPairing F G) hrestrict

theorem arensPairings_eq (F G : StrongDual ℂ (StrongDual ℂ A)) (φ : StrongDual ℂ A) :
    firstArensPairing F G φ = secondArensPairing F G φ := by
  let Φ := (canonicalPredualEquiv A).symm φ
  have hrestrict : restriction A Φ = φ := canonicalPredualEquiv_restrict A φ
  calc
    firstArensPairing F G φ = firstArensPairing F G (restriction A Φ) :=
      congrArg (firstArensPairing F G) hrestrict.symm
    _ = (Φ : StrongDual ℂ (algebra A))
        (canonicalBidualIsometry A F * canonicalBidualIsometry A G) :=
      firstArensPairing_restriction F G Φ
    _ = secondArensPairing F G (restriction A Φ) := (secondArensPairing_restriction F G Φ).symm
    _ = secondArensPairing F G φ := congrArg (secondArensPairing F G) hrestrict

end SpectralIsometry.BidualFoundation.UniversalWeakClosure

