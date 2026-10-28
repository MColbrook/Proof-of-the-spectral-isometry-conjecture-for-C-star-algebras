module

public import SpectralIsometry.BidualRestriction
public import SpectralIsometry.GenericPredualPullback

/-!
# Bidual Trace Extension

Supporting results for spectral isometries of complex unital C*-algebras.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace SpectralIsometry.BidualFoundation.UniversalWeakClosure

attribute [local instance] CoefficientPredual.complexNormedSpaceSelf
attribute [local instance] orderedA starOrderedA
attribute [local instance 2000] complexOrder complexStarOrder
attribute [local instance] predualNormedGroup predualNormedSpace

universe u
variable (A : Type u) [CStarAlgebra A]

private theorem predual_ext {Φ Ψ : predual A}
    (h : ∀ a : A, (Φ : StrongDual ℂ (algebra A)) (inclusion A a) =
      (Ψ : StrongDual ℂ (algebra A)) (inclusion A a)) : Φ = Ψ := by
  apply (canonicalPredualEquiv A).injective
  apply ContinuousLinearMap.ext
  exact h

private def mulLeftPullback (Φ : predual A) (m : algebra A) : predual A :=
  CoefficientPredual.leftMulPullback (algebra A) Φ m

private def mulRightPullback (Φ : predual A) (m : algebra A) : predual A :=
  CoefficientPredual.rightMulPullback (algebra A) Φ m

/-- Extends the trace law from the original algebra in each variable separately.
No density/continuity premise is supplied by the caller beyond membership in
the actual constructed coefficient predual. -/
theorem tracial_of_restriction (Φ : predual A) (τ : StrongDual ℂ A)
    (hτ : ∀ a : A, (Φ : StrongDual ℂ (algebra A)) (inclusion A a) = τ a)
    (htr : ∀ a b : A, τ (a * b) = τ (b * a)) :
    ∀ m n : algebra A, (Φ : StrongDual ℂ (algebra A)) (m * n) =
      (Φ : StrongDual ℂ (algebra A)) (n * m) := by
  have horig (a : A) (n : algebra A) :
      (Φ : StrongDual ℂ (algebra A)) (inclusion A a * n) =
        (Φ : StrongDual ℂ (algebra A)) (n * inclusion A a) := by
    have he : mulLeftPullback A Φ (inclusion A a) =
        mulRightPullback A Φ (inclusion A a) := by
      apply predual_ext A
      intro b
      change (Φ : StrongDual ℂ (algebra A)) (inclusion A a * inclusion A b) =
        (Φ : StrongDual ℂ (algebra A)) (inclusion A b * inclusion A a)
      calc
        (Φ : StrongDual ℂ (algebra A)) (inclusion A a * inclusion A b) =
            (Φ : StrongDual ℂ (algebra A)) (inclusion A (a * b)) :=
          congrArg (fun m : algebra A => (Φ : StrongDual ℂ (algebra A)) m)
            ((inclusion A).map_mul a b).symm
        _ = τ (a * b) := hτ (a * b)
        _ = τ (b * a) := htr a b
        _ = (Φ : StrongDual ℂ (algebra A)) (inclusion A (b * a)) := (hτ (b * a)).symm
        _ = (Φ : StrongDual ℂ (algebra A)) (inclusion A b * inclusion A a) :=
          congrArg (fun m : algebra A => (Φ : StrongDual ℂ (algebra A)) m)
            ((inclusion A).map_mul b a)
    exact congrArg (fun Ψ : predual A => (Ψ : StrongDual ℂ (algebra A)) n) he
  intro m n
  have he : mulLeftPullback A Φ m = mulRightPullback A Φ m := by
    apply predual_ext A
    intro a
    change (Φ : StrongDual ℂ (algebra A)) (m * inclusion A a) =
      (Φ : StrongDual ℂ (algebra A)) (inclusion A a * m)
    exact (horig a m).symm
  exact congrArg (fun Ψ : predual A => (Ψ : StrongDual ℂ (algebra A)) n) he

theorem canonicalPredualEquiv_symm_tracial (τ : StrongDual ℂ A)
    (htr : ∀ a b : A, τ (a * b) = τ (b * a)) :
    ∀ m n : algebra A,
      (((canonicalPredualEquiv A).symm τ : predual A) :
        StrongDual ℂ (algebra A)) (m * n) =
      (((canonicalPredualEquiv A).symm τ : predual A) :
        StrongDual ℂ (algebra A)) (n * m) := by
  apply tracial_of_restriction A ((canonicalPredualEquiv A).symm τ) τ
  · intro a
    exact congrArg (fun f : StrongDual ℂ A => f a) (canonicalPredualEquiv_restrict A τ)
  · exact htr

theorem canonicalPredualEquiv_symm_one (τ : StrongDual ℂ A) :
    (((canonicalPredualEquiv A).symm τ : predual A) :
      StrongDual ℂ (algebra A)) 1 = τ 1 := by
  have h := congrArg (fun f : StrongDual ℂ A => f 1) (canonicalPredualEquiv_restrict A τ)
  change (((canonicalPredualEquiv A).symm τ : predual A) :
    StrongDual ℂ (algebra A)) (inclusion A 1) = τ 1 at h
  exact (congrArg (fun m : algebra A =>
    (((canonicalPredualEquiv A).symm τ : predual A) :
      StrongDual ℂ (algebra A)) m) ((inclusion A).map_one)).symm.trans h

end SpectralIsometry.BidualFoundation.UniversalWeakClosure

