module

public import SpectralIsometry.BidualConcretePredual

/-!
# Bidual Foundation

Supporting results for spectral isometries of complex unital C*-algebras.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace SpectralIsometry.BidualFoundation.UniversalWeakClosure

open scoped InnerProductSpace ComplexOrder
open OAI.BoundedHochschild.KadisonRingrose OAI.HochschildNormalPart
open CoefficientPredual

private theorem generic_fourTerm_norm_le {X : Type*} [NormedAddCommGroup X]
    [NormedSpace ℂ X] (e : Fin 4 → X) (N : ℝ) (he : ∀ i : Fin 4, ‖e i‖ ≤ N) :
    ‖e 0 - e 1 + Complex.I • (e 2 - e 3)‖ ≤ 4 * N := by
  calc
    ‖e 0 - e 1 + Complex.I • (e 2 - e 3)‖ ≤
        ‖e 0 - e 1‖ + ‖Complex.I • (e 2 - e 3)‖ := norm_add_le _ _
    _ ≤ (‖e 0‖ + ‖e 1‖) + (‖e 2‖ + ‖e 3‖) := by
      rw [norm_smul Complex.I (e 2 - e 3), Complex.norm_I, one_mul]
      exact add_le_add (norm_sub_le _ _) (norm_sub_le _ _)
    _ ≤ (N + N) + (N + N) :=
      add_le_add (add_le_add (he 0) (he 1)) (add_le_add (he 2) (he 3))
    _ = 4 * N := by ring

universe u
variable (A : Type u) [CStarAlgebra A]

attribute [local instance] CoefficientPredual.complexNormedSpaceSelf
-- These specific scalar instances must outrank the polymorphic canonical
-- order on the abstract algebra A below.
local instance (priority := 2000) complexOrder : PartialOrder ℂ := Complex.partialOrder
local instance (priority := 2000) complexStarOrder : StarOrderedRing ℂ :=
  RCLike.toStarOrderedRing
local instance orderedA : PartialOrder A := CStarAlgebra.spectralOrder A
local instance starOrderedA : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A

/-- Pin the original-dual norm and the canonical orders before introducing the
concrete coefficient-predual dictionaries. This is proof reuse from the
attributed candidate, with no new hypothesis on A or its functionals. -/
theorem exists_four_positive_canonical (φ : StrongDual ℂ A) :
    ∃ ψ : Fin 4 → (A →ₚ[ℂ] ℂ), (∀ i, ‖ψ i 1‖ ≤ ‖φ‖) ∧
      ∀ a : A, φ a = ψ 0 a - ψ 1 a + Complex.I * (ψ 2 a - ψ 3 a) :=
  OAI.HochschildPositiveDecomposition.exists_four_positive (M := A) φ

def fourPositiveFamily (φ : StrongDual ℂ A) : Fin 4 → (A →ₚ[ℂ] ℂ) :=
  Classical.choose (exists_four_positive_canonical A φ)

theorem fourPositiveFamily_norm (φ : StrongDual ℂ A) (i : Fin 4) :
    ‖fourPositiveFamily A φ i 1‖ ≤ ‖φ‖ :=
  (Classical.choose_spec (exists_four_positive_canonical A φ)).1 i

theorem fourPositiveFamily_apply (φ : StrongDual ℂ A) (a : A) :
    φ a = fourPositiveFamily A φ 0 a - fourPositiveFamily A φ 1 a +
      Complex.I * (fourPositiveFamily A φ 2 a - fourPositiveFamily A φ 3 a) :=
  (Classical.choose_spec (exists_four_positive_canonical A φ)).2 a

abbrev Hilbert := UniversalGNS A

/-- Bicommutant of an arbitrary represented star subalgebra. -/
def weakClosure {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (S : StarSubalgebra ℂ (H →L[ℂ] H)) : VonNeumannAlgebra H where
  toStarSubalgebra := StarSubalgebra.centralizer ℂ
    (StarSubalgebra.centralizer ℂ (S : Set (H →L[ℂ] H)) : Set (H →L[ℂ] H))
  centralizer_centralizer' := by
    change Set.centralizer (Set.centralizer
      (StarSubalgebra.centralizer ℂ
        (StarSubalgebra.centralizer ℂ (S : Set (H →L[ℂ] H)) : Set (H →L[ℂ] H)) :
          Set (H →L[ℂ] H))) =
      (StarSubalgebra.centralizer ℂ
        (StarSubalgebra.centralizer ℂ (S : Set (H →L[ℂ] H)) : Set (H →L[ℂ] H)) :
          Set (H →L[ℂ] H))
    rw [StarSubalgebra.coe_centralizer_centralizer, StarMemClass.star_coe_eq, Set.union_self]
    exact Set.centralizer_centralizer_centralizer (Set.centralizer (S : Set (H →L[ℂ] H)))

theorem weakClosure_coe {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (S : StarSubalgebra ℂ (H →L[ℂ] H)) :
    (weakClosure S : Set (H →L[ℂ] H)) =
      Set.centralizer (Set.centralizer (S : Set (H →L[ℂ] H))) := by
  change (StarSubalgebra.centralizer ℂ
    (StarSubalgebra.centralizer ℂ (S : Set (H →L[ℂ] H)) : Set (H →L[ℂ] H)) :
      Set (H →L[ℂ] H)) = _
  rw [StarSubalgebra.coe_centralizer_centralizer, StarMemClass.star_coe_eq, Set.union_self]

theorem subset_weakClosure {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (S : StarSubalgebra ℂ (H →L[ℂ] H)) : S ≤ (weakClosure S).toStarSubalgebra := by
  intro T hT
  change T ∈ (weakClosure S : Set (H →L[ℂ] H))
  rw [weakClosure_coe]
  exact Set.subset_centralizer_centralizer hT

def algebra : VonNeumannAlgebra (Hilbert A) :=
  weakClosure (universalGNSRepresentation (M := A)).range

def inclusion : A →⋆ₐ[ℂ] algebra A :=
  (universalGNSRepresentation (M := A)).codRestrict (algebra A).toStarSubalgebra
    (fun a => subset_weakClosure _ ⟨a, rfl⟩)

@[simp] theorem inclusion_coe (a : A) :
    ((inclusion A a : algebra A) : Hilbert A →L[ℂ] Hilbert A) =
      universalGNSRepresentation a := rfl

theorem inclusion_norm (a : A) : ‖inclusion A a‖ = ‖a‖ :=
  universalGNSRepresentation_norm a

theorem inclusion_injective : Function.Injective (inclusion A) := by
  intro a b h
  exact universalGNSRepresentation_injective (congrArg Subtype.val h)

def inclusionCLM : A →L[ℂ] algebra A where
  toLinearMap := (inclusion A).toLinearMap
  cont := (NonUnitalStarAlgHom.isometry (inclusion A) (inclusion_injective A)).continuous

abbrev predual := coefficientPredual (algebra A)

-- Register only the specialized coefficient subtype dictionaries below.
-- Imported helper reducibility is left unchanged; no unsafe override is used.

local instance predualNormedGroup : NormedAddCommGroup (predual A) :=
  CoefficientPredual.coefficientNormedGroup (algebra A)
local instance predualNormedSpace : NormedSpace ℂ (predual A) :=
  CoefficientPredual.coefficientNormedSpace (algebra A)

theorem predual_norm_coe (Φ : predual A) :
    ‖(Φ : StrongDual ℂ (algebra A))‖ = ‖Φ‖ := rfl

def restriction (Φ : predual A) : StrongDual ℂ A :=
  (Φ : StrongDual ℂ (algebra A)).comp (inclusionCLM A)

@[simp] theorem restriction_apply (Φ : predual A) (a : A) :
    restriction A Φ a = (Φ : StrongDual ℂ (algebra A)) (inclusion A a) := rfl

theorem restriction_add (Φ Ψ : predual A) :
    restriction A (Φ + Ψ) = restriction A Φ + restriction A Ψ := by
  ext a
  rfl

theorem restriction_sub (Φ Ψ : predual A) :
    restriction A (Φ - Ψ) = restriction A Φ - restriction A Ψ := by
  ext a
  rfl

theorem restriction_smul (z : ℂ) (Φ : predual A) :
    restriction A (z • Φ) = z • restriction A Φ := by
  ext a
  rfl

theorem restriction_norm_le (Φ : predual A) : ‖restriction A Φ‖ ≤ ‖Φ‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg Φ)
  intro a
  calc
    ‖restriction A Φ a‖ ≤ ‖(Φ : StrongDual ℂ (algebra A))‖ * ‖inclusion A a‖ := Φ.val.le_opNorm _
    _ = ‖Φ‖ * ‖a‖ :=
      congrArg₂ (fun x y : ℝ => x * y) (predual_norm_coe A Φ) (inclusion_norm A a)

def cyclicVector (ψ : A →ₚ[ℂ] ℂ) : Hilbert A := by
  classical
  exact lp.single 2 ψ (positiveVector ψ)

theorem cyclicVector_coefficient (ψ : A →ₚ[ℂ] ℂ) (a : A) :
    ⟪cyclicVector A ψ, universalGNSRepresentation a (cyclicVector A ψ)⟫_ℂ = ψ a := by
  classical
  change ⟪lp.single 2 ψ (positiveVector ψ),
    universalGNSRepresentation a (lp.single 2 ψ (positiveVector ψ))⟫_ℂ = ψ a
  rw [lp.inner_single_left, universalGNSRepresentation_apply, lp.single_apply_self]
  exact positiveVector_coefficient ψ a

theorem cyclicVector_norm_sq (ψ : A →ₚ[ℂ] ℂ) : ‖cyclicVector A ψ‖ ^ 2 = ‖ψ 1‖ := by
  classical
  rw [cyclicVector, lp.norm_single (by norm_num : (0 : ENNReal) < 2), positiveVector_norm_sq]

def positiveExtension (ψ : A →ₚ[ℂ] ℂ) : predual A :=
  coefficientVector (algebra A) (cyclicVector A ψ) (cyclicVector A ψ)

@[simp] theorem positiveExtension_apply (ψ : A →ₚ[ℂ] ℂ) (a : A) :
    restriction A (positiveExtension A ψ) a = ψ a :=
  cyclicVector_coefficient A ψ a

theorem positiveExtension_norm_le (ψ : A →ₚ[ℂ] ℂ) :
    ‖positiveExtension A ψ‖ ≤ ‖ψ 1‖ := by
  calc
    ‖positiveExtension A ψ‖ ≤ ‖cyclicVector A ψ‖ * ‖cyclicVector A ψ‖ :=
      coefficientVector_norm_le _ _ _
    _ = ‖ψ 1‖ := by rw [← pow_two, cyclicVector_norm_sq]

def fourCombination (e : Fin 4 → predual A) : predual A :=
  e 0 - e 1 + Complex.I • (e 2 - e 3)

theorem restriction_fourCombination (e : Fin 4 → predual A) :
    restriction A (fourCombination A e) =
      restriction A (e 0) - restriction A (e 1) +
        Complex.I • (restriction A (e 2) - restriction A (e 3)) := by
  apply ContinuousLinearMap.ext
  intro a
  rfl

theorem fourCombination_norm_le (e : Fin 4 → predual A) (N : ℝ)
    (he : ∀ i : Fin 4, ‖e i‖ ≤ N) : ‖fourCombination A e‖ ≤ 4 * N := by
  exact generic_fourTerm_norm_le e N he

/-- Every original dual functional has a coefficient-predual extension. The
factor four is an extension existence bound, not a claimed isometry. -/
theorem exists_predual_extension (φ : StrongDual ℂ A) :
    ∃ Φ : predual A, restriction A Φ = φ ∧ ‖Φ‖ ≤ 4 * ‖φ‖ := by
  classical
  let e : Fin 4 → predual A := fun i => positiveExtension A (fourPositiveFamily A φ i)
  have he (i : Fin 4) : ‖e i‖ ≤ ‖φ‖ :=
    (positiveExtension_norm_le A (fourPositiveFamily A φ i)).trans
      (fourPositiveFamily_norm A φ i)
  refine ⟨fourCombination A e, ?_, fourCombination_norm_le A e ‖φ‖ he⟩
  · refine (restriction_fourCombination A e).trans ?_
    ext a
    change restriction A (e 0) a - restriction A (e 1) a +
      Complex.I * (restriction A (e 2) a - restriction A (e 3) a) = φ a
    simp only [e, positiveExtension_apply]
    exact (fourPositiveFamily_apply A φ a).symm

theorem restriction_surjective : Function.Surjective (restriction A) :=
  fun φ => (exists_predual_extension A φ).elim (fun Φ h => ⟨Φ, h.1⟩)

end SpectralIsometry.BidualFoundation.UniversalWeakClosure

