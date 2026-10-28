module

public import SpectralIsometry.BidualNormality
public import OAI.Analysis.BoundedHochschild.StarPreduals

/-!
# Generic Predual Star

Supporting results for spectral isometries of complex unital C*-algebras.
-/

 

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace SpectralIsometry.BidualFoundation.CoefficientPredual
attribute [local instance] complexNormedSpaceSelf dualNormedGroup dualNormedSpace
  coefficientNormedGroup coefficientNormedSpace

universe u

def functionalStarLinear {A : Type u} [CStarAlgebra A] (φ : StrongDual ℂ A) : A →ₗ[ℂ] ℂ where
  toFun a := star (φ (star a))
  map_add' a b := by simp only [star_add, map_add]
  map_smul' z a := by simp only [star_smul, map_smul, star_star, RingHom.id_apply]

def functionalStar {A : Type u} [CStarAlgebra A] (φ : StrongDual ℂ A) : StrongDual ℂ A :=
  (functionalStarLinear φ).mkContinuous ‖φ‖ (by
    intro a
    simpa only [functionalStarLinear, LinearMap.coe_mk, AddHom.coe_mk, norm_star] using
      φ.le_opNorm (star a))

@[simp] theorem functionalStar_apply {A : Type u} [CStarAlgebra A]
    (φ : StrongDual ℂ A) (a : A) : functionalStar φ a = star (φ (star a)) := rfl

open OAI.HochschildNormalPart

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (M : VonNeumannAlgebra H)

theorem functionalStar_mem_coefficientPredual (Φ : coefficientPredual M) :
    functionalStar (Φ : StrongDual ℂ M) ∈ coefficientPredual M := by
  let e := concretePredualIsometry M
  obtain ⟨z, hz⟩ := (mem_normalDual e (Φ : StrongDual ℂ M)).mp
    (coefficientPredual_normal M Φ)
  obtain ⟨w, hw⟩ := OAI.HochschildSakai.exists_star_predual_vector e z
  have hnormal : functionalStar (Φ : StrongDual ℂ M) ∈ normalDual e := by
    apply (mem_normalDual e _).mpr
    refine ⟨w, fun a => ?_⟩
    calc
      functionalStar (Φ : StrongDual ℂ M) a = star ((Φ : StrongDual ℂ M) (star a)) := rfl
      _ = star (star (e.symm (star a) z)) := congrArg star (hz (star a))
      _ = e.symm (star a) z := star_star _
      _ = star (e.symm a w) := hw a
  exact (le_of_eq (normalDual_eq_coefficientPredual M)) hnormal

def starPullback (Φ : coefficientPredual M) : coefficientPredual M :=
  ⟨functionalStar (Φ : StrongDual ℂ M), functionalStar_mem_coefficientPredual M Φ⟩

@[simp] theorem starPullback_apply (Φ : coefficientPredual M) (m : M) :
    ((starPullback M Φ : coefficientPredual M) : StrongDual ℂ M) m =
      star ((Φ : StrongDual ℂ M) (star m)) := rfl

end SpectralIsometry.BidualFoundation.CoefficientPredual

