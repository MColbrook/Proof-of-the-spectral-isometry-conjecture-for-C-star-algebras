module

public import OAI.Analysis.BoundedHochschild.NormalOperators

/-!
# Generic Scalar Normal Part

Supporting results for spectral isometries of complex unital C*-algebras.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace SpectralIsometry.ScalarNormalPart
open OAI.HochschildNormalPart

universe u
variable {M X : Type u} [CStarAlgebra M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

theorem four_evaluation (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (g : Fin 4 → StrongDual ℂ M) (a : M) :
    scalarNormalPart e (g 0-g 1+Complex.I • (g 2-g 3)) a =
      scalarNormalPart e (g 0) a-scalarNormalPart e (g 1) a+
        Complex.I*(scalarNormalPart e (g 2) a-scalarNormalPart e (g 3) a) := by
  simp only [map_add,map_sub,map_smul,add_apply,sub_apply,
    ContinuousLinearMap.smul_apply,smul_eq_mul]

end SpectralIsometry.ScalarNormalPart

