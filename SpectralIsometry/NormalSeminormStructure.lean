module
public import SpectralIsometry.NormalSeminorm
public import Mathlib.Analysis.Normed.Lp.ProdLp
public import Mathlib.Analysis.Normed.Module.Seminorm.Basic
public import Mathlib.Analysis.LocallyConvex.WithSeminorms

/-!
# Normal Seminorm Structure

Supporting results for spectral isometries of complex unital C*-algebras.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open Filter Topology
open scoped ComplexOrder

namespace SpectralIsometry.NormalSeminorm

variable {M : Type*} [CStarAlgebra M]
local instance structureOrderedM : PartialOrder M := CStarAlgebra.spectralOrder M
local instance structureStarOrderedM : StarOrderedRing M := CStarAlgebra.spectralOrderedRing M
local instance (priority := 2000) structureComplexOrder : PartialOrder ℂ := Complex.partialOrder
local instance (priority := 2000) structureComplexStarOrder : StarOrderedRing ℂ := RCLike.toStarOrderedRing

def gnsPair (ψ : M →ₚ[ℂ] ℂ) (x : M) : WithLp 2 (ψ.PreGNS × ψ.PreGNS) :=
  WithLp.toLp 2 (ψ.toPreGNS x,ψ.toPreGNS (star x))

theorem gnsPair_add (ψ : M →ₚ[ℂ] ℂ) (x y : M) :
    gnsPair ψ (x+y)=gnsPair ψ x+gnsPair ψ y := by
  apply (WithLp.equiv 2 (ψ.PreGNS × ψ.PreGNS)).injective
  simp [gnsPair,star_add,map_add]

theorem gnsPair_norm_sq (ψ : M →ₚ[ℂ] ℂ) (x : M) :
    ‖gnsPair ψ x‖^2=‖ψ.toPreGNS x‖^2+‖ψ.toPreGNS (star x)‖^2 := by
  exact WithLp.prod_norm_sq_eq_of_L2 (gnsPair ψ x)

theorem gnsPair_norm_smul (ψ : M →ₚ[ℂ] ℂ) (c : ℂ) (x : M) :
    ‖gnsPair ψ (c • x)‖=‖c‖*‖gnsPair ψ x‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mp
  rw [gnsPair_norm_sq,mul_pow,gnsPair_norm_sq]
  simp only [star_smul,map_smul,norm_smul,norm_star,RingHom.id_apply]
  ring

theorem preGNS_norm_sq_re (ψ : M →ₚ[ℂ] ℂ) (x : M) :
    ‖ψ.toPreGNS x‖^2=(ψ (star x*x)).re := by
  have h := congrArg Complex.re (ψ.preGNS_norm_sq (ψ.toPreGNS x))
  simpa only [←Complex.ofReal_pow,Complex.ofReal_re,
    PositiveLinearMap.ofPreGNS_toPreGNS] using h

theorem gnsPair_norm_eq_seminorm (ψ : M →ₚ[ℂ] ℂ) (x : M) :
    ‖gnsPair ψ x‖=seminorm ψ x := by
  rw [WithLp.prod_norm_eq_of_L2]
  change Real.sqrt (‖ψ.toPreGNS x‖^2+‖ψ.toPreGNS (star x)‖^2)=seminorm ψ x
  rw [preGNS_norm_sq_re,preGNS_norm_sq_re,star_star]
  rfl

/-- Actual complex seminorm, with the source's exact square-root value. -/
def bundled (ψ : M →ₚ[ℂ] ℂ) : Seminorm ℂ M :=
  Seminorm.of (fun x => ‖gnsPair ψ x‖)
    (fun x y => by rw [gnsPair_add]; exact norm_add_le _ _)
    (gnsPair_norm_smul ψ)

@[simp] theorem bundled_apply (ψ : M →ₚ[ℂ] ℂ) (x : M) :
    bundled ψ x=seminorm ψ x := gnsPair_norm_eq_seminorm ψ x

theorem seminorm_add_le (ψ : M →ₚ[ℂ] ℂ) (x y : M) :
    seminorm ψ (x+y)≤seminorm ψ x+seminorm ψ y := by
  simpa only [bundled_apply] using (map_add_le_add (bundled ψ) x y)

theorem seminorm_smul (ψ : M →ₚ[ℂ] ℂ) (c : ℂ) (x : M) :
    seminorm ψ (c • x)=‖c‖*seminorm ψ x := by
  simpa only [bundled_apply] using (map_smul_eq_mul (bundled ψ) c x)

end SpectralIsometry.NormalSeminorm

