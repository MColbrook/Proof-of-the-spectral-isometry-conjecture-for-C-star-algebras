module

public import SpectralIsometry.JordanSpectral
public import Mathlib.Analysis.Calculus.FDeriv.CompCLM

/-!
# Off Diagonal Family

Supporting results for spectral isometries of complex unital C*-algebras.
-/

 

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace SpectralIsometry.OffDiagonalFamily

variable {A B F : Type*} [CStarAlgebra A] [CStarAlgebra B] [CStarAlgebra F]

theorem selfAdjoint_of_jordan_real_spectrum_shifts
    (R : A ≃ₗ[ℂ] A) (h1 : R 1 = 1)
    (hsquare : ∀ a : A, R (a^2) = (R a)^2)
    (b c : A) (hc : R c = b)
    (hreal : ∀ a : A, IsSelfAdjoint a → ∀ ζ ∈ spectrum ℂ (R a + b), ζ.im = 0) :
    IsSelfAdjoint c := by
  apply selfadjoint_of_real_spectrum_shifts c
  intro a ha ζ hζ
  have hspec := JordanSpectral.linearEquiv_spectrum R h1 hsquare (a+c)
  have hm : ζ ∈ spectrum ℂ (R (a+c)) := by rw [hspec]; exact hζ
  have he : R (a+c) = R a+b := (map_add R a c).trans (congrArg (fun x : A => R a+x) hc)
  rw [he] at hm
  exact hreal a ha ζ hm

theorem differentiable_transported_component
    (R : ℂ → A →L[ℂ] A) (L : ℂ → F →L[ℂ] A)
    (hR : Differentiable ℂ R) (hL : Differentiable ℂ L) (f : F) :
    Differentiable ℂ (fun z : ℂ => R (-z) (L z f)) := by
  have hRneg : Differentiable ℂ (fun z : ℂ => R (-z)) := hR.comp differentiable_neg
  have hLf : Differentiable ℂ (fun z : ℂ => L z f) := hL.clm_apply (differentiable_const f)
  exact hRneg.clm_apply hLf

theorem offDiagonal_family_eq_zero
    (R : ℂ → A ≃L[ℂ] A) (L : ℂ → F →L[ℂ] A)
    (h1 : ∀ z : ℂ, R z 1 = 1)
    (hsquare : ∀ (z : ℂ) (a : A), R z (a^2) = (R z a)^2)
    (hinv : ∀ (z : ℂ) (a : A), R z (R (-z) a) = a)
    (hR : Differentiable ℂ (fun z : ℂ => (R z).toContinuousLinearMap))
    (hL : Differentiable ℂ L)
    (hreal : ∀ (z : ℂ) (a : A), IsSelfAdjoint a → ∀ f : F, IsSelfAdjoint f →
      ∀ ζ ∈ spectrum ℂ (R z a + L z f), ζ.im = 0)
    (hzero : L 0 = 0) : ∀ z : ℂ, L z = 0 := by
  have hvan (z : ℂ) (f : F) (hf : IsSelfAdjoint f) : L z f = 0 := by
    let c : ℂ → A := fun w => R (-w) (L w f)
    have hhol : Differentiable ℂ c :=
      differentiable_transported_component (fun w => (R w).toContinuousLinearMap) L hR hL f
    have hsa (w : ℂ) : IsSelfAdjoint (c w) :=
      selfAdjoint_of_jordan_real_spectrum_shifts (R w).toLinearEquiv (h1 w) (hsquare w)
        (L w f) (c w) (hinv w (L w f)) (fun a ha => hreal w a ha f hf)
    have hc0 : c 0 = 0 := by
      change R (-0) (L 0 f) = 0
      rw [neg_zero,hzero,ContinuousLinearMap.zero_apply,map_zero]
    have hcz : c z = 0 := (holomorphic_selfadjoint_const c hhol hsa z 0).trans hc0
    have hh := congrArg (R z) hcz
    change R z (R (-z) (L z f)) = R z 0 at hh
    rw [hinv,map_zero] at hh
    exact hh
  intro z
  apply ContinuousLinearMap.ext
  intro f
  change L z f = 0
  have hr : L z (realPart f : F) = 0 := hvan z _ (realPart f).property
  have hi : L z (imaginaryPart f : F) = 0 := hvan z _ (imaginaryPart f).property
  calc
    L z f = L z ((realPart f : F) + Complex.I • (imaginaryPart f : F)) :=
      congrArg (L z) (realPart_add_I_smul_imaginaryPart f).symm
    _ = 0 := by rw [map_add,map_smul,hr,hi,smul_zero,add_zero]

end SpectralIsometry.OffDiagonalFamily

