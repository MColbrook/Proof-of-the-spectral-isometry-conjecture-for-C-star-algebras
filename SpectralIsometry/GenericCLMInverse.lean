module

public import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
public import Mathlib.Analysis.Normed.Module.Basic

/-!
# GenericCLM Inverse

Supporting results for spectral isometries of complex unital C*-algebras.
-/

 

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace SpectralIsometry.GenericCLMInverse

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

def ofInverses (f : E →L[𝕜] F) (g : F →L[𝕜] E)
    (hgf : ∀ x : E, g (f x)=x) (hfg : ∀ y : F, f (g y)=y) : E ≃L[𝕜] F where
  toLinearEquiv :=
    { toLinearMap := f.toLinearMap
      invFun := g
      left_inv := hgf
      right_inv := hfg }
  continuous_toFun := f.continuous
  continuous_invFun := g.continuous

@[simp] theorem ofInverses_apply (f : E →L[𝕜] F) (g : F →L[𝕜] E)
    (hgf : ∀ x : E, g (f x)=x) (hfg : ∀ y : F, f (g y)=y) (x : E) :
    ofInverses f g hgf hfg x=f x := rfl

@[simp] theorem ofInverses_symm_apply (f : E →L[𝕜] F) (g : F →L[𝕜] E)
    (hgf : ∀ x : E, g (f x)=x) (hfg : ∀ y : F, f (g y)=y) (y : F) :
    (ofInverses f g hgf hfg).symm y=g y := rfl

/-- Box parameter negation before instantiating a large concrete model. -/
theorem rightInv_of_negLeftInv {I E : Type*} [AddGroup I] (f : I → E → E)
    (h : ∀ z x, f (-z) (f z x)=x) (z : I) (x : E) : f z (f (-z) x)=x := by
  have hh := h (-z) x
  simpa only [neg_neg] using hh

end SpectralIsometry.GenericCLMInverse

