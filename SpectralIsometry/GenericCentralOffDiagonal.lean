module
public import SpectralIsometry.GenericWeightedFamilyResult
public import SpectralIsometry.GenericCentralBlockIdentities

/-!
# Generic Central Off Diagonal

Supporting results for spectral isometries of complex unital C*-algebras.
-/

 

@[expose] public section
set_option autoImplicit false
noncomputable section
open OAI.HochschildCorners

namespace SpectralIsometry.GenericCentralOffDiagonal
open FiniteQuotientAssembly CornerFamilyHolomorphic

theorem family_zero {M : Type*} [CStarAlgebra M]
    (p q : M) (hp : IsStarProjection p) (hq : IsStarProjection q)
    (hpc : ∀ a : M, p*a=a*p) (hqc : ∀ a : M, q*a=a*q) (hsum : p+q=1)
    (V : ℂ → M →L[ℂ] M) (R : ℂ → Corner p hp ≃L[ℂ] Corner p hp)
    (hReq : ∀ (z : ℂ) (a : Corner p hp), R z a=centralBlockCLM p hp hpc (V z) a)
    (hR : WeightedFamilyResult.UnitalSquares (fun z => centralBlockCLM p hp hpc (V z)))
    (hinvLeft : ∀ (z : ℂ) (a : Corner p hp),
      centralBlockCLM p hp hpc (V (-z)) (centralBlockCLM p hp hpc (V z) a)=a)
    (hRh : Differentiable ℂ (fun z => centralBlockCLM p hp hpc (V z)))
    (hLh : Differentiable ℂ (fun z => crossBlockCLM p hp hpc q hq (V z)))
    (hrealV : ∀ (z : ℂ) (x : M), IsSelfAdjoint x → ∀ ζ∈spectrum ℂ (V z x), ζ.im=0)
    (hzeroV : ∀ x : M, V 0 x=x) :
    ∀ z : ℂ, crossBlockCLM p hp hpc q hq (V z)=0 := by
  let L : ℂ → Corner q hq →L[ℂ] Corner p hp := fun z => crossBlockCLM p hp hpc q hq (V z)
  have hFun : (fun z : ℂ => (R z).toContinuousLinearMap)=
      (fun z => centralBlockCLM p hp hpc (V z)) := by
    funext z
    exact ContinuousLinearMap.ext (hReq z)
  have hRs : WeightedFamilyResult.UnitalSquares (fun z => (R z).toContinuousLinearMap) := by
    rw [hFun]
    exact hR
  have hRh' : Differentiable ℂ (fun z => (R z).toContinuousLinearMap) := by
    rw [hFun]
    exact hRh
  have hinv (z : ℂ) (a : Corner p hp) : R z (R (-z) a)=a := by
    rw [hReq,hReq]
    simpa only [neg_neg] using hinvLeft (-z) a
  have hreal (z : ℂ) (a : Corner p hp) (ha : IsSelfAdjoint a)
      (f : Corner q hq) (hf : IsSelfAdjoint f) (ζ : ℂ)
      (hζ : ζ∈spectrum ℂ (R z a+L z f)) : ζ.im=0 := by
    have haM : IsSelfAdjoint (a:M) := congrArg Subtype.val ha
    have hfM : IsSelfAdjoint (f:M) := congrArg Subtype.val hf
    have he : centralCompressionHom p hp hpc (V z ((a:M)+(f:M)))=R z a+L z f := by
      rw [hReq]
      exact GenericCentralBlockIdentities.compression_of_corner_add p q hp hq hpc (V z) a f
    rw [←he] at hζ
    exact hrealV z _ (haM.add hfM) ζ
      ((AlgHom.spectrum_apply_subset (centralCompressionHom p hp hpc).toAlgHom _) hζ)
  have hzero : L 0=0 := by
    apply ContinuousLinearMap.ext
    intro f
    apply Subtype.ext
    change p*V 0 (f:M)=0
    rw [hzeroV]
    have hpq : p=1-q := eq_sub_iff_add_eq.mpr hsum
    rw [hpq,sub_mul,one_mul,f.property.1,sub_self]
  exact WeightedFamilyResult.offDiagonal_zero R L hRs hinv hRh' hLh hreal hzero

end SpectralIsometry.GenericCentralOffDiagonal

