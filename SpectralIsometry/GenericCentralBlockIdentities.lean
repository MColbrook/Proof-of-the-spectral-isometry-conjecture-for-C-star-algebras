module

public import SpectralIsometry.CornerFamilyHolomorphic

/-!
# Generic Central Block Identities

Supporting results for spectral isometries of complex unital C*-algebras.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open OAI.HochschildCorners

namespace SpectralIsometry.GenericCentralBlockIdentities

open FiniteQuotientAssembly CornerFamilyHolomorphic
variable {M : Type*} [CStarAlgebra M]

@[simp] theorem centralBlock_coe (p : M) (hp : IsStarProjection p)
    (hpc : ∀ x : M, p*x=x*p) (V : M →L[ℂ] M) (a : Corner p hp) :
    (centralBlockCLM p hp hpc V a : M)=p*V (a:M) := rfl

theorem compression_of_corner_add (p q : M) (hp : IsStarProjection p)
    (hq : IsStarProjection q) (hpc : ∀ x : M, p*x=x*p)
    (V : M →L[ℂ] M) (a : Corner p hp) (f : Corner q hq) :
    centralCompressionHom p hp hpc (V ((a:M)+(f:M)))=
      centralBlockCLM p hp hpc V a+crossBlockCLM p hp hpc q hq V f := by
  apply Subtype.ext
  change p*V ((a:M)+(f:M))=p*V (a:M)+p*V (f:M)
  rw [map_add,mul_add]

@[simp] theorem centralBlock_id (p : M) (hp : IsStarProjection p)
    (hpc : ∀ x : M, p*x=x*p) :
    centralBlockCLM p hp hpc (ContinuousLinearMap.id ℂ M)=ContinuousLinearMap.id ℂ (Corner p hp) := by
  apply ContinuousLinearMap.ext
  intro a
  apply Subtype.ext
  exact a.property.1

@[simp] theorem crossBlock_id (p q : M) (hp : IsStarProjection p)
    (hq : IsStarProjection q) (hpc : ∀ x : M, p*x=x*p) (hsum : p+q=1) :
    crossBlockCLM p hp hpc q hq (ContinuousLinearMap.id ℂ M)=0 := by
  apply ContinuousLinearMap.ext
  intro f
  apply Subtype.ext
  change p*(f:M)=0
  have hpq : p=1-q := eq_sub_iff_add_eq.mpr hsum
  rw [hpq,sub_mul,one_mul,f.property.1,sub_self]

theorem corner_square_zero_of_coe (p : M) (hp : IsStarProjection p)
    (V : M →L[ℂ] M) (R : Corner p hp →L[ℂ] Corner p hp)
    (hcoe : ∀ a : Corner p hp, (R a:M)=V (a:M))
    (hV : ∀ x : M, x^2=0 → (V x)^2=0) :
    ∀ a : Corner p hp, a^2=0 → (R a)^2=0 := by
  intro a ha
  have haM : (a:M)^2=0 := by
    have hh := congrArg Subtype.val ha
    simpa only [pow_two,corner_coe_mul,corner_coe_zero] using hh
  apply Subtype.ext
  have hh := hV (a:M) haM
  simpa only [pow_two,corner_coe_mul,corner_coe_zero,hcoe] using hh

end SpectralIsometry.GenericCentralBlockIdentities

