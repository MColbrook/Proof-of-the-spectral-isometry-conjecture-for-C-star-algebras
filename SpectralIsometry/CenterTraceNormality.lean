module

public import OAI.Analysis.BoundedHochschild.NormalOperators
public import OAI.Analysis.BoundedHochschild.NormalMultiplication

/-!
# Center Trace Normality

Supporting results for spectral isometries of complex unital C*-algebras.
-/

 

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace SpectralIsometry.CenterTraceNormality

open OAI.HochschildNormalPart OAI.BoundedHochschild OAI.HochschildSakai

universe u v
variable {M X : Type u} [CStarAlgebra M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

local instance orderedM : PartialOrder M := CStarAlgebra.spectralOrder M
local instance starOrderedM : StarOrderedRing M := CStarAlgebra.spectralOrderedRing M

def Central (a : M) : Prop := ∀ b : M, a*b=b*a

theorem normalPart_scalar (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (E : M →L[ℂ] M) (φ : StrongDual ℂ M) (hφ : φ ∈ normalDual e)
    (hfix : φ.comp E=φ) (a : M) :
    φ (operatorNormalPart e E a)=φ a := by
  obtain ⟨z,hz⟩ := (mem_normalDual e φ).mp hφ
  have heq : φ=predualEmbedding e z := by
    ext b
    exact hz b
  rw [heq] at hfix ⊢
  rw [operatorNormalPart_pairing,hfix,scalarNormalPart_fixes e
    (show predualEmbedding e z ∈ normalDual e from ⟨z,rfl⟩)]

theorem normalPart_central (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (E : M →L[ℂ] M) (hc : ∀ a, Central (E a)) :
    ∀ a, Central (operatorNormalPart e E a) := by
  intro a b
  have heq : (ContinuousLinearMap.mul ℂ M b).comp E=
      ((ContinuousLinearMap.mul ℂ M).flip b).comp E := by
    ext c
    exact (hc c b).symm
  have h := congrArg (operatorNormalPart e) heq
  rw [operatorNormalPart_comp_normal e E _ (mul_hasPreadjoint e b),
    operatorNormalPart_comp_normal e E _ (mul_right_hasPreadjoint e b)] at h
  exact (congrArg (fun T : M →L[ℂ] M => T a) h).symm

theorem normal_of_central_pairings (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    {I : Type v} (E : M →L[ℂ] M) (hc : ∀ a, Central (E a))
    (φ : I → StrongDual ℂ M) (hφ : ∀ i, φ i ∈ normalDual e)
    (hpair : ∀ i z, Central z → ∀ a, φ i (z*E a)=φ i (z*a))
    (hsep : ∀ c, Central c → (∀ i, φ i (star c*c)=0) → c=0) :
    HasPreadjoint e E := by
  have hNc := normalPart_central e E hc
  have hEq : operatorNormalPart e E=E := by
    ext a
    let d : M := operatorNormalPart e E a-E a
    have hd : Central d := by
      intro b
      dsimp [d]
      rw [sub_mul,mul_sub,hNc a b,hc a b]
    have hsd : Central (star d) := by
      intro b
      have h := congrArg star (hd (star b))
      simpa only [star_mul,star_star] using h.symm
    have hz : d=0 := hsep d hd (fun i => by
      let ψ : StrongDual ℂ M := (φ i).comp (ContinuousLinearMap.mul ℂ M (star d))
      have hψ : ψ ∈ normalDual e :=
        normalDual_comp e (hφ i) _ (mul_hasPreadjoint e (star d))
      have hfix : ψ.comp E=ψ := by
        ext b
        exact hpair i (star d) hsd b
      have hn := normalPart_scalar e E ψ hψ hfix a
      change φ i (star d*operatorNormalPart e E a)=φ i (star d*a) at hn
      dsimp [d]
      rw [mul_sub,map_sub,hn,hpair i (star d) hsd a,sub_self])
    exact sub_eq_zero.mp hz
  rw [←hEq]
  exact operatorNormalPart_normal e E

end SpectralIsometry.CenterTraceNormality

