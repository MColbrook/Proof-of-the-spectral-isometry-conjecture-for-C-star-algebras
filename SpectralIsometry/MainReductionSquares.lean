module

public import SpectralIsometry.MainReduction
import Mathlib.Tactic.NoncommRing

/-!
# Main Reduction Squares

Supporting results for spectral isometries of complex unital C*-algebras.
-/

/- Source317--364 conditional main reduction, restricted-map/Nagasawa/squares
assembly. The explicit AllTransportedLeibniz premise must still be proved by
actual entire_group; this file neither assumes it as an axiom nor claims main_result.
E_h has only its derived commutative Banach-algebra structure, no assumed star.
Proof reuse/attribution is recorded beside the copied polarization bodies and
in reviews/main-reduction-development-notes.md. Lean4.35.0-rc3, pinned Mathlib
b63f6e8a68d220e3b3bc4f3792bb53650d375f24, Apache-2.0. -/

@[expose] public section
noncomputable section
namespace SpectralIsometry.MainReduction
variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]

def restrictedMap (U : A ≃L[ℂ] B) (h1 : U 1=1) (hder : AllTransportedLeibniz U)
    (h : selfAdjoint A) : relativeBicommutant h →ₗ[ℂ] imageBicommutantAlgebra U h1 hder h where
  toFun c := ⟨U (c:A),by
    change U (c:A)∈(imageBicommutantAlgebra U h1 hder h:Set B)
    rw [imageBicommutantAlgebra_coe U h1 hder h]
    exact ⟨(c:A),c.property,rfl⟩⟩
  map_add' c d := by
    apply Subtype.ext
    exact U.map_add (c:A) (d:A)
  map_smul' r c := by
    apply Subtype.ext
    change U (r•(c:A))=r•U (c:A)
    exact U.map_smul r (c:A)

@[simp] theorem restrictedMap_apply (U : A ≃L[ℂ] B) (h1 : U 1=1)
    (hder : AllTransportedLeibniz U) (h : selfAdjoint A) (c : relativeBicommutant h) :
    ((restrictedMap U h1 hder h c : imageBicommutantAlgebra U h1 hder h):B)=U (c:A) := rfl

theorem restrictedMap_surjective (U : A ≃L[ℂ] B) (h1 : U 1=1)
    (hder : AllTransportedLeibniz U) (h : selfAdjoint A) :
    Function.Surjective (restrictedMap U h1 hder h) := by
  intro w
  have hw : (w:B)∈U '' (relativeBicommutant h:Set A) := by
    rw [←imageBicommutantAlgebra_coe U h1 hder h]
    exact w.property
  obtain ⟨a,ha,haw⟩ := hw
  exact ⟨⟨a,ha⟩,Subtype.ext haw⟩

theorem restrictedMap_one (U : A ≃L[ℂ] B) (h1 : U 1=1)
    (hder : AllTransportedLeibniz U) (h : selfAdjoint A) :
    restrictedMap U h1 hder h 1=1 := Subtype.ext h1

theorem restrictedMap_preservesRadius (U : A ≃L[ℂ] B) (h1 : U 1=1)
    (hr : PreservesRadius U.toLinearEquiv.toLinearMap) (hder : AllTransportedLeibniz U)
    (h : selfAdjoint A) (c : relativeBicommutant h) :
    spectralRadius ℂ (restrictedMap U h1 hder h c)=spectralRadius ℂ c := by
  rw [closed_subalgebra_spectralRadius (imageBicommutantAlgebra U h1 hder h)
      (imageBicommutantAlgebra_isClosed U h1 hder h),restrictedMap_apply]
  calc
    spectralRadius ℂ (U (c : A)) = spectralRadius ℂ (c : A) := hr (c : A)
    _ = spectralRadius ℂ c :=
      (closed_subalgebra_spectralRadius (relativeBicommutant h).toSubalgebra
        (relativeBicommutant_isClosed h) c).symm

/-- The literal source multiplicativity conclusion for the restricted map. -/
theorem relativeBicommutant_multiplicative (U : A ≃L[ℂ] B) (h1 : U 1=1)
    (hr : PreservesRadius U.toLinearEquiv.toLinearMap) (hder : AllTransportedLeibniz U)
    (h : selfAdjoint A) (c d : relativeBicommutant h) :
    U ((c:A)*(d:A))=U (c:A)*U (d:A) := by
  let E := imageBicommutantAlgebra U h1 hder h
  letI : CompleteSpace E := (imageBicommutantAlgebra_isClosed U h1 hder h).completeSpace_coe
  letI : NormedCommRing E :=
    { (inferInstance : NormedRing E) with mul_comm:=imageBicommutant_mul_comm U h1 hr hder h }
  have hm := CommutativeReduction.commutative_multiplicative (restrictedMap U h1 hder h)
    (restrictedMap_surjective U h1 hder h) (restrictedMap_one U h1 hder h)
    (restrictedMap_preservesRadius U h1 hr hder h) c d
  exact congrArg (fun w:E => (w:B)) hm

/-- Nagasawa's exact checked C*-source reduction applies after E_h commutativity
has been proved. E_h is never assumed star closed. -/
theorem relativeBicommutant_squares (U : A ≃L[ℂ] B) (h1 : U 1=1)
    (hr : PreservesRadius U.toLinearEquiv.toLinearMap) (hder : AllTransportedLeibniz U)
    (h : selfAdjoint A) (c : relativeBicommutant h) : U ((c:A)^2)=(U (c:A))^2 := by
  let E := imageBicommutantAlgebra U h1 hder h
  letI : CompleteSpace E := (imageBicommutantAlgebra_isClosed U h1 hder h).completeSpace_coe
  letI : NormedCommRing E :=
    { (inferInstance : NormedRing E) with mul_comm:=imageBicommutant_mul_comm U h1 hr hder h }
  have hs := CommutativeReduction.commutative_squares (restrictedMap U h1 hder h)
    (restrictedMap_surjective U h1 hder h) (restrictedMap_one U h1 hder h)
    (restrictedMap_preservesRadius U h1 hr hder h) c
  exact congrArg (fun w:E => (w:B)) hs

theorem selfadjoint_squares_of_all_transported_leibniz (U : A ≃L[ℂ] B) (h1 : U 1=1)
    (hr : PreservesRadius U.toLinearEquiv.toLinearMap) (hder : AllTransportedLeibniz U)
    (h : A) (hsa : IsSelfAdjoint h) : U (h^2)=(U h)^2 := by
  let k : selfAdjoint A := ⟨h,hsa⟩
  exact relativeBicommutant_squares U h1 hr hder k
    ⟨h,self_mem_relativeBicommutant k⟩

/- Proof reuse: the following polarization/decomposition proof is copied from
Solution.CommutativeReduction's private jordan_product_from_selfadjoint and
all_squares_from_selfadjoint. Its algebra works in these general C*-algebras;
the source's commutativity assumptions are not used by these two proof bodies. -/
private theorem jordan_product_from_selfadjoint (T : A →ₗ[ℂ] B)
    (hs : ∀ h : A, IsSelfAdjoint h → T (h ^ 2) = (T h) ^ 2)
    (h k:A) (hh:IsSelfAdjoint h) (hk:IsSelfAdjoint k) :
    T (h * k + k * h) = T h * T k + T k * T h := by
  calc
    T (h*k+k*h) = T ((h+k)^2-h^2-k^2) := by congr 1; noncomm_ring
    _ = (T (h+k))^2-(T h)^2-(T k)^2 := by
      rw [map_sub,map_sub,hs (h+k) (hh.add hk),hs h hh,hs k hk]
    _ =T h*T k+T k*T h := by rw[map_add];noncomm_ring

theorem all_squares_of_selfadjoint_squares (T:A→ₗ[ℂ] B)
    (hs : ∀ h : A, IsSelfAdjoint h → T (h ^ 2) = (T h) ^ 2) :
    ∀ a : A, T (a ^ 2) = (T a) ^ 2 := by
  intro a
  let h:A := (realPart a:A)
  let k:A := (imaginaryPart a:A)
  have hh:IsSelfAdjoint h := (realPart a).property
  have hk:IsSelfAdjoint k := (imaginaryPart a).property
  have ha:a=h+Complex.I•k := (realPart_add_I_smul_imaginaryPart a).symm
  have hexp (x y:A) : (x+Complex.I•y)^2=x^2-y^2+Complex.I•(x*y+y*x) := by
    simp [pow_two,mul_add,add_mul,smul_add,smul_smul,Complex.I_mul_I,sub_eq_add_neg]
    abel
  have hexpB (x y:B) : (x+Complex.I•y)^2=x^2-y^2+Complex.I•(x*y+y*x) := by
    simp [pow_two,mul_add,add_mul,smul_add,smul_smul,Complex.I_mul_I,sub_eq_add_neg]
    abel
  rw [ha,hexp,map_add,map_sub,map_smul,hs h hh,hs k hk,
    jordan_product_from_selfadjoint T hs h k hh hk,map_add,map_smul,hexpB]

/-- Explicit conditional reduction, not the manuscript's main_result. The
entire-group proof must still discharge AllTransportedLeibniz. -/
theorem jordan_reduction_of_all_transported_leibniz (T:A→ₗ[ℂ] B)
    (honto:Function.Surjective T) (hr:PreservesRadius T) (h1:T 1=1)
    (hder:AllTransportedLeibniz (radiusEquiv T honto hr)) : IsJordanIsomorphism T := by
  let U := radiusEquiv T honto hr
  have hU1:U 1=1 := h1
  have hUr:PreservesRadius U.toLinearEquiv.toLinearMap := hr
  refine ⟨⟨injective_of_preservesRadius T hr,honto⟩,?_⟩
  apply all_squares_of_selfadjoint_squares T
  intro h hsa
  exact selfadjoint_squares_of_all_transported_leibniz U hU1 hUr hder h hsa

end SpectralIsometry.MainReduction
