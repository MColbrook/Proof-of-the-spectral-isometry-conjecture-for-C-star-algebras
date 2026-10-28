module

public import SpectralIsometry.StrongStarApproximation
public import Mathlib.Analysis.InnerProductSpace.StarOrder
public import Mathlib.Analysis.CStarAlgebra.Hom
public import Mathlib.Analysis.VonNeumannAlgebra.Basic

/-!
# Concrete Corner Operators

Supporting results for spectral isometries of complex unital C*-algebras.
-/

@[expose] public section
noncomputable section

open scoped InnerProductSpace ComplexOrder CStarAlgebra

namespace SpectralIsometry.ConcreteCorner

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

def compress (V : K →ₗᵢ[ℂ] H) : (H →L[ℂ] H) →L[ℂ] (K →L[ℂ] K) :=
  ((ContinuousLinearMap.compL ℂ K H K) V.toContinuousLinearMap.adjoint).comp
    ((ContinuousLinearMap.compL ℂ K H H).flip V.toContinuousLinearMap)

def lift (V : K →ₗᵢ[ℂ] H) (T : K →L[ℂ] K) : H →L[ℂ] H :=
  V.toContinuousLinearMap.comp (T.comp V.toContinuousLinearMap.adjoint)

def projection (V : K →ₗᵢ[ℂ] H) : H →L[ℂ] H :=
  V.toContinuousLinearMap.comp V.toContinuousLinearMap.adjoint

lemma adjoint_apply (V : K →ₗᵢ[ℂ] H) (x : K) :
    V.toContinuousLinearMap.adjoint (V x) = x :=
  congrArg (fun T : K →L[ℂ] K => T x) V.adjoint_comp_self

@[simp] lemma compress_apply (V : K →ₗᵢ[ℂ] H) (T : H →L[ℂ] H) (x : K) :
    compress V T x = V.toContinuousLinearMap.adjoint (T (V x)) := rfl

@[simp] lemma lift_apply (V : K →ₗᵢ[ℂ] H) (T : K →L[ℂ] K) (x : H) :
    lift V T x = V (T (V.toContinuousLinearMap.adjoint x)) := rfl

@[simp] lemma compress_lift (V : K →ₗᵢ[ℂ] H) (T : K →L[ℂ] K) :
    compress V (lift V T) = T := by ext x; simp only [compress_apply,lift_apply,adjoint_apply]

lemma lift_injective (V : K →ₗᵢ[ℂ] H) : Function.Injective (lift V) := by
  intro T U h
  have he := congrArg (compress V) h
  simpa only [compress_lift] using he

lemma lift_mul (V : K →ₗᵢ[ℂ] H) (T U : K →L[ℂ] K) : lift V (T*U) = lift V T*lift V U := by
  ext x
  simp only [lift_apply,mul_apply_eq_comp,adjoint_apply]

lemma lift_star (V : K →ₗᵢ[ℂ] H) (T : K →L[ℂ] K) : lift V (star T) = star (lift V T) := by
  change V.toContinuousLinearMap.comp (T.adjoint.comp V.toContinuousLinearMap.adjoint) =
    (V.toContinuousLinearMap.comp (T.comp V.toContinuousLinearMap.adjoint)).adjoint
  rw [ContinuousLinearMap.adjoint_comp,ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.adjoint_adjoint,ContinuousLinearMap.comp_assoc]

lemma compress_star (V : K →ₗᵢ[ℂ] H) (T : H →L[ℂ] H) :
    compress V (star T) = star (compress V T) := by
  change V.toContinuousLinearMap.adjoint.comp (T.adjoint.comp V.toContinuousLinearMap) =
    (V.toContinuousLinearMap.adjoint.comp (T.comp V.toContinuousLinearMap)).adjoint
  rw [ContinuousLinearMap.adjoint_comp,ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.adjoint_adjoint,ContinuousLinearMap.comp_assoc]

def liftHom (V : K →ₗᵢ[ℂ] H) : (K →L[ℂ] K) →⋆ₙₐ[ℂ] (H →L[ℂ] H) where
  toFun := lift V
  map_zero' := by ext x; simp
  map_add' T U := by ext x; simp
  map_smul' c T := by ext x; simp
  map_mul' := lift_mul V
  map_star' := lift_star V

lemma projection_apply (V : K →ₗᵢ[ℂ] H) (x : H) :
    projection V x = V (V.toContinuousLinearMap.adjoint x) := rfl

@[simp] lemma projection_inclusion (V : K →ₗᵢ[ℂ] H) (x : K) : projection V (V x) = V x := by
  rw [projection_apply,adjoint_apply]

lemma lift_compress (V : K →ₗᵢ[ℂ] H) (T : H →L[ℂ] H) :
    lift V (compress V T) = projection V * T * projection V := by ext x; rfl

lemma inclusion_intertwines (V : K →ₗᵢ[ℂ] H) (T : H →L[ℂ] H)
    (hT : Commute T (projection V)) (x : K) : T (V x) = V (compress V T x) := by
  have he := congrArg (fun R : H →L[ℂ] H => R (V x)) hT.eq
  simpa only [mul_apply_eq_comp,projection_inclusion,projection_apply,compress_apply,adjoint_apply] using he

lemma adjoint_intertwines (V : K →ₗᵢ[ℂ] H) (T : H →L[ℂ] H)
    (hT : Commute T (projection V)) (x : H) :
    compress V T (V.toContinuousLinearMap.adjoint x) = V.toContinuousLinearMap.adjoint (T x) := by
  have he := congrArg (fun R : H →L[ℂ] H => R x) hT.eq
  change T (projection V x) = projection V (T x) at he
  change V.toContinuousLinearMap.adjoint (T (projection V x)) = _
  rw [he,projection_apply,adjoint_apply]

lemma lift_mul_right (V : K →ₗᵢ[ℂ] H) (T : K →L[ℂ] K) (b : H →L[ℂ] H)
    (hb : Commute b (projection V)) : lift V T*b = lift V (T*compress V b) := by
  ext x
  simp only [mul_apply_eq_comp,lift_apply]
  rw [adjoint_intertwines V b hb]

lemma lift_mul_left (V : K →ₗᵢ[ℂ] H) (T : K →L[ℂ] K) (b : H →L[ℂ] H)
    (hb : Commute b (projection V)) : b*lift V T = lift V (compress V b*T) := by
  ext x
  simp only [mul_apply_eq_comp,lift_apply]
  exact inclusion_intertwines V b hb _

lemma lift_commute_iff (V : K →ₗᵢ[ℂ] H) (T : K →L[ℂ] K) (b : H →L[ℂ] H)
    (hb : Commute b (projection V)) : Commute (lift V T) b ↔ Commute T (compress V b) := by
  simp only [Commute,SemiconjBy,lift_mul_right V T b hb,lift_mul_left V T b hb,
    (lift_injective V).eq_iff]

def restrictHom {A : Type*} [CStarAlgebra A] (V : K →ₗᵢ[ℂ] H)
    (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (hπ : ∀ a, Commute (π a) (projection V)) :
    A →⋆ₐ[ℂ] (K →L[ℂ] K) where
  toFun a := compress V (π a)
  map_zero' := by simp
  map_one' := by ext x; simp [adjoint_apply]
  map_add' a b := by simp
  map_mul' a b := by
    ext x
    simp only [map_mul,compress_apply,mul_apply_eq_comp]
    exact congrArg (fun y : H => V.toContinuousLinearMap.adjoint (π a y))
      (inclusion_intertwines V (π b) (hπ b) x)
  commutes' c := by
    ext x
    change V.toContinuousLinearMap.adjoint (π ((algebraMap ℂ A) c) (V x)) = _
    simp only [Algebra.algebraMap_eq_smul_one,map_smul,map_one,smul_apply,one_apply_eq_self,adjoint_apply]
  map_star' a := by
    change V.toContinuousLinearMap.adjoint.comp ((π (star a)).comp V.toContinuousLinearMap) =
      (V.toContinuousLinearMap.adjoint.comp ((π a).comp V.toContinuousLinearMap)).adjoint
    rw [map_star,ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint_comp,
      ContinuousLinearMap.adjoint_comp,ContinuousLinearMap.adjoint_adjoint,ContinuousLinearMap.comp_assoc]

def commutantOf (A : StarSubalgebra ℂ (K →L[ℂ] K)) : VonNeumannAlgebra K where
  toStarSubalgebra := StarSubalgebra.centralizer ℂ (A : Set (K →L[ℂ] K))
  centralizer_centralizer' := by simp

lemma mem_commutantOf_iff (A : StarSubalgebra ℂ (K →L[ℂ] K)) (T : K →L[ℂ] K) :
    T ∈ commutantOf A ↔ ∀ b ∈ A, Commute b T := by
  change T ∈ StarSubalgebra.centralizer ℂ (A : Set (K →L[ℂ] K)) ↔ _
  rw [StarSubalgebra.mem_centralizer_iff]
  constructor
  · intro h b hb
    exact (h b hb).1
  · intro h b hb
    exact ⟨h b hb,h (star b) (A.star_mem' hb)⟩

lemma commutant_commutes (M : VonNeumannAlgebra H) (V : K →ₗᵢ[ℂ] H)
    (hp : projection V ∈ M) (b : M.commutant.toStarSubalgebra) :
    Commute (b : H →L[ℂ] H) (projection V) :=
  (show Commute (projection V) (b : H →L[ℂ] H) from
    VonNeumannAlgebra.mem_commutant_iff.mp b.property _ hp).symm

def commutantHom (M : VonNeumannAlgebra H) (V : K →ₗᵢ[ℂ] H) (hp : projection V ∈ M) :
    M.commutant.toStarSubalgebra →⋆ₐ[ℂ] (K →L[ℂ] K) where
  toFun a := compress V (a : H →L[ℂ] H)
  map_zero' := by ext x; simp
  map_one' := by ext x; simp [adjoint_apply]
  map_add' a b := by ext x; simp
  map_mul' a b := by
    ext x
    change V.toContinuousLinearMap.adjoint ((a : H →L[ℂ] H) ((b : H →L[ℂ] H) (V x))) =
      V.toContinuousLinearMap.adjoint ((a : H →L[ℂ] H) (V (compress V (b : H →L[ℂ] H) x)))
    rw [inclusion_intertwines V (b : H →L[ℂ] H) (commutant_commutes M V hp b)]
  commutes' c := by
    ext x
    change V.toContinuousLinearMap.adjoint (c • V x) = c • x
    rw [map_smul,adjoint_apply]
  map_star' a := by
    change compress V (star (a : H →L[ℂ] H)) = star (compress V (a : H →L[ℂ] H))
    exact compress_star V (a : H →L[ℂ] H)

def algebra (M : VonNeumannAlgebra H) (V : K →ₗᵢ[ℂ] H) (hp : projection V ∈ M) : VonNeumannAlgebra K :=
  commutantOf (commutantHom M V hp).range

lemma mem_algebra_iff (M : VonNeumannAlgebra H) (V : K →ₗᵢ[ℂ] H) (hp : projection V ∈ M)
    (T : K →L[ℂ] K) : T ∈ algebra M V hp ↔ lift V T ∈ M := by
  rw [algebra,mem_commutantOf_iff]
  conv_rhs => rw [←M.commutant_commutant,VonNeumannAlgebra.mem_commutant_iff]
  constructor
  · intro h b hb
    have hc := h _ (show commutantHom M V hp (⟨b,hb⟩ : M.commutant.toStarSubalgebra) ∈
      (commutantHom M V hp).range from Set.mem_range_self _)
    have ht : Commute T (compress V b) := hc.symm
    exact ((lift_commute_iff V T b (commutant_commutes M V hp ⟨b,hb⟩)).mpr ht).eq.symm
  · intro h b hb
    obtain ⟨c,rfl⟩ := hb
    have hc : Commute (lift V T) (c : H →L[ℂ] H) :=
      (show Commute (c : H →L[ℂ] H) (lift V T) from h c c.property).symm
    exact ((lift_commute_iff V T c (commutant_commutes M V hp c)).mp hc).symm

lemma compress_mem (M : VonNeumannAlgebra H) (V : K →ₗᵢ[ℂ] H) (hp : projection V ∈ M)
    (T : H →L[ℂ] H) (hT : T ∈ M) : compress V T ∈ algebra M V hp := by
  rw [mem_algebra_iff,lift_compress]
  exact M.mul_mem (M.mul_mem hp hT) hp

lemma lift_norm (V : K →ₗᵢ[ℂ] H) (T : K →L[ℂ] K) : ‖lift V T‖ = ‖T‖ :=
  NonUnitalStarAlgHom.norm_map (liftHom V) (lift_injective V) T

end SpectralIsometry.ConcreteCorner

