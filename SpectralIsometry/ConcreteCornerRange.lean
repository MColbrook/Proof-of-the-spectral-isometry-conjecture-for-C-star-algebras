module

public import SpectralIsometry.ConcreteCornerOperators
public import OAI.Analysis.BoundedHochschild.Corners
public import OAI.Analysis.Commutator.VonNeumannCStar

/-!
# Concrete Corner Range

Supporting results for spectral isometries of complex unital C*-algebras.
-/

@[expose] public section
noncomputable section

open scoped InnerProductSpace ComplexOrder CStarAlgebra
open OAI.HochschildCorners

namespace SpectralIsometry.ConcreteCorner

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def HilbertRange (p : H →L[ℂ] H) (_hp : IsStarProjection p) := p.range

instance rangeNorm (p : H →L[ℂ] H) (hp : IsStarProjection p) : NormedAddCommGroup (HilbertRange p hp) :=
  inferInstanceAs (NormedAddCommGroup p.range)

instance rangeInner (p : H →L[ℂ] H) (hp : IsStarProjection p) : InnerProductSpace ℂ (HilbertRange p hp) :=
  inferInstanceAs (InnerProductSpace ℂ p.range)

instance rangeComplete (p : H →L[ℂ] H) (hp : IsStarProjection p) : CompleteSpace (HilbertRange p hp) :=
  (ContinuousLinearMap.IsIdempotentElem.isClosed_range hp.isIdempotentElem).completeSpace_coe

def inclusion (p : H →L[ℂ] H) (hp : IsStarProjection p) : HilbertRange p hp →ₗᵢ[ℂ] H := p.range.subtypeₗᵢ

lemma inclusion_fixed (p : H →L[ℂ] H) (hp : IsStarProjection p) (x : HilbertRange p hp) :
    p (inclusion p hp x) = inclusion p hp x := by
  obtain ⟨y,hy⟩ := x.property
  change p x.val = x.val
  rw [←hy]
  exact congrArg (fun T : H →L[ℂ] H => T y) hp.isIdempotentElem.eq

lemma inclusion_adjoint (p : H →L[ℂ] H) (hp : IsStarProjection p) (x : H) :
    (inclusion p hp).toContinuousLinearMap.adjoint x = (⟨p x,x,rfl⟩ : HilbertRange p hp) := by
  apply ext_inner_right ℂ
  intro y
  rw [ContinuousLinearMap.adjoint_inner_left]
  change inner ℂ x (inclusion p hp y) = inner ℂ (p x) (inclusion p hp y)
  have hs : p.adjoint = p := hp.isSelfAdjoint.star_eq
  calc
    _ = inner ℂ x (p (inclusion p hp y)) := by rw [inclusion_fixed]
    _ = inner ℂ (p.adjoint x) (inclusion p hp y) :=
      (ContinuousLinearMap.adjoint_inner_left p _ x).symm
    _ = _ := congrArg (fun T : H →L[ℂ] H => inner ℂ (T x) (inclusion p hp y)) hs

@[simp] lemma inclusion_projection (p : H →L[ℂ] H) (hp : IsStarProjection p) :
    projection (inclusion p hp) = p := by
  ext x
  rw [projection_apply,inclusion_adjoint]
  rfl

theorem ambientProjection {M : VonNeumannAlgebra H} {p : M} (hp : IsStarProjection p) :
    IsStarProjection (p : H →L[ℂ] H) :=
  ⟨congrArg Subtype.val hp.isIdempotentElem.eq,congrArg Subtype.val hp.isSelfAdjoint.star_eq⟩

abbrev CornerHilbert (M : VonNeumannAlgebra H) (p : M) (hp : IsStarProjection p) :=
  HilbertRange (p : H →L[ℂ] H) (ambientProjection hp)

def cornerInclusion (M : VonNeumannAlgebra H) (p : M) (hp : IsStarProjection p) :
    CornerHilbert M p hp →ₗᵢ[ℂ] H := inclusion _ (ambientProjection hp)

lemma cornerProjection (M : VonNeumannAlgebra H) (p : M) (hp : IsStarProjection p) :
    projection (cornerInclusion M p hp) = (p : H →L[ℂ] H) := inclusion_projection _ _

lemma cornerProjection_mem (M : VonNeumannAlgebra H) (p : M) (hp : IsStarProjection p) :
    projection (cornerInclusion M p hp) ∈ M := by rw [cornerProjection]; exact p.property

def model (M : VonNeumannAlgebra H) (p : M) (hp : IsStarProjection p) :
    VonNeumannAlgebra (CornerHilbert M p hp) :=
  algebra M (cornerInclusion M p hp) (cornerProjection_mem M p hp)

def liftInAmbient (M : VonNeumannAlgebra H) (p : M) (hp : IsStarProjection p)
    (T : model M p hp) : M :=
  ⟨lift (cornerInclusion M p hp) T,
    (mem_algebra_iff M (cornerInclusion M p hp) (cornerProjection_mem M p hp) T).mp T.property⟩

lemma lift_left (M : VonNeumannAlgebra H) (p : M) (hp : IsStarProjection p)
    (T : model M p hp) : p * liftInAmbient M p hp T = liftInAmbient M p hp T := by
  apply Subtype.ext
  change (p : H →L[ℂ] H) * lift (cornerInclusion M p hp) T = lift (cornerInclusion M p hp) T
  have heq := congrArg (fun q : H →L[ℂ] H => q * lift (cornerInclusion M p hp) T)
    (cornerProjection M p hp)
  apply heq.symm.trans
  ext x
  exact projection_inclusion (cornerInclusion M p hp) _

lemma lift_right (M : VonNeumannAlgebra H) (p : M) (hp : IsStarProjection p)
    (T : model M p hp) : liftInAmbient M p hp T * p = liftInAmbient M p hp T := by
  apply Subtype.ext
  change lift (cornerInclusion M p hp) T * (p : H →L[ℂ] H) = lift (cornerInclusion M p hp) T
  have heq := congrArg (fun q : H →L[ℂ] H => lift (cornerInclusion M p hp) T * q)
    (cornerProjection M p hp)
  apply heq.symm.trans
  ext x
  simp only [mul_apply_eq_comp,lift_apply,projection_apply,adjoint_apply]

def liftToCorner (M : VonNeumannAlgebra H) (p : M) (hp : IsStarProjection p)
    (T : model M p hp) : Corner p hp :=
  ⟨liftInAmbient M p hp T,lift_left M p hp T,lift_right M p hp T⟩

def compressToModel (M : VonNeumannAlgebra H) (p : M) (hp : IsStarProjection p)
    (a : Corner p hp) : model M p hp :=
  ⟨compress (cornerInclusion M p hp) ((a : M) : H →L[ℂ] H),
    compress_mem M (cornerInclusion M p hp) (cornerProjection_mem M p hp) _ (a : M).property⟩

lemma compress_liftToCorner (M : VonNeumannAlgebra H) (p : M) (hp : IsStarProjection p)
    (T : model M p hp) : compressToModel M p hp (liftToCorner M p hp T) = T := by
  apply Subtype.ext
  exact compress_lift (cornerInclusion M p hp) T

lemma lift_compressToModel (M : VonNeumannAlgebra H) (p : M) (hp : IsStarProjection p)
    (a : Corner p hp) : liftToCorner M p hp (compressToModel M p hp a) = a := by
  apply Subtype.ext
  apply Subtype.ext
  change lift (cornerInclusion M p hp) (compress (cornerInclusion M p hp) ((a : M) : H →L[ℂ] H)) = _
  rw [lift_compress,cornerProjection]
  exact congrArg Subtype.val (show p * (a : M) * p = (a : M) from by rw [a.property.1,a.property.2])

def liftStarHom (M : VonNeumannAlgebra H) (p : M) (hp : IsStarProjection p) :
    model M p hp →⋆ₐ[ℂ] Corner p hp where
  toFun := liftToCorner M p hp
  map_zero' := by
    apply Subtype.ext; apply Subtype.ext
    exact map_zero (liftHom (cornerInclusion M p hp))
  map_one' := by
    apply Subtype.ext; apply Subtype.ext
    change lift (cornerInclusion M p hp) 1 = (p : H →L[ℂ] H)
    calc
      lift (cornerInclusion M p hp) 1 = projection (cornerInclusion M p hp) := by ext x; rfl
      _ = _ := cornerProjection M p hp
  map_add' T U := by
    apply Subtype.ext; apply Subtype.ext
    exact map_add (liftHom (cornerInclusion M p hp))
      (T : CornerHilbert M p hp →L[ℂ] CornerHilbert M p hp)
      (U : CornerHilbert M p hp →L[ℂ] CornerHilbert M p hp)
  map_mul' T U := by
    apply Subtype.ext; apply Subtype.ext
    exact map_mul (liftHom (cornerInclusion M p hp))
      (T : CornerHilbert M p hp →L[ℂ] CornerHilbert M p hp)
      (U : CornerHilbert M p hp →L[ℂ] CornerHilbert M p hp)
  commutes' c := by
    apply Subtype.ext; apply Subtype.ext
    change lift (cornerInclusion M p hp) (c • (1 : CornerHilbert M p hp →L[ℂ] CornerHilbert M p hp)) =
      c • (p : H →L[ℂ] H)
    calc
      _ = c • lift (cornerInclusion M p hp) 1 := map_smul (liftHom (cornerInclusion M p hp)) c 1
      _ = c • projection (cornerInclusion M p hp) := congrArg (fun T : H →L[ℂ] H => c • T)
        (show lift (cornerInclusion M p hp) 1 = projection (cornerInclusion M p hp) from by ext x; rfl)
      _ = _ := congrArg (fun T : H →L[ℂ] H => c • T) (cornerProjection M p hp)
  map_star' T := by
    apply Subtype.ext; apply Subtype.ext
    exact map_star (liftHom (cornerInclusion M p hp))
      (T : CornerHilbert M p hp →L[ℂ] CornerHilbert M p hp)

def equivalence (M : VonNeumannAlgebra H) (p : M) (hp : IsStarProjection p) :
    model M p hp ≃⋆ₐ[ℂ] Corner p hp where
  toFun := liftToCorner M p hp
  invFun := compressToModel M p hp
  left_inv := compress_liftToCorner M p hp
  right_inv := lift_compressToModel M p hp
  map_add' := map_add (liftStarHom M p hp)
  map_mul' := map_mul (liftStarHom M p hp)
  map_smul' := map_smul (liftStarHom M p hp)
  map_star' := map_star (liftStarHom M p hp)

theorem equivalence_isometry (M : VonNeumannAlgebra H) (p : M) (hp : IsStarProjection p) :
    Isometry (equivalence M p hp) := by
  apply Isometry.of_dist_eq
  intro T U
  rw [dist_eq_norm,dist_eq_norm]
  change ‖lift (cornerInclusion M p hp) (T : CornerHilbert M p hp →L[ℂ] CornerHilbert M p hp) -
      lift (cornerInclusion M p hp) (U : CornerHilbert M p hp →L[ℂ] CornerHilbert M p hp)‖ =
    ‖(T : CornerHilbert M p hp →L[ℂ] CornerHilbert M p hp) - U‖
  calc
    _ = ‖lift (cornerInclusion M p hp)
        ((T : CornerHilbert M p hp →L[ℂ] CornerHilbert M p hp) - U)‖ :=
      congrArg norm (map_sub (liftHom (cornerInclusion M p hp))
        (T : CornerHilbert M p hp →L[ℂ] CornerHilbert M p hp)
        (U : CornerHilbert M p hp →L[ℂ] CornerHilbert M p hp)).symm
    _ = _ := lift_norm (cornerInclusion M p hp) _

theorem equivalence_symm_isometry (M : VonNeumannAlgebra H) (p : M) (hp : IsStarProjection p) :
    Isometry (equivalence M p hp).symm := by
  apply Isometry.of_dist_eq
  intro a b
  have hh := (equivalence_isometry M p hp).dist_eq
    ((equivalence M p hp).symm a) ((equivalence M p hp).symm b)
  simpa only [(equivalence M p hp).apply_symm_apply] using hh.symm

end SpectralIsometry.ConcreteCorner

