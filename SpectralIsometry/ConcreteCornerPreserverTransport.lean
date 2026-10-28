module

public import SpectralIsometry.ConcreteCornerTopology
public import SpectralIsometry.SquareZeroPreserver

/-!
# Concrete Corner Preserver Transport

Supporting results for spectral isometries of complex unital C*-algebras.
-/

 

@[expose] public section
set_option autoImplicit false
noncomputable section

open Filter Topology
open scoped ComplexOrder CStarAlgebra
open OAI.HochschildCorners
open SpectralIsometry.StrongStarApproximation

namespace SpectralIsometry.ConcreteCorner

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def transport (M : VonNeumannAlgebra H) (p : M) (hp : IsStarProjection p)
    (R : Corner p hp →L[ℂ] Corner p hp) : model M p hp →L[ℂ] model M p hp :=
  (continuousEquivalence M p hp).symm.toContinuousLinearMap.comp
    (R.comp (continuousEquivalence M p hp).toContinuousLinearMap)

@[simp] theorem equivalence_transport (M : VonNeumannAlgebra H) (p : M) (hp : IsStarProjection p)
    (R : Corner p hp →L[ℂ] Corner p hp) (a : model M p hp) :
    equivalence M p hp (transport M p hp R a) = R (equivalence M p hp a) := by
  change equivalence M p hp ((equivalence M p hp).symm (R (equivalence M p hp a))) = _
  exact (equivalence M p hp).apply_symm_apply _

theorem transport_surjective (M : VonNeumannAlgebra H) (p : M) (hp : IsStarProjection p)
    (R : Corner p hp →L[ℂ] Corner p hp) (hR : Function.Surjective R) :
    Function.Surjective (transport M p hp R) := by
  intro b
  obtain ⟨a,ha⟩ := hR (equivalence M p hp b)
  refine ⟨(equivalence M p hp).symm a,?_⟩
  apply (equivalence M p hp).injective
  change equivalence M p hp (transport M p hp R ((equivalence M p hp).symm a)) =
    equivalence M p hp b
  rw [equivalence_transport,(equivalence M p hp).apply_symm_apply,ha]

theorem transport_preservesSquareZero (M : VonNeumannAlgebra H) (p : M) (hp : IsStarProjection p)
    (R : Corner p hp →L[ℂ] Corner p hp)
    (hR : SpectralIsometry.SquareZeroPreserver.PreservesSquareZero R.toLinearMap) :
    SpectralIsometry.SquareZeroPreserver.PreservesSquareZero (transport M p hp R).toLinearMap := by
  intro a ha
  have hzero : (equivalence M p hp a)^2 = 0 := by rw [←map_pow,ha,map_zero]
  have hh := hR (equivalence M p hp a) hzero
  apply (equivalence M p hp).injective
  change equivalence M p hp ((transport M p hp R a)^2) = equivalence M p hp 0
  calc
    equivalence M p hp ((transport M p hp R a)^2) =
        (equivalence M p hp (transport M p hp R a))^2 :=
      map_pow (equivalence M p hp) _ _
    _ = (R (equivalence M p hp a))^2 := by rw [equivalence_transport]
    _ = 0 := hh
    _ = equivalence M p hp 0 := (map_zero (equivalence M p hp)).symm

theorem equivalence_transport_weight (M : VonNeumannAlgebra H) (p : M) (hp : IsStarProjection p)
    (R : Corner p hp →L[ℂ] Corner p hp) :
    equivalence M p hp (transport M p hp R 1) = R 1 := by rw [equivalence_transport,map_one]

theorem transport_unit_isometries (M : VonNeumannAlgebra H) (p : M) (hp : IsStarProjection p)
    (r s : Corner p hp) (hr : star r*r=1) (hs : star s*s=1) (hrs : star r*s=0) :
    star ((equivalence M p hp).symm r)*(equivalence M p hp).symm r=1 ∧
      star ((equivalence M p hp).symm s)*(equivalence M p hp).symm s=1 ∧
      star ((equivalence M p hp).symm r)*(equivalence M p hp).symm s=0 := by
  let F := (equivalence M p hp).symm
  have hstar (a : Corner p hp) : star (F a) = F (star a) := (map_star F a).symm
  have hmul (a b : Corner p hp) : F a * F b = F (a*b) := (map_mul F a b).symm
  constructor
  · change star (F r) * F r = 1
    rw [hstar r,hmul,hr,map_one]
  constructor
  · change star (F s) * F s = 1
    rw [hstar s,hmul,hs,map_one]
  · change star (F r) * F s = 0
    rw [hstar r,hmul,hrs,map_zero]

theorem transport_bounded_sequence_continuity
    (M : VonNeumannAlgebra H) (p : M) (hp : IsStarProjection p)
    (R : Corner p hp →L[ℂ] Corner p hp)
    (hR : ∀ (a : ℕ → Corner p hp) (b : Corner p hp), (∀ n, ‖a n‖ ≤ 1) →
      StrongStarTendsto (fun n => ((a n : M) : H →L[ℂ] H)) atTop ((b : M) : H →L[ℂ] H) →
      StrongStarTendsto (fun n => ((R (a n) : M) : H →L[ℂ] H)) atTop ((R b : M) : H →L[ℂ] H)) :
    ∀ (a : ℕ → model M p hp) (b : model M p hp), (∀ n, ‖a n‖ ≤ 1) →
      StrongStarTendsto (fun n => (a n : CornerHilbert M p hp →L[ℂ] CornerHilbert M p hp)) atTop
        (b : CornerHilbert M p hp →L[ℂ] CornerHilbert M p hp) →
      StrongStarTendsto (fun n => (transport M p hp R (a n) : CornerHilbert M p hp →L[ℂ] CornerHilbert M p hp)) atTop
        (transport M p hp R b : CornerHilbert M p hp →L[ℂ] CornerHilbert M p hp) := by
  intro a b hnorm hlim
  have hEnorm (n : ℕ) : ‖equivalence M p hp (a n)‖ ≤ 1 := by
    change ‖lift (cornerInclusion M p hp) (a n)‖ ≤ 1
    rw [lift_norm]
    exact hnorm n
  have hE := (strongStarTendsto_equivalence_iff M p hp a b).mpr hlim
  have hRlim := hR (fun n => equivalence M p hp (a n)) (equivalence M p hp b) hEnorm hE
  apply (strongStarTendsto_equivalence_iff M p hp
    (fun n => transport M p hp R (a n)) (transport M p hp R b)).mp
  simpa only [equivalence_transport] using hRlim

theorem central_weight_of_transport (M : VonNeumannAlgebra H) (p : M) (hp : IsStarProjection p)
    (R : Corner p hp →L[ℂ] Corner p hp)
    (hcentral : ∀ b : model M p hp, Commute (transport M p hp R 1) b) :
    ∀ a : Corner p hp, Commute (R 1) a := by
  intro a
  have hh := congrArg (equivalence M p hp) (hcentral ((equivalence M p hp).symm a)).eq
  change R 1 * a = a * R 1
  simpa only [map_mul,equivalence_transport_weight,(equivalence M p hp).apply_symm_apply] using hh

end SpectralIsometry.ConcreteCorner

