module

public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.NoncommRing

/-!
# Square Zero Projection Algebra

Supporting results for spectral isometries of complex unital C*-algebras.
-/

 

@[expose] public section
noncomputable section

namespace SpectralIsometry.SquareZeroPreserver

variable {B : Type*} [Ring B]

def WeightedProjectionRelation (u x : B) : Prop :=
  u * x + x * u = 2 * x ^ 2

theorem weightedProjectionRelation_complement (u x : B)
    (hx : WeightedProjectionRelation u x) : WeightedProjectionRelation u (u - x) := by
  have hid : u * (u - x) + (u - x) * u - 2 * (u - x) ^ 2 =
      u * x + x * u - 2 * x ^ 2 := by noncomm_ring
  apply sub_eq_zero.mp
  rw [hid, hx, sub_self]

theorem weightedProjectionRelation_add (u x y : B)
    (hx : WeightedProjectionRelation u x) (hy : WeightedProjectionRelation u y)
    (hxy : x * y + y * x = 0) : WeightedProjectionRelation u (x + y) := by
  have hid : u * (x + y) + (x + y) * u - 2 * (x + y) ^ 2 =
      (u * x + x * u - 2 * x ^ 2) + (u * y + y * u - 2 * y ^ 2) -
        2 * (x * y + y * x) := by noncomm_ring
  apply sub_eq_zero.mp
  rw [hid, hx, hy, hxy]
  simp

theorem commute_square_of_weightedProjectionRelation (u x : B)
    (hx : WeightedProjectionRelation u x) : Commute u (x ^ 2) := by
  have ha : u * x = x * x + x * x - x * u := by
    apply eq_sub_iff_add_eq.mpr
    exact hx.trans (by noncomm_ring)
  have hb : x * u = x * x + x * x - u * x := by
    apply eq_sub_iff_add_eq.mpr
    rw [add_comm]
    exact hx.trans (by noncomm_ring)
  change u * x ^ 2 = x ^ 2 * u
  calc
    u * x ^ 2 = (u * x) * x := by noncomm_ring
    _ = (x * x + x * x - x * u) * x := by rw [ha]
    _ = x * (x * x + x * x - u * x) := by noncomm_ring
    _ = x * (x * u) := by rw [← hb]
    _ = x ^ 2 * u := by noncomm_ring

theorem commute_unitSquare_of_weightedProjectionRelation (u x : B)
    (hx : WeightedProjectionRelation u x) : Commute (u ^ 2) x := by
  have hs := (commute_square_of_weightedProjectionRelation u x hx).eq
  have ha : u * x = x * x + x * x - x * u := by
    apply eq_sub_iff_add_eq.mpr
    exact hx.trans (by noncomm_ring)
  have hb : x * u = x * x + x * x - u * x := by
    apply eq_sub_iff_add_eq.mpr
    rw [add_comm]
    exact hx.trans (by noncomm_ring)
  have hs' : u * (x * x) = (x * x) * u := by simpa only [pow_two] using hs
  change u ^ 2 * x = x * u ^ 2
  calc
    u ^ 2 * x = u * (u * x) := by noncomm_ring
    _ = u * (x * x + x * x - x * u) := by rw [ha]
    _ = u * (x * x) + u * (x * x) - u * x * u := by noncomm_ring
    _ = (x * x) * u + (x * x) * u - u * x * u := by rw [hs']
    _ = (x * x + x * x - u * x) * u := by noncomm_ring
    _ = (x * u) * u := by rw [← hb]
    _ = x * u ^ 2 := by noncomm_ring

theorem commutator_complement_square_identity (u x : B) :
    u * (u - x) ^ 2 - (u - x) ^ 2 * u =
      (u * x ^ 2 - x ^ 2 * u) - (u ^ 2 * x - x * u ^ 2) := by
  noncomm_ring

theorem commute_square_of_complement (u x : B)
    (hc : Commute u ((u - x) ^ 2)) (hs : Commute (u ^ 2) x) :
    Commute u (x ^ 2) := by
  have hid := commutator_complement_square_identity u x
  rw [hc.eq, hs.eq, sub_self, sub_self, sub_zero] at hid
  exact (sub_eq_zero.mp hid.symm)

variable [Algebra ℂ B]

theorem central_of_commutes_squares (u : B) (h : ∀ x : B, Commute u (x ^ 2)) :
    ∀ x : B, Commute u x := by
  intro x
  have hz : (2 : ℂ) • (u * x - x * u) = 0 := by
    calc
      (2 : ℂ) • (u * x - x * u) =
          (u * (1 + x) ^ 2 - (1 + x) ^ 2 * u) - (u * x ^ 2 - x ^ 2 * u) := by
        rw [two_smul]
        noncomm_ring
      _ = 0 := by rw [(h (1 + x)).eq, (h x).eq, sub_self, sub_self, sub_self]
  change u * x = x * u
  exact sub_eq_zero.mp ((smul_eq_zero.mp hz).resolve_left (two_ne_zero : (2 : ℂ) ≠ 0))

end SpectralIsometry.SquareZeroPreserver

