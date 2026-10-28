module

public import Mathlib.Algebra.Star.Basic
public import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic.NoncommRing

/-!
# Square Zero Copies

Supporting results for spectral isometries of complex unital C*-algebras.
-/

 

@[expose] public section

namespace SpectralIsometry.SquareZeroPreserver

variable {A : Type*} [Ring A] [StarRing A]

def HasOrthogonalCopies (p : A) : Prop :=
  ∃ r s : A, p * r = r ∧ r * p = r ∧ p * s = s ∧ s * p = s ∧
    star r * r = p ∧ star s * s = p ∧ star r * s = 0

theorem hasOrthogonalCopies_zero : HasOrthogonalCopies (0 : A) := by
  exact ⟨0, 0, by simp, by simp, by simp, by simp, by simp, by simp, by simp⟩

theorem hasOrthogonalCopies_of_contained_copy {p q v : A}
    (hp : HasOrthogonalCopies p) (hq : q * q = q) (hqs : star q = q)
    (hpq : p * q = q) (hqp : q * p = q)
    (hv : star v * v = p) (hqv : q * v = v) : HasOrthogonalCopies q := by
  obtain ⟨r, s, hpr, hrp, hps, hsp, hr, hs, hrs⟩ := hp
  have hrstar : star r * p = star r := by
    have hpstar : star p = p := by
      calc star p = star (star r * r) := congrArg star hr.symm
           _ = star r * r := by simp only [star_mul, star_star]
           _ = p := hr
    simpa only [star_mul, hpstar] using congrArg star hpr
  have hsstar : star s * p = star s := by
    have hpstar : star p = p := by
      calc star p = star (star s * s) := congrArg star hs.symm
           _ = star s * s := by simp only [star_mul, star_star]
           _ = p := hs
    simpa only [star_mul, hpstar] using congrArg star hps
  refine ⟨v * r * q, v * s * q, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← mul_assoc, ← mul_assoc, hqv]
  · rw [mul_assoc, hq]
  · rw [← mul_assoc, ← mul_assoc, hqv]
  · rw [mul_assoc, hq]
  · calc
      star (v * r * q) * (v * r * q) = q * (star r * (star v * v) * r) * q := by
        simp only [star_mul, hqs]
        noncomm_ring
      _ = q := by rw [hv, hrstar, hr, hqp, hq]
  · calc
      star (v * s * q) * (v * s * q) = q * (star s * (star v * v) * s) * q := by
        simp only [star_mul, hqs]
        noncomm_ring
      _ = q := by rw [hv, hsstar, hs, hqp, hq]
  · calc
      star (v * r * q) * (v * s * q) = q * (star r * (star v * v) * s) * q := by
        simp only [star_mul, hqs]
        noncomm_ring
      _ = 0 := by rw [hv, hrstar, hrs]; simp

theorem hasOrthogonalCopies_central_cut {p z : A} (hp : HasOrthogonalCopies p)
    (hz : z * z = z) (hzs : star z = z) (hcentral : ∀ a : A, z * a = a * z) :
    HasOrthogonalCopies (z * p) := by
  obtain ⟨r, s, hpr, hrp, hps, hsp, hr, hs, hrs⟩ := hp
  have hzr : z * r * z = z * r := by rw [hcentral r, mul_assoc, hz, ← hcentral r]
  have hzs' : z * s * z = z * s := by rw [hcentral s, mul_assoc, hz, ← hcentral s]
  refine ⟨z * r, z * s, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · calc
      (z * p) * (z * r) = z * (p * z) * r := by noncomm_ring
      _ = z * (z * p) * r := by rw [← hcentral p]
      _ = (z * z) * (p * r) := by noncomm_ring
      _ = z * r := by rw [hz, hpr]
  · calc
      (z * r) * (z * p) = (z * r * z) * p := by noncomm_ring
      _ = z * r := by rw [hzr, mul_assoc, hrp]
  · calc
      (z * p) * (z * s) = z * (p * z) * s := by noncomm_ring
      _ = z * (z * p) * s := by rw [← hcentral p]
      _ = (z * z) * (p * s) := by noncomm_ring
      _ = z * s := by rw [hz, hps]
  · calc
      (z * s) * (z * p) = (z * s * z) * p := by noncomm_ring
      _ = z * s := by rw [hzs', mul_assoc, hsp]
  · calc
      star (z * r) * (z * r) = star r * (z * z) * r := by rw [star_mul, hzs]; noncomm_ring
      _ = z * p := by rw [hz, ← hcentral (star r), mul_assoc, hr]
  · calc
      star (z * s) * (z * s) = star s * (z * z) * s := by rw [star_mul, hzs]; noncomm_ring
      _ = z * p := by rw [hz, ← hcentral (star s), mul_assoc, hs]
  · calc
      star (z * r) * (z * s) = star r * (z * z) * s := by rw [star_mul, hzs]; noncomm_ring
      _ = 0 := by rw [hz, ← hcentral (star r), mul_assoc, hrs, mul_zero]

theorem hasOrthogonalCopies_split {p : A} (hps : star p = p) (hpp : p * p = p)
    (hp : HasOrthogonalCopies p) :
    ∃ f : A, star f = f ∧ f * f = f ∧ p * f = f ∧ f * p = f ∧
      HasOrthogonalCopies f ∧ HasOrthogonalCopies (p - f) := by
  obtain ⟨r, s, hpr, hrp, hps', hsp, hr, hs, hrs⟩ := hp
  let f := r * star r
  have hfs : star f = f := by dsimp [f]; simp only [star_mul, star_star]
  have hpf : p * f = f := by dsimp [f]; rw [← mul_assoc, hpr]
  have hfp : f * p = f := by
    have h := congrArg star hpr
    simp only [star_mul, hps] at h
    dsimp [f]
    rw [mul_assoc, h]
  have hff : f * f = f := by
    change (r * star r) * (r * star r) = r * star r
    calc
      (r * star r) * (r * star r) = r * (star r * r) * star r := by noncomm_ring
      _ = r * star r := by rw [hr, hrp]
  have hfr : f * r = r := by dsimp [f]; rw [mul_assoc, hr, hrp]
  have hcopiesf : HasOrthogonalCopies f :=
    hasOrthogonalCopies_of_contained_copy ⟨r,s,hpr,hrp,hps',hsp,hr,hs,hrs⟩
      hff hfs hpf hfp hr hfr
  have hqq : (p - f) * (p - f) = p - f := by
    rw [sub_mul, mul_sub, mul_sub, hpp, hpf, hfp, hff]
    noncomm_ring
  have hqs : star (p - f) = p - f := by rw [star_sub, hps, hfs]
  have hpq : p * (p - f) = p - f := by rw [mul_sub, hpp, hpf]
  have hqp : (p - f) * p = p - f := by rw [sub_mul, hpp, hfp]
  have hqs' : (p - f) * s = s := by
    change (p - r * star r) * s = s
    rw [sub_mul, hps', mul_assoc, hrs, mul_zero, sub_zero]
  exact ⟨f,hfs,hff,hpf,hfp,hcopiesf,
    hasOrthogonalCopies_of_contained_copy ⟨r,s,hpr,hrp,hps',hsp,hr,hs,hrs⟩
      hqq hqs hpq hqp hs hqs'⟩

end SpectralIsometry.SquareZeroPreserver

