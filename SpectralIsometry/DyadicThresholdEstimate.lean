module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Module
import Mathlib.Tactic.NormNum

/-!
# Dyadic Threshold Estimate

Supporting results for spectral isometries of complex unital C*-algebras.
-/

@[expose] public section
noncomputable section

open scoped ComplexOrder CStarAlgebra

namespace SpectralIsometry.SquareZeroPreserver

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem dyadic_projection_square_error_le {a q : A} (hq : IsStarProjection q)
    (haq : Commute a q) (hc0 : 0 ≤ 2 * a - q) (hc1 : 2 * a - q ≤ 1) :
    (q - a) ^ 2 ≤ 4 * (a - a ^ 2) ^ 2 := by
  let c : A := 2 * a - q
  let b : A := 1 - c
  let f : A := b + (1 - q) + (1 - q)
  let g : A := c + q + q
  have hcq : Commute c q := by
    change (2 * a - q) * q = q * (2 * a - q)
    noncomm_ring [haq.eq]
  have hcb : Commute c b := by
    change c * (1 - c) = (1 - c) * c
    noncomm_ring
  have hcf : Commute c f := by
    change c * ((1 - c) + (1 - q) + (1 - q)) =
      ((1 - c) + (1 - q) + (1 - q)) * c
    noncomm_ring [hcq.eq]
  have hbf : Commute b f := by
    change (1 - c) * ((1 - c) + (1 - q) + (1 - q)) =
      ((1 - c) + (1 - q) + (1 - q)) * (1 - c)
    noncomm_ring [hcq.eq]
  have hcg : Commute c g := by
    change c * (c + q + q) = (c + q + q) * c
    noncomm_ring [hcq.eq]
  have hbg : Commute b g := by
    change (1 - c) * (c + q + q) = (c + q + q) * (1 - c)
    noncomm_ring [hcq.eq]
  have hfg : Commute f g := by
    change ((1 - c) + (1 - q) + (1 - q)) * (c + q + q) =
      (c + q + q) * ((1 - c) + (1 - q) + (1 - q))
    noncomm_ring [hcq.eq]
  have hb0 : 0 ≤ b := sub_nonneg.mpr hc1
  have hq0 : 0 ≤ 1 - q := sub_nonneg.mpr hq.le_one
  have hf0 : 0 ≤ f := add_nonneg (add_nonneg hb0 hq0) hq0
  have hg0 : 0 ≤ g := add_nonneg (add_nonneg hc0 hq.nonneg) hq.nonneg
  have hprod : 0 ≤ c * b * f * g :=
    ((hcg.mul_left hbg).mul_left hfg).mul_nonneg
      ((hcf.mul_left hbf).mul_nonneg (hcb.mul_nonneg hc0 hb0) hf0) hg0
  have hqq (x : A) : q * (q * x) = q * x := by
    rw [←mul_assoc,hq.isIdempotentElem.eq]
  have hfour (x : A) : (4 : ℝ) • x = x + x + x + x := by module
  have hcertificate : (4 : ℝ) • (4 * (a - a ^ 2) ^ 2 - (q - a) ^ 2) =
      c * b * f * g := by
    rw [hfour]
    dsimp only [c,b,f,g]
    noncomm_ring [hq.isIdempotentElem.eq,haq.eq,haq.left_comm,hqq]
  have hscaled : 0 ≤ (4 : ℝ) • (4 * (a - a ^ 2) ^ 2 - (q - a) ^ 2) := by
    rw [hcertificate]
    exact hprod
  have hpos := smul_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 4) hscaled
  rw [smul_smul,show (1 / 4 : ℝ) * 4 = 1 by norm_num,one_smul] at hpos
  exact sub_nonneg.mp hpos

end SpectralIsometry.SquareZeroPreserver

