module

public import SpectralIsometry.SquareZeroCopies
public import OAI.Analysis.BoundedHochschild.ProperlyInfiniteIsometries
import Mathlib.Tactic.NoncommRing

/-!
# Proper Infinite Copies Bridge

Supporting results for spectral isometries of complex unital C*-algebras.
-/

 

@[expose] public section
set_option autoImplicit false
noncomputable section

open scoped ComplexOrder CStarAlgebra
open OAI.HochschildCorners OAI.HochschildComparison
open OAI.BoundedHochschild.KadisonRingrose

namespace SpectralIsometry.SquareZeroPreserver

variable {M : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]

theorem properlyInfinite_of_hasOrthogonalCopies {p : M} (hp : IsStarProjection p)
    (h : HasOrthogonalCopies p) : ProperlyInfiniteProjection p := by
  obtain ⟨r,s,hpr,hrp,hps,hsp,hr,hs,hrs⟩ := h
  let V : PartialIso M := ⟨r,by rw [mul_assoc,hr,hrp]⟩
  let W : PartialIso M := ⟨s,by rw [mul_assoc,hs,hsp]⟩
  have hV : V.final ≤ p := by
    apply (V.final_proj.le_iff_mul_eq_right hp).mpr
    change p * (r * star r) = r * star r
    rw [←mul_assoc,hpr]
  have hW : W.final ≤ p := by
    apply (W.final_proj.le_iff_mul_eq_right hp).mpr
    change p * (s * star s) = s * star s
    rw [←mul_assoc,hps]
  refine ⟨V,W,hr,hs,hV,hW,?_⟩
  change (r * star r) * (s * star s) = 0
  calc
    (r * star r) * (s * star s) = r * (star r * s) * star s := by noncomm_ring
    _ = 0 := by rw [hrs]; simp

theorem exists_corner_isometries_of_properlyInfinite {p : M} (hp : IsStarProjection p)
    (hproper : ProperlyInfiniteProjection p) :
    ∃ r s : Corner p hp, star r * r = 1 ∧ star s * s = 1 ∧ star r * s = 0 := by
  obtain ⟨v,w,hvi,hwi,hvf,hwf,ho⟩ := hproper
  let r : Corner p hp := partialIsoInCorner hp v (by rw [hvi]) hvf
  let s : Corner p hp := partialIsoInCorner hp w (by rw [hwi]) hwf
  exact ⟨r,s,Subtype.ext hvi,Subtype.ext hwi,
    Subtype.ext (PartialIso.star_mul_eq_zero_of_final_orthogonal ho)⟩

end SpectralIsometry.SquareZeroPreserver

