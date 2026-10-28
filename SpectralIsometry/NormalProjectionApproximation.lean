module

public import SpectralIsometry.UnitCopyTails
public import SpectralIsometry.ProjectionTailStrong
public import SpectralIsometry.CornerCommutingDyadic
public import SpectralIsometry.DyadicProjectionStrong
public import SpectralIsometry.ProperInfiniteCopiesBridge
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Positivity

/-!
# Normal Projection Approximation

Supporting results for spectral isometries of complex unital C*-algebras.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

open Filter Topology
open scoped ComplexOrder CStarAlgebra
open OAI.HochschildCorners OAI.HochschildComparison
open OAI.BoundedHochschild.KadisonRingrose
open SpectralIsometry.BidualFoundation.CoefficientPredual
open SpectralIsometry.StrongStarApproximation

namespace SpectralIsometry.SquareZeroPreserver

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local instance approximationComplexNormedSpaceSelf : NormedSpace ℂ ℂ := NormedField.toNormedSpace
local instance approximationCoefficientNormedGroup (M : VonNeumannAlgebra H) :
    NormedAddCommGroup (coefficientPredual M) :=
  SpectralIsometry.BidualFoundation.CoefficientPredual.coefficientNormedGroup M
local instance approximationCoefficientNormedSpace (M : VonNeumannAlgebra H) :
    NormedSpace ℂ (coefficientPredual M) :=
  SpectralIsometry.BidualFoundation.CoefficientPredual.coefficientNormedSpace M

theorem exists_properlyInfinite_complement_projection_approximation
    (M : VonNeumannAlgebra H) (v w : M)
    (hv : star v * v = 1) (hw : star w * w = 1) (hvw : star v * w = 0)
    (p : M) (hp : IsStarProjection p) :
    ∃ t : ℕ → M,
      (∀ n, IsStarProjection (t n) ∧ ProperlyInfiniteProjection (t n) ∧
        ProperlyInfiniteProjection (1 - t n)) ∧
      StrongStarTendsto (fun n => (t n : H →L[ℂ] H)) atTop (p : H →L[ℂ] H) := by
  classical
  let e := concretePredualIsometry M
  obtain ⟨c,r,hci,horth,hr,hrlim⟩ := exists_orthogonal_unitCopy_tails e v w hv hw hvw
  let s (n : ℕ) : M := 1 - r n
  have hs (n : ℕ) : IsStarProjection (s n) := (hr n).1.one_sub
  let a (n : ℕ) : M := s n * p * s n
  have hamem (n : ℕ) : a n ∈ corner (s n) (hs n) := compress_mem_corner (hs n) p
  have ha0 (n : ℕ) : 0 ≤ a n := by
    simpa only [(hs n).isSelfAdjoint.star_eq] using star_left_conjugate_nonneg hp.nonneg (s n)
  have has (n : ℕ) : a n ≤ s n := by
    have hh := star_left_conjugate_nonneg hp.one_sub.nonneg (s n)
    rw [(hs n).isSelfAdjoint.star_eq] at hh
    have he : s n * (1-p) * s n = s n - a n := by
      calc
        s n * (1-p) * s n = s n * s n - s n * p * s n := by noncomm_ring
        _ = s n - a n := by rw [(hs n).isIdempotentElem.eq]
    rw [he] at hh
    exact sub_nonneg.mp hh
  have ha1 (n : ℕ) : a n ≤ 1 := (has n).trans (hs n).le_one
  have hqex (n : ℕ) : ∃ q : M, IsStarProjection q ∧ q ≤ s n ∧ Commute (a n) q ∧
      0 ≤ (2 : ℝ) • a n - q ∧ (2 : ℝ) • a n - q ≤ s n :=
    exists_commuting_corner_dyadic_projection e (hs n) (hamem n) (ha0 n) (has n)
  choose q hq hqs haq hc0 hc1 using hqex
  have hrop (n : ℕ) : IsStarProjection (r n : H →L[ℂ] H) :=
    ⟨congrArg Subtype.val (hr n).1.isIdempotentElem.eq,
      congrArg Subtype.val (hr n).1.isSelfAdjoint.star_eq⟩
  have hsop (n : ℕ) : IsStarProjection (s n : H →L[ℂ] H) :=
    ⟨congrArg Subtype.val (hs n).isIdempotentElem.eq,
      congrArg Subtype.val (hs n).isSelfAdjoint.star_eq⟩
  have hpop : IsStarProjection (p : H →L[ℂ] H) :=
    ⟨congrArg Subtype.val hp.isIdempotentElem.eq,congrArg Subtype.val hp.isSelfAdjoint.star_eq⟩
  have hrstrong := strongStarTendsto_zero_of_projection_predual M r (fun n => (hr n).1) hrlim
  have hsstrong : StrongStarTendsto (fun n => (s n : H →L[ℂ] H)) atTop 1 := by
    constructor <;> intro ξ
    · change Tendsto (fun n => ξ - (r n : H →L[ℂ] H) ξ) atTop (𝓝 ξ)
      simpa only [ContinuousLinearMap.zero_apply,sub_zero] using
        (tendsto_const_nhds (x := ξ)).sub (hrstrong.1 ξ)
    · have hstar : (fun n => star (s n : H →L[ℂ] H)) = (fun n => (s n : H →L[ℂ] H)) :=
        funext fun n => (hsop n).isSelfAdjoint.star_eq
      rw [hstar,star_one]
      change Tendsto (fun n => ξ - (r n : H →L[ℂ] H) ξ) atTop (𝓝 ξ)
      simpa only [ContinuousLinearMap.zero_apply,sub_zero] using
        (tendsto_const_nhds (x := ξ)).sub (hrstrong.1 ξ)
  have hpconst := strongStarTendsto_const (H := H) (atTop : Filter ℕ) (p : H →L[ℂ] H)
  have hanlim : StrongStarTendsto (fun n => (a n : H →L[ℂ] H)) atTop (p : H →L[ℂ] H) := by
    have hleft := strongStarTendsto_mul_of_norm_bounds hsstrong hpconst
      (Eventually.of_forall fun n => (hsop n).norm_le _) (Eventually.of_forall fun _ => hpop.norm_le _)
    have hleftnorm : ∀ n, ‖(s n : H →L[ℂ] H) * (p : H →L[ℂ] H)‖ ≤ 1 := by
      intro n
      exact (norm_mul_le _ _).trans
        (mul_le_one₀ ((hsop n).norm_le _) (norm_nonneg _) (hpop.norm_le _))
    have hh := strongStarTendsto_mul_of_norm_bounds hleft hsstrong
      (Eventually.of_forall hleftnorm) (Eventually.of_forall fun n => (hsop n).norm_le _)
    change StrongStarTendsto
      (fun n => (s n : H →L[ℂ] H) * (p : H →L[ℂ] H) * (s n : H →L[ℂ] H))
      atTop (p : H →L[ℂ] H)
    simpa only [one_mul,mul_one] using hh
  have hqop (n : ℕ) : IsStarProjection (q n : H →L[ℂ] H) :=
    ⟨congrArg Subtype.val (hq n).isIdempotentElem.eq,
      congrArg Subtype.val (hq n).isSelfAdjoint.star_eq⟩
  have hqlim : StrongStarTendsto (fun n => (q n : H →L[ℂ] H)) atTop (p : H →L[ℂ] H) := by
    apply strongStarTendsto_dyadic_projections _ _ _ ha0 ha1 hqop hpop ?_ ?_ ?_ hanlim
    · intro n; exact congrArg Subtype.val (haq n).eq
    · intro n
      have hh : (0 : M) ≤ a n + a n - q n := by simpa only [two_smul] using hc0 n
      change (0 : H →L[ℂ] H) ≤ (a n : H →L[ℂ] H) + (a n : H →L[ℂ] H) - (q n : H →L[ℂ] H) at hh
      simpa only [two_mul] using hh
    · intro n
      have hh : a n + a n - q n ≤ (1 : M) := by
        simpa only [two_smul] using (hc1 n).trans (hs n).le_one
      change (a n : H →L[ℂ] H) + (a n : H →L[ℂ] H) - (q n : H →L[ℂ] H) ≤ 1 at hh
      simpa only [two_mul] using hh
  let t (n : ℕ) : M := q n + (c n).final
  have hcopies : HasOrthogonalCopies (1 : M) :=
    ⟨v,w,one_mul v,mul_one v,one_mul w,mul_one w,hv,hw,hvw⟩
  have ht (n : ℕ) : IsStarProjection (t n) ∧ ProperlyInfiniteProjection (t n) ∧
      ProperlyInfiniteProjection (1 - t n) := by
    have hsr0 : s n * r n = 0 := by
      dsimp only [s]
      rw [sub_mul,one_mul,(hr n).1.isIdempotentElem.eq,sub_self]
    have hqcf (i : ℕ) (hi : (c i).final ≤ r n) : q n * (c i).final = 0 :=
      projection_mul_zero_of_bounds (hs n) (hr n).1 (hq n) (c i).final_proj
        hsr0 (hqs n) hi
    have htn : IsStarProjection (t n) := (hq n).add (c n).final_proj (hqcf n (hr n).2.1)
    have hfl : (c n).final ≤ t n := le_add_of_nonneg_left (hq n).nonneg
    have htcopy : HasOrthogonalCopies (t n) := hasOrthogonalCopies_of_contained_copy hcopies
      htn.isIdempotentElem.eq htn.isSelfAdjoint.star_eq (one_mul _) (mul_one _)
      (hci n) (partialIso_left_support htn (c n) hfl)
    have htg : t n * (c (n+1)).final = 0 := by
      rw [show t n = q n + (c n).final from rfl,add_mul,hqcf (n+1) (hr n).2.2,
        horth n (n+1) (Nat.lt_succ_self n).ne,zero_add]
    have hgt : (c (n+1)).final * t n = 0 := by
      simpa only [star_mul,(c (n+1)).final_proj.isSelfAdjoint.star_eq,
        htn.isSelfAdjoint.star_eq,star_zero] using congrArg star htg
    have hgl : (c (n+1)).final ≤ 1 - t n :=
      projection_le_complement_of_mul_zero (c (n+1)).final_proj htn hgt
    have hcompcopy : HasOrthogonalCopies (1 - t n) := hasOrthogonalCopies_of_contained_copy hcopies
      htn.one_sub.isIdempotentElem.eq htn.one_sub.isSelfAdjoint.star_eq (one_mul _) (mul_one _)
      (hci (n+1)) (partialIso_left_support htn.one_sub (c (n+1)) hgl)
    exact ⟨htn,properlyInfinite_of_hasOrthogonalCopies htn htcopy,
      properlyInfinite_of_hasOrthogonalCopies htn.one_sub hcompcopy⟩
  have hflim : StrongStarTendsto (fun n => ((c n).final : H →L[ℂ] H)) atTop 0 := by
    apply strongStarTendsto_zero_of_projection_diagonal _
      (fun n => ⟨congrArg Subtype.val (c n).final_proj.isIdempotentElem.eq,
        congrArg Subtype.val (c n).final_proj.isSelfAdjoint.star_eq⟩)
    intro ξ
    -- The ordered projection bound controls the positive vector coefficients.
    have hcoeff (n : ℕ) : 0 ≤ (inner ℂ ξ (((c n).final : H →L[ℂ] H) ξ)).re ∧
        (inner ℂ ξ (((c n).final : H →L[ℂ] H) ξ)).re ≤
          (inner ℂ ξ ((r n : H →L[ℂ] H) ξ)).re := by
      constructor
      · exact (ContinuousLinearMap.nonneg_iff_isPositive.mp (c n).final_proj.nonneg).re_inner_nonneg_right ξ
      · have hle : ((c n).final : H →L[ℂ] H) ≤ (r n : H →L[ℂ] H) := (hr n).2.1
        have hh := (ContinuousLinearMap.nonneg_iff_isPositive.mp
          (sub_nonneg.mpr hle)).re_inner_nonneg_right ξ
        change 0 ≤ (inner ℂ ξ (((r n : H →L[ℂ] H) - ((c n).final : H →L[ℂ] H)) ξ)).re at hh
        rw [ContinuousLinearMap.sub_apply,inner_sub_right,Complex.sub_re] at hh
        exact sub_nonneg.mp hh
    have hreal : Tendsto (fun n => (inner ℂ ξ (((c n).final : H →L[ℂ] H) ξ)).re) atTop (𝓝 0) :=
      squeeze_zero (fun n => (hcoeff n).1) (fun n => (hcoeff n).2)
        (by
          have hh := Complex.continuous_re.continuousAt.tendsto.comp
            ((tendsto_const_nhds (x := ξ)).inner (hrstrong.1 ξ))
          change Tendsto (fun n : ℕ => (inner ℂ ξ ((r n : H →L[ℂ] H) ξ)).re)
            atTop (𝓝 (inner ℂ ξ ((0 : H →L[ℂ] H) ξ)).re) at hh
          simpa only [ContinuousLinearMap.zero_apply,inner_zero_right,Complex.zero_re] using hh)
    have him (n : ℕ) : (inner ℂ ξ (((c n).final : H →L[ℂ] H) ξ)).im = 0 :=
      ((ContinuousLinearMap.nonneg_iff_isPositive.mp (c n).final_proj.nonneg).inner_nonneg_right ξ).2.symm
    have hre (n : ℕ) : ((inner ℂ ξ (((c n).final : H →L[ℂ] H) ξ)).re : ℂ) =
        inner ℂ ξ (((c n).final : H →L[ℂ] H) ξ) := Complex.ext rfl (by simpa only [Complex.ofReal_im] using (him n).symm)
    have hh := Complex.continuous_ofReal.continuousAt.tendsto.comp hreal
    have hfn : (fun n : ℕ => ((inner ℂ ξ (((c n).final : H →L[ℂ] H) ξ)).re : ℂ)) =
        (fun n : ℕ => inner ℂ ξ (((c n).final : H →L[ℂ] H) ξ)) := funext hre
    change Tendsto (fun n : ℕ => ((inner ℂ ξ (((c n).final : H →L[ℂ] H) ξ)).re : ℂ))
      atTop (𝓝 (Complex.ofReal (0 : ℝ))) at hh
    rw [hfn,Complex.ofReal_zero] at hh
    exact hh
  refine ⟨t,ht,?_⟩
  constructor <;> intro ξ
  · change Tendsto (fun n => (q n : H →L[ℂ] H) ξ + ((c n).final : H →L[ℂ] H) ξ) atTop
      (𝓝 ((p : H →L[ℂ] H) ξ))
    simpa only [ContinuousLinearMap.zero_apply,add_zero] using
      (hqlim.1 ξ).add (hflim.1 ξ)
  · have he : (fun n => star (t n : H →L[ℂ] H) ξ) =
        (fun n => star (q n : H →L[ℂ] H) ξ + star ((c n).final : H →L[ℂ] H) ξ) := by
      funext n
      change star ((q n : H →L[ℂ] H) + ((c n).final : H →L[ℂ] H)) ξ = _
      rw [star_add,ContinuousLinearMap.add_apply]
    rw [he]
    simpa only [star_zero,ContinuousLinearMap.zero_apply,add_zero] using (hqlim.2 ξ).add (hflim.2 ξ)

end SpectralIsometry.SquareZeroPreserver

