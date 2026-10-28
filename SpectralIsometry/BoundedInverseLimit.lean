module

public import SpectralIsometry.StrongStarApproximation
public import Mathlib.Analysis.Normed.Operator.Banach
public import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

/-!
# Bounded Inverse Limit

Supporting results for spectral isometries of complex unital C*-algebras.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open Filter Topology
open scoped NNReal

namespace SpectralIsometry.BoundedInverseLimit

open StrongStarApproximation
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem isUnit_of_two_vector_bounds (b : H →L[ℂ] H) (L : ℝ≥0)
    (hb : ∀ ξ : H, ‖ξ‖≤L*‖b ξ‖)
    (hbs : ∀ ξ : H, ‖ξ‖≤L*‖b.adjoint ξ‖) : IsUnit b := by
  have hanti : AntilipschitzWith L b := b.antilipschitz_of_bound hb
  have hantiStar : AntilipschitzWith L b.adjoint := b.adjoint.antilipschitz_of_bound hbs
  have hker : b.adjoint.ker=⊥ := LinearMap.ker_eq_bot.mpr hantiStar.injective
  have hdense : b.range.topologicalClosure=⊤ := by
    have hh := b.adjoint.orthogonal_ker
    rw [ContinuousLinearMap.adjoint_adjoint] at hh
    rw [←hh,hker]
    apply top_unique
    intro ξ _
    intro η hη
    have hη0 : η=0 := by simpa using hη
    subst η
    simp
  exact ContinuousLinearMap.isUnit_iff_bijective.mpr
    (b.bijective_iff_dense_range_and_antilipschitz.mpr ⟨hdense,L,hanti⟩)

private theorem norm_le_of_left_inverse (c d : H →L[ℂ] H) (hd : d*c=1) (ξ : H) :
    ‖ξ‖≤‖d‖*‖c ξ‖ := by
  have hξ : d (c ξ)=ξ := congrArg (fun T : H →L[ℂ] H => T ξ) hd
  calc ‖ξ‖ = ‖d (c ξ)‖ := congrArg norm hξ.symm
       _ ≤ ‖d‖*‖c ξ‖ := d.le_opNorm _

/-- Uniform two-sided inverse bounds survive a strong-star limit. The filter
must be nonbottom to pass inequalities to its limit; arbitrary index sets,
the zero Hilbert space, and L=0 are included. -/
theorem isUnit_of_strongStar_of_inverse_norm_bound {ι : Type*} {l : Filter ι} [l.NeBot]
    (a d : ι → (H →L[ℂ] H)) (b : H →L[ℂ] H) (L : ℝ≥0)
    (ha : StrongStarTendsto a l b)
    (hdL : ∀ i, d i*a i=1) (hdR : ∀ i, a i*d i=1)
    (hdN : ∀ i, ‖d i‖≤L) : IsUnit b := by
  have hleft (i : ι) (ξ : H) : ‖ξ‖≤L*‖a i ξ‖ :=
    (norm_le_of_left_inverse _ _ (hdL i) ξ).trans
      (mul_le_mul_of_nonneg_right (hdN i) (norm_nonneg _))
  have hright (i : ι) (ξ : H) : ‖ξ‖≤L*‖(a i).adjoint ξ‖ := by
    have hh : star (d i)*star (a i)=1 := by
      simpa only [star_mul,star_one] using congrArg star (hdR i)
    have hb := norm_le_of_left_inverse (star (a i)) (star (d i)) hh ξ
    rw [norm_star,ContinuousLinearMap.star_eq_adjoint] at hb
    exact hb.trans (mul_le_mul_of_nonneg_right (hdN i) (norm_nonneg _))
  apply isUnit_of_two_vector_bounds b L
  · intro ξ
    exact le_of_tendsto_of_tendsto tendsto_const_nhds ((ha.1 ξ).norm.const_mul (L:ℝ))
      (Eventually.of_forall fun i => hleft i ξ)
  · intro ξ
    have ht : Tendsto (fun i => (a i).adjoint ξ) l (𝓝 (b.adjoint ξ)) := by
      simpa only [ContinuousLinearMap.star_eq_adjoint] using ha.2 ξ
    exact le_of_tendsto_of_tendsto tendsto_const_nhds (ht.norm.const_mul (L:ℝ))
      (Eventually.of_forall fun i => hright i ξ)

end SpectralIsometry.BoundedInverseLimit

