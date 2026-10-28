module

public import SpectralIsometry.StrongStarApproximation
public import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
public import Mathlib.Analysis.CStarAlgebra.Projection
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Linarith

/-!
# Nilpotent Supports

Supporting results for spectral isometries of complex unital C*-algebras.
-/

 

@[expose] public section
noncomputable section

open Filter Topology Set
open scoped CStarAlgebra

namespace SpectralIsometry.StrongStarApproximation

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/- Exact proof reuse: OAI.Kadison.projection_commutes_of_invariant in
vendor/OAI/Analysis/Commutator/BicommutantOrbit.lean. -/
private theorem projection_commutes_of_invariant (P : Submodule ℂ H)
    [P.HasOrthogonalProjection] (a : Op (H := H))
    (ha : ∀ x ∈ P, a x ∈ P) (hstar : ∀ x ∈ P, (star a) x ∈ P) :
    P.starProjection * a = a * P.starProjection := by
  ext x
  change P.starProjection (a x) = a (P.starProjection x)
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · exact ha _ (P.starProjection_apply_mem x)
  · intro w hw
    rw [← map_sub, ← ContinuousLinearMap.adjoint_inner_right]
    exact Submodule.starProjection_inner_eq_zero x _ (hstar w hw)

private theorem star_mem_commutant (S : StarSubalgebra ℂ (Op (H := H)))
    (r : Op (H := H)) (hr : r ∈ Set.centralizer (S : Set (Op (H := H)))) :
    star r ∈ Set.centralizer (S : Set (Op (H := H))) := by
  intro a ha
  have he := congrArg star (hr (star a) (star_mem ha))
  simpa only [star_mul, star_star] using he.symm

private theorem kernel_invariant (n r : Op (H := H)) (hcomm : r * n = n * r) :
    ∀ x ∈ n.ker, r x ∈ n.ker := by
  intro x hx
  change n (r x) = 0
  have hx0 : n x = 0 := hx
  have he := congrArg (fun T : Op (H := H) => T x) hcomm
  simpa only [mul_apply_eq_comp, hx0, map_zero] using he.symm

private theorem rangeClosure_invariant (n r : Op (H := H)) (hcomm : r * n = n * r) :
    ∀ x ∈ n.range.topologicalClosure, r x ∈ n.range.topologicalClosure := by
  intro x hx
  apply closure_minimal (t := {y : H | r y ∈ n.range.topologicalClosure}) ?_ ?_ hx
  · rintro y ⟨z, rfl⟩
    change r (n z) ∈ n.range.topologicalClosure
    have he : r (n z) = n (r z) := by
      simpa only [mul_apply_eq_comp] using congrArg (fun T : Op (H := H) => T z) hcomm
    rw [he]
    exact n.range.le_topologicalClosure ⟨r z, rfl⟩
  · exact n.range.isClosed_topologicalClosure.preimage r.continuous

/-- The literal orthogonality product from the manuscript's approximation proof. -/
theorem squareZero_support_product (n : Op (H := H)) (h2 : n ^ 2 = 0) :
    (star n * n) * (n * star n) = 0 := by
  have hnn : n * n = 0 := by simpa only [pow_two] using h2
  calc
    (star n * n) * (n * star n) = star n * (n * n) * star n := by noncomm_ring
    _ = 0 := by rw [hnn, mul_zero, zero_mul]

/-- The two orthogonal support projections and the exact positive/negative cuts
of their difference. Arbitrary complete Hilbert spaces, including zero, apply. -/
theorem nilpotent_support_projections (S : StarSubalgebra ℂ (Op (H := H)))
    (n : Op (H := H))
    (hn : n ∈ Set.centralizer (Set.centralizer (S : Set (Op (H := H)))))
    (h2 : n ^ 2 = 0) :
    ∃ e f : Op (H := H), IsStarProjection e ∧ IsStarProjection f ∧
      e ∈ Set.centralizer (Set.centralizer (S : Set (Op (H := H)))) ∧
      f ∈ Set.centralizer (Set.centralizer (S : Set (Op (H := H)))) ∧
      e * f = 0 ∧ f * e = 0 ∧ e * n * f = n ∧
      IsSelfAdjoint (e - f) ∧ ‖e - f‖ ≤ 1 ∧
      (e - f)⁺ = e ∧ (e - f)⁻ = f := by
  let E : Submodule ℂ H := n.range.topologicalClosure
  let K : Submodule ℂ H := n.ker
  letI : IsClosed (E : Set H) := n.range.isClosed_topologicalClosure
  letI : IsClosed (K : Set H) := n.isClosed_ker
  let e : Op (H := H) := E.starProjection
  let p : Op (H := H) := K.starProjection
  let f : Op (H := H) := 1 - p
  have heP : IsStarProjection e := isStarProjection_starProjection (U := E)
  have hpP : IsStarProjection p := isStarProjection_starProjection (U := K)
  have hfP : IsStarProjection f := hpP.one_sub
  have heM : e ∈ Set.centralizer (Set.centralizer (S : Set (Op (H := H)))) := by
    intro r hr
    exact (projection_commutes_of_invariant E r
      (rangeClosure_invariant n r (hn r hr))
      (rangeClosure_invariant n (star r) (hn (star r) (star_mem_commutant S r hr)))).symm
  have hpM : p ∈ Set.centralizer (Set.centralizer (S : Set (Op (H := H)))) := by
    intro r hr
    exact (projection_commutes_of_invariant K r
      (kernel_invariant n r (hn r hr))
      (kernel_invariant n (star r) (hn (star r) (star_mem_commutant S r hr)))).symm
  have hfM : f ∈ Set.centralizer (Set.centralizer (S : Set (Op (H := H)))) := by
    intro r hr
    dsimp only [f]
    rw [mul_sub, sub_mul, mul_one, one_mul, hpM r hr]
  have hnn : n * n = 0 := by simpa only [pow_two] using h2
  have hRange : n.range ≤ K := by
    rintro y ⟨x, rfl⟩
    change n (n x) = 0
    simpa only [mul_apply_eq_comp, ContinuousLinearMap.zero_apply] using
      congrArg (fun T : Op (H := H) => T x) hnn
  have hEK : E ≤ K := n.range.topologicalClosure_minimal hRange n.isClosed_ker
  have hpe : p * e = e := by
    ext x
    change K.starProjection (E.starProjection x) = E.starProjection x
    exact Submodule.starProjection_eq_self_iff.mpr (hEK (E.starProjection_apply_mem x))
  have hep : e * p = e := by
    have he := congrArg star hpe
    simpa only [star_mul, heP.isSelfAdjoint.star_eq, hpP.isSelfAdjoint.star_eq] using he
  have hef : e * f = 0 := by
    change e * (1 - p) = 0
    rw [mul_sub, mul_one, hep, sub_self]
  have hfe : f * e = 0 := by
    change (1 - p) * e = 0
    rw [sub_mul, one_mul, hpe, sub_self]
  have hen : e * n = n := by
    ext x
    change E.starProjection (n x) = n x
    exact Submodule.starProjection_eq_self_iff.mpr
      (n.range.le_topologicalClosure ⟨x, rfl⟩)
  have hnp : n * p = 0 := by
    ext x
    change n (K.starProjection x) = 0
    exact K.starProjection_apply_mem x
  have hnf : n * f = n := by
    change n * (1 - p) = n
    rw [mul_sub, mul_one, hnp, sub_zero]
  have henf : e * n * f = n := by rw [hen, hnf]
  have hsa : IsSelfAdjoint (e - f) := heP.isSelfAdjoint.sub hfP.isSelfAdjoint
  have hsum : IsStarProjection (e + f) := heP.add hfP hef
  have hsquare : (e - f) * (e - f) = e + f := by
    noncomm_ring [heP.isIdempotentElem.eq, hfP.isIdempotentElem.eq, hef, hfe]
  have heq : ‖e - f‖ * ‖e - f‖ = ‖e + f‖ := by
    rw [← CStarRing.norm_star_mul_self, hsa.star_eq, hsquare]
  have hnorm : ‖e - f‖ ≤ 1 := by
    have hsumNorm := IsStarProjection.norm_le (e + f) hsum
    nlinarith [norm_nonneg (e - f)]
  have hparts : (e - f)⁺ = e ∧ (e - f)⁻ = f := by
    letI := CStarAlgebra.spectralOrder (Op (H := H))
    letI := CStarAlgebra.spectralOrderedRing (Op (H := H))
    exact CFC.posPart_negPart_unique rfl hef heP.nonneg hfP.nonneg
  exact ⟨e, f, heP, hfP, heM, hfM, hef, hfe, henf, hsa, hnorm, hparts.1, hparts.2⟩

end SpectralIsometry.StrongStarApproximation

