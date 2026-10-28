module
public import SpectralIsometry.NilpotentSupports
public import OAI.Analysis.BoundedHochschild.NormalModulus
import Mathlib.Tactic.NoncommRing

/-!
# Nilpotent Support Identification

Supporting results for spectral isometries of complex unital C*-algebras.
-/

 

@[expose] public section
set_option autoImplicit false
noncomputable section
open Set

namespace SpectralIsometry.SupportIdentification
open OAI.BoundedHochschild

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
abbrev Op := H →L[ℂ] H

local instance canonicalOrder : PartialOrder (Op (H:=H)) :=
  CStarAlgebra.spectralOrder _
local instance canonicalStarOrder : StarOrderedRing (Op (H:=H)) :=
  CStarAlgebra.spectralOrderedRing _

def rangeSupport (n : Op (H:=H)) : Op (H:=H) := by
  letI : IsClosed (n.range.topologicalClosure : Set H) := n.range.isClosed_topologicalClosure
  exact n.range.topologicalClosure.starProjection

def kernelComplement (n : Op (H:=H)) : Op (H:=H) := by
  letI : IsClosed (n.ker : Set H) := n.isClosed_ker
  exact 1-n.ker.starProjection

theorem rangeSupport_projection (n : Op (H:=H)) : IsStarProjection (rangeSupport n) := by
  letI : IsClosed (n.range.topologicalClosure : Set H) := n.range.isClosed_topologicalClosure
  exact isStarProjection_starProjection (U:=n.range.topologicalClosure)

theorem rangeSupport_mul (n : Op (H:=H)) : rangeSupport n*n=n := by
  letI : IsClosed (n.range.topologicalClosure : Set H) := n.range.isClosed_topologicalClosure
  ext ξ
  change n.range.topologicalClosure.starProjection (n ξ)=n ξ
  exact Submodule.starProjection_eq_self_iff.mpr
    (n.range.le_topologicalClosure ⟨ξ,rfl⟩)

theorem rangeSupport_is_support (n : Op (H:=H)) :
    IsSupportProjection (n*star n) (rangeSupport n) := by
  letI : IsClosed (n.range.topologicalClosure : Set H) := n.range.isClosed_topologicalClosure
  have hp := rangeSupport_projection n
  have hl : rangeSupport n*(n*star n)=n*star n := by
    rw [←mul_assoc,rangeSupport_mul]
  have hr : (n*star n)*rangeSupport n=n*star n := by
    simpa only [star_mul,star_star,hp.isSelfAdjoint.star_eq] using congrArg star hl
  refine ⟨hp,hl,hr,?_⟩
  intro x hx
  have hnx : star n*x=0 := by
    apply (CStarRing.star_mul_self_eq_zero_iff _).mp
    calc
      star (star n*x)*(star n*x)=star x*((n*star n)*x) := by
        simp only [star_mul,star_star]
        noncomm_ring
      _=0 := by rw [hx,mul_zero]
  ext ξ
  change n.range.topologicalClosure.starProjection (x ξ)=0
  apply Submodule.eq_starProjection_of_mem_orthogonal
    (n.range.topologicalClosure.zero_mem)
  rw [sub_zero,Submodule.orthogonal_closure,ContinuousLinearMap.orthogonal_range]
  change (star n) (x ξ)=0
  exact congrArg (fun T : Op (H:=H) => T ξ) hnx

theorem kernelComplement_eq_rangeSupport_star (n : Op (H:=H)) :
    kernelComplement n=rangeSupport (star n) := by
  letI : IsClosed (n.ker : Set H) := n.isClosed_ker
  letI : IsClosed ((star n).range.topologicalClosure : Set H) :=
    (star n).range.isClosed_topologicalClosure
  change 1-n.ker.starProjection=(star n).range.topologicalClosure.starProjection
  rw [←Submodule.starProjection_orthogonal']
  congr 1
  exact n.orthogonal_ker

theorem kernelComplement_is_support (n : Op (H:=H)) :
    IsSupportProjection (star n*n) (kernelComplement n) := by
  rw [kernelComplement_eq_rangeSupport_star]
  simpa only [star_star] using rangeSupport_is_support (star n)

theorem mul_kernelComplement (n : Op (H:=H)) : n*kernelComplement n=n := by
  letI : IsClosed (n.ker : Set H) := n.isClosed_ker
  have hnp : n*n.ker.starProjection=0 := by
    ext ξ
    exact n.ker.starProjection_apply_mem ξ
  change n*(1-n.ker.starProjection)=n
  rw [mul_sub,mul_one,hnp,sub_zero]

theorem squareZero_supports_orthogonal (n : Op (H:=H)) (h2 : n^2=0) :
    rangeSupport n*kernelComplement n=0 ∧ kernelComplement n*rangeSupport n=0 := by
  let E := n.range.topologicalClosure
  let K := n.ker
  letI : IsClosed (E : Set H) := n.range.isClosed_topologicalClosure
  letI : IsClosed (K : Set H) := n.isClosed_ker
  have hrange : n.range≤K := by
    rintro _ ⟨ξ,rfl⟩
    change n (n ξ)=0
    simpa only [pow_two,mul_apply_eq_comp,
      ContinuousLinearMap.zero_apply] using congrArg (fun T : Op (H:=H) => T ξ) h2
  have hEK : E≤K := n.range.topologicalClosure_minimal hrange n.isClosed_ker
  have hpe : K.starProjection*E.starProjection=E.starProjection := by
    ext ξ
    exact Submodule.starProjection_eq_self_iff.mpr
      (hEK (E.starProjection_apply_mem ξ))
  have hep : E.starProjection*K.starProjection=E.starProjection := by
    simpa only [star_mul,
      (isStarProjection_starProjection (U:=E)).isSelfAdjoint.star_eq,
      (isStarProjection_starProjection (U:=K)).isSelfAdjoint.star_eq] using congrArg star hpe
  constructor
  · change E.starProjection*(1-K.starProjection)=0
    rw [mul_sub,mul_one,hep,sub_self]
  · change (1-K.starProjection)*E.starProjection=0
    rw [sub_mul,one_mul,hpe,sub_self]

private theorem projection_commutes (P : Submodule ℂ H) [P.HasOrthogonalProjection]
    (a : Op (H:=H)) (ha : ∀ x∈P, a x∈P) (hstar : ∀ x∈P, (star a) x∈P) :
    P.starProjection*a=a*P.starProjection := by
  ext x
  change P.starProjection (a x)=a (P.starProjection x)
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · exact ha _ (P.starProjection_apply_mem x)
  · intro w hw
    rw [←map_sub,←ContinuousLinearMap.adjoint_inner_right]
    exact Submodule.starProjection_inner_eq_zero x _ (hstar w hw)

private theorem rangeClosure_invariant (n r : Op (H:=H)) (hcomm : r*n=n*r) :
    ∀ x∈n.range.topologicalClosure, r x∈n.range.topologicalClosure := by
  intro x hx
  apply closure_minimal (t:={y : H | r y∈n.range.topologicalClosure}) ?_ ?_ hx
  · rintro _ ⟨ξ,rfl⟩
    change r (n ξ)∈n.range.topologicalClosure
    have he : r (n ξ)=n (r ξ) := by
      simpa only [mul_apply_eq_comp] using
        congrArg (fun T : Op (H:=H) => T ξ) hcomm
    rw [he]
    exact n.range.le_topologicalClosure ⟨r ξ,rfl⟩
  · exact n.range.isClosed_topologicalClosure.preimage r.continuous

private theorem star_mem_commutant (S : StarSubalgebra ℂ (Op (H:=H)))
    (r : Op (H:=H)) (hr : r∈centralizer (S:Set (Op (H:=H)))) :
    star r∈centralizer (S:Set (Op (H:=H))) := by
  intro a ha
  have he := congrArg star (hr (star a) (star_mem ha))
  simpa only [star_mul,star_star] using he.symm

theorem rangeSupport_mem_bicommutant (S : StarSubalgebra ℂ (Op (H:=H)))
    (n : Op (H:=H)) (hn : n∈centralizer (centralizer (S:Set (Op (H:=H))))) :
    rangeSupport n∈centralizer (centralizer (S:Set (Op (H:=H)))) := by
  let E := n.range.topologicalClosure
  letI : IsClosed (E:Set H) := n.range.isClosed_topologicalClosure
  intro r hr
  exact (projection_commutes E r
    (rangeClosure_invariant n r (hn r hr))
    (rangeClosure_invariant n (star r) (hn (star r) (star_mem_commutant S r hr)))).symm

theorem literal_nilpotent_supports (S : StarSubalgebra ℂ (Op (H:=H)))
    (n : Op (H:=H)) (hn : n∈centralizer (centralizer (S:Set (Op (H:=H)))))
    (h2 : n^2=0) :
    ∃ e f : Op (H:=H), IsSupportProjection (n*star n) e ∧
      IsSupportProjection (star n*n) f ∧
      e∈centralizer (centralizer (S:Set (Op (H:=H)))) ∧
      f∈centralizer (centralizer (S:Set (Op (H:=H)))) ∧
      e*f=0 ∧ f*e=0 ∧ e*n*f=n := by
  have hnstar : star n∈centralizer (centralizer (S:Set (Op (H:=H)))) := by
    intro r hr
    have hh := congrArg star (hn (star r) (star_mem_commutant S r hr))
    simpa only [star_mul,star_star] using hh.symm
  have hfmem : kernelComplement n∈centralizer (centralizer (S:Set (Op (H:=H)))) := by
    rw [kernelComplement_eq_rangeSupport_star]
    exact rangeSupport_mem_bicommutant S (star n) hnstar
  exact ⟨rangeSupport n,kernelComplement n,rangeSupport_is_support n,
    kernelComplement_is_support n,rangeSupport_mem_bicommutant S n hn,hfmem,
    (squareZero_supports_orthogonal n h2).1,(squareZero_supports_orthogonal n h2).2,
    by rw [rangeSupport_mul,mul_kernelComplement]⟩

end SpectralIsometry.SupportIdentification

