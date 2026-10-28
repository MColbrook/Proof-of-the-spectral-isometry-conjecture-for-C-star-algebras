module
public import SpectralIsometry.StrongStarApproximation
public import SpectralIsometry.BidualFoundation
public import Mathlib.Topology.ContinuousMap.Bounded.Star
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.InnerProductSpace.StarOrder
public import Mathlib.Topology.UniformSpace.UniformConvergence
public import Mathlib.Topology.Sequences
import Mathlib.Tactic.FunProp

/-!
# Bounded Strong Star Net Graph

Supporting results for spectral isometries of complex unital C*-algebras.
-/

 

@[expose] public section
set_option autoImplicit false
noncomputable section
open Filter Topology
open scoped BoundedContinuousFunction

namespace SpectralIsometry.BoundedStrongStarNetGraph
open StrongStarApproximation

variable {I A H : Type*} [TopologicalSpace I] [CStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local instance boundedFunctionsCStar : CStarAlgebra (I →ᵇ A) where

variable (M : VonNeumannAlgebra H) (j : A →⋆ₐ[ℂ] M)
  (hnorm : ∀ a : A, ‖j a‖≤‖a‖) (l : Filter I)

def Converges (p : (I →ᵇ A) × M) : Prop :=
  StrongStarTendsto (fun i => (j (p.1 i) : H →L[ℂ] H)) l (p.2 : H →L[ℂ] H)

include hnorm

theorem pointwise_norm_bound (f : I →ᵇ A) (i : I) :
    ‖(j (f i) : H →L[ℂ] H)‖≤‖f‖ :=
  (hnorm (f i)).trans (f.norm_coe_le_norm i)

def graph : StarSubalgebra ℂ ((I →ᵇ A) × M) where
  carrier := {p | Converges M j l p}
  zero_mem' := by
    change StrongStarTendsto (fun _ : I => (j (0:A):H →L[ℂ] H)) l (0:M)
    simpa only [map_zero] using strongStarTendsto_const l ((0:M):H →L[ℂ] H)
  one_mem' := by
    change StrongStarTendsto (fun _ : I => (j (1:A):H →L[ℂ] H)) l (1:M)
    simpa only [map_one] using strongStarTendsto_const l ((1:M):H →L[ℂ] H)
  add_mem' := by
    intro p q hp hq
    constructor
    · intro ξ
      change Tendsto (fun i => (j (p.1 i+q.1 i):H →L[ℂ] H) ξ) l
        (𝓝 ((p.2+q.2:H →L[ℂ] H) ξ))
      simpa only [map_add,AddMemClass.coe_add,ContinuousLinearMap.add_apply] using
        (hp.1 ξ).add (hq.1 ξ)
    · intro ξ
      change Tendsto (fun i => (star (j (p.1 i+q.1 i):H →L[ℂ] H)) ξ) l
        (𝓝 ((star (p.2+q.2:H →L[ℂ] H)) ξ))
      simpa only [map_add,AddMemClass.coe_add,star_add,ContinuousLinearMap.add_apply] using
        (hp.2 ξ).add (hq.2 ξ)
  mul_mem' := by
    intro p q hp hq
    have hh := strongStarTendsto_mul_of_norm_bounds hp hq
      (Eventually.of_forall (pointwise_norm_bound M j hnorm p.1))
      (Eventually.of_forall (pointwise_norm_bound M j hnorm q.1))
    change StrongStarTendsto (fun i => (j (p.1 i*q.1 i):H →L[ℂ] H)) l
      ((p.2*q.2:M):H →L[ℂ] H)
    simpa only [map_mul,MulMemClass.coe_mul] using hh
  algebraMap_mem' := by
    intro z
    change StrongStarTendsto (fun _ : I =>
      (j (algebraMap ℂ A z):H →L[ℂ] H)) l (algebraMap ℂ M z:H →L[ℂ] H)
    simpa only [AlgHomClass.commutes] using
      strongStarTendsto_const l (algebraMap ℂ M z:H →L[ℂ] H)
  star_mem' := by
    intro p hp
    change StrongStarTendsto (fun i => (j (star (p.1 i)):H →L[ℂ] H)) l
      ((star p.2:M):H →L[ℂ] H)
    simpa only [map_star,StarMemClass.coe_star] using strongStarTendsto_star hp

theorem evaluation_difference_bound (f g : I →ᵇ A) (ξ : H) (i : I) :
    ‖(j (f i):H →L[ℂ] H) ξ-(j (g i):H →L[ℂ] H) ξ‖≤‖f-g‖*‖ξ‖ := by
  calc
    _=‖(j (f i-g i):H →L[ℂ] H) ξ‖ := by rw [map_sub]; rfl
    _≤‖j (f i-g i)‖*‖ξ‖ := (j (f i-g i):H →L[ℂ] H).le_opNorm ξ
    _≤‖f i-g i‖*‖ξ‖ := mul_le_mul_of_nonneg_right (hnorm _) (norm_nonneg ξ)
    _≤‖f-g‖*‖ξ‖ :=
      mul_le_mul_of_nonneg_right ((f-g).norm_coe_le_norm i) (norm_nonneg ξ)

theorem uniform_evaluation {f : ℕ → (I →ᵇ A)} {g : I →ᵇ A}
    (hf : Tendsto f atTop (𝓝 g)) (ξ : H) :
    TendstoUniformly (fun n i => (j (f n i):H →L[ℂ] H) ξ)
      (fun i => (j (g i):H →L[ℂ] H) ξ) atTop := by
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  have hz : Tendsto (fun n => ‖g-f n‖*‖ξ‖) atTop (𝓝 0) := by
    simpa only [sub_self,norm_zero,zero_mul] using
      (((tendsto_const_nhds (x:=g)).sub hf).norm.mul_const ‖ξ‖)
  filter_upwards [hz.eventually (gt_mem_nhds hε)] with n hn i
  simpa only [dist_eq_norm] using
    (evaluation_difference_bound M j hnorm g (f n) ξ i).trans_lt hn

theorem graph_isClosed :
    IsClosed (graph M j hnorm l : Set ((I →ᵇ A) × M)) := by
  apply isSeqClosed_iff_isClosed.mp
  intro p q hp hq
  change Converges M j l q
  have hpf := (continuous_fst.tendsto q).comp hq
  have hps := (continuous_snd.tendsto q).comp hq
  constructor
  · intro ξ
    have hu := uniform_evaluation M j hnorm hpf ξ
    have hc : Continuous (fun b : M => (b:H →L[ℂ] H) ξ) := by fun_prop
    exact hu.tendsto_of_eventually_tendsto
      (Eventually.of_forall (fun n => (hp n).1 ξ)) (hc.tendsto _ |>.comp hps)
  · intro ξ
    have hu := uniform_evaluation M j hnorm hpf.star ξ
    have hc : Continuous (fun b : M => (star b:H →L[ℂ] H) ξ) := by fun_prop
    have hh : Tendsto (fun i => (j (star (q.1 i)):H →L[ℂ] H) ξ) l
        (𝓝 ((star q.2:H →L[ℂ] H) ξ)) := by
      exact hu.tendsto_of_eventually_tendsto
        (Eventually.of_forall (fun n => by
          simpa only [BoundedContinuousFunction.star_apply,map_star,StarMemClass.coe_star,
            Function.comp_def]
            using (hp n).2 ξ)) (hc.tendsto _ |>.comp hps)
    simpa only [map_star,StarMemClass.coe_star] using hh

instance graphCompleteSpace : CompleteSpace (graph M j hnorm l) :=
  (graph_isClosed M j hnorm l).completeSpace_coe

instance graphCStarAlgebra : CStarAlgebra (graph M j hnorm l) where

def firstHom : graph M j hnorm l →⋆ₐ[ℂ] (I →ᵇ A) :=
  (StarAlgHom.fst ℂ (I →ᵇ A) M).comp (graph M j hnorm l).subtype

def limitHom : graph M j hnorm l →⋆ₐ[ℂ] M :=
  (StarAlgHom.snd ℂ (I →ᵇ A) M).comp (graph M j hnorm l).subtype

theorem limit_norm_le [l.NeBot] (p : graph M j hnorm l) :
    ‖p.val.2‖≤‖p.val.1‖ := by
  apply ContinuousLinearMap.opNorm_le_bound (p.val.2:H →L[ℂ] H) (norm_nonneg _)
  intro ξ
  apply le_of_tendsto ((p.property.1 ξ).norm)
  exact Eventually.of_forall (fun i =>
    ((j (p.val.1 i):H →L[ℂ] H).le_opNorm ξ).trans
      (mul_le_mul_of_nonneg_right (pointwise_norm_bound M j hnorm p.val.1 i)
        (norm_nonneg ξ)))

theorem graph_norm [l.NeBot] (p : graph M j hnorm l) :
    ‖p‖=‖firstHom M j hnorm l p‖ := by
  change max ‖p.val.1‖ ‖p.val.2‖=‖p.val.1‖
  exact max_eq_left (limit_norm_le M j hnorm l p)

theorem firstHom_isometry [l.NeBot] : Isometry (firstHom M j hnorm l) :=
  AddMonoidHomClass.isometry_of_norm (firstHom M j hnorm l)
    (fun p => (graph_norm M j hnorm l p).symm)

theorem firstHom_range [l.NeBot] :
    Set.range (firstHom M j hnorm l)=
      {f : I →ᵇ A | ∃ b : M, Converges M j l (f,b)} := by
  apply Set.ext
  intro f
  constructor
  · rintro ⟨p,rfl⟩
    exact ⟨p.val.2,p.property⟩
  · rintro ⟨b,hb⟩
    exact ⟨⟨(f,b),hb⟩,rfl⟩

theorem convergent_nets_isClosed [l.NeBot] :
    IsClosed {f : I →ᵇ A | ∃ b : M, Converges M j l (f,b)} := by
  rw [←firstHom_range M j hnorm l]
  exact (firstHom_isometry M j hnorm l).isClosedEmbedding.isClosed_range

theorem limitHom_norm_bound [l.NeBot] (p : graph M j hnorm l) :
    ‖limitHom M j hnorm l p‖≤‖p‖ := by
  rw [graph_norm M j hnorm l p]
  exact limit_norm_le M j hnorm l p

end SpectralIsometry.BoundedStrongStarNetGraph

