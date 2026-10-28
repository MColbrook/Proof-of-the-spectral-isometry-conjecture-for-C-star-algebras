module

public import OAI.Analysis.BoundedHochschild.PathStages
public import OAI.Analysis.BoundedHochschild.NormalMultiplication
public import OAI.Analysis.BoundedHochschild.OrthogonalProjectionSums

/-!
# Center Trace Gluing

Supporting results for spectral isometries of complex unital C*-algebras.
-/

 

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace SpectralIsometry.CenterTraceGluing

open OAI.BoundedHochschild OAI.HochschildSakai Filter Topology

universe u v
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

theorem exists_bounded_gluing (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    {I : Type v} (p : I → M) (hp : ∀ i, IsStarProjection (p i))
    (ho : ∀ i j, i≠j → p i*p j=0) (g : I → M →L[ℂ] M)
    (hleft : ∀ i a, p i*g i a=g i a)
    (hright : ∀ i a, g i a*p i=g i a)
    (hbound : ∀ i a, ‖g i a‖≤‖a‖) :
    ∃ E : M →L[ℂ] M, (∀ a, ‖E a‖≤‖a‖) ∧
      ∀ i a, p i*E a=g i a := by
  classical
  let F (s : Finset I) : M →L[ℂ] M := ∑ i ∈ s, g i
  have hF (s : Finset I) (a : M) : ‖F s a‖≤‖a‖ := by
    change ‖(∑ i ∈ s,g i) a‖≤‖a‖
    rw [sum_apply]
    exact supported_sum_norm_le p (fun i => g i a) hp ho
      (fun i => hleft i a) (fun i => hright i a) s ‖a‖ (norm_nonneg a)
      (fun i _ => hbound i a)
  let U : Ultrafilter (Finset I) := Ultrafilter.of atTop
  have hU : (U : Filter (Finset I))≤atTop := Ultrafilter.of_le _
  have hex (a : M) : ∃ b : M, ‖b‖≤‖a‖ ∧
      PredualTendsto e (fun s => F s a) U b :=
    exists_predual_ultralimit e U (fun s => F s a) ‖a‖ (fun s => hF s a)
  choose b hb ht using hex
  let E₀ : M →ₗ[ℂ] M :=
    { toFun := b
      map_add' := fun a c => by
        apply predual_tendsto_unique e (ht (a+c))
        simpa only [map_add] using predual_tendsto_add e (ht a) (ht c)
      map_smul' := fun c a => by
        apply predual_tendsto_unique e (ht (c • a))
        simpa only [map_smul,RingHom.id_apply] using predual_tendsto_smul e (ht a) c }
  let E : M →L[ℂ] M := E₀.mkContinuous 1 (fun a => by
    change ‖b a‖≤1*‖a‖
    simpa only [one_mul] using hb a)
  refine ⟨E,hb,?_⟩
  intro i a
  have hlim := predual_tendsto_mul_left e (p i) (ht a)
  have heq : (fun s => p i*F s a)=ᶠ[U] (fun _ => g i a) := by
    apply hU
    filter_upwards [eventually_ge_atTop ({i} : Finset I)] with s hs
    have hi : i∈s := hs (Finset.mem_singleton_self i)
    change p i*(∑ j ∈ s,g j) a=g i a
    rw [sum_apply,Finset.mul_sum,Finset.sum_eq_single i]
    · exact hleft i a
    · intro j _ hji
      calc
        p i*g j a = p i*(p j*g j a) := by rw [hleft]
        _ = 0 := by rw [←mul_assoc,ho i j hji.symm,zero_mul]
    · exact fun hn => (hn hi).elim
  apply predual_tendsto_unique e hlim
  intro z
  exact tendsto_const_nhds.congr' (heq.mono fun _ h =>
    congrArg (fun c : M => e.symm c z) h.symm)

theorem exists_positive_gluing (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    {I : Type v} (p : I → M) (hp : ∀ i, IsStarProjection (p i))
    (ho : ∀ i j, i≠j → p i*p j=0)
    (htotal : ∀ a : M, (∀ i, p i*a=0) → a=0)
    (g : I → M →L[ℂ] M) (hleft : ∀ i a, p i*g i a=g i a)
    (hright : ∀ i a, g i a*p i=g i a)
    (hbound : ∀ i a, ‖g i a‖≤‖a‖)
    (hpos : ∀ i a, 0≤a → 0≤g i a) :
    ∃ E : M →L[ℂ] M, (∀ a, ‖E a‖≤‖a‖) ∧
      (∀ i a, p i*E a=g i a) ∧ ∀ a, 0≤a → 0≤E a := by
  classical
  obtain ⟨E,hnorm,hpiece⟩ := exists_bounded_gluing e p hp ho g hleft hright hbound
  refine ⟨E,hnorm,hpiece,?_⟩
  intro a ha
  obtain ⟨P,hP,hupper,_,ht⟩ :=
    OAI.BoundedHochschild.KadisonRingrose.exists_orthogonal_projection_sum e p hp ho
  have hP1 : P=1 := by
    have hz : 1-P=0 := htotal _ (fun i => by
      rw [mul_sub,mul_one,((hp i).le_iff_mul_eq_left hP).mp (hupper i),sub_self])
    exact (sub_eq_zero.mp hz).symm
  have hlim := predual_tendsto_mul_right e (E a) ht
  rw [hP1,one_mul] at hlim
  have heq : (fun s : Finset I => (∑ i ∈ s,p i)*E a)=
      (fun s : Finset I => ∑ i ∈ s,g i a) := by
    funext s
    simp only [Finset.sum_mul,hpiece]
  rw [heq] at hlim
  apply nonneg_of_bounded_predual_limit e ‖a‖ (norm_nonneg a) _ _ hlim
  · apply Filter.Eventually.of_forall
    intro s
    exact supported_sum_norm_le p (fun i => g i a) hp ho
      (fun i => hleft i a) (fun i => hright i a) s ‖a‖ (norm_nonneg a)
      (fun i _ => hbound i a)
  · exact Filter.Eventually.of_forall (fun s => Finset.sum_nonneg (fun i _ => hpos i a ha))

end SpectralIsometry.CenterTraceGluing

