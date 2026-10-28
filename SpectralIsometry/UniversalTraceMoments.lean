module

public import SpectralIsometry.Basic
public import SpectralIsometry.BidualOperatorCore
public import SpectralIsometry.UniversalNormalContinuity
public import SpectralIsometry.BidualTraceExtension

/-!
# Universal Trace Moments

Supporting results for spectral isometries of complex unital C*-algebras.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open Filter Topology
open scoped InnerProductSpace ComplexOrder

namespace SpectralIsometry.BidualFoundation.UniversalTraceMoments
open UniversalWeakClosure CoefficientPredual OperatorExtension StrongStarApproximation

private theorem norm_pow_bound {D : Type*} [CStarAlgebra D]
    (x : D) (C : ℝ) (hx : ‖x‖≤C) (n : ℕ) : ‖x^n‖≤C^n := by
  cases subsingleton_or_nontrivial D with
  | inl hD =>
    letI := hD
    have hxzero : x=0 := Subsingleton.elim _ _
    have hpowzero : x^n=0 := Subsingleton.elim _ _
    have hC : 0≤C := by simpa only [hxzero, norm_zero] using hx
    simpa only [hpowzero, norm_zero] using pow_nonneg hC n
  | inr hD =>
    letI := hD
    exact (norm_pow_le x n).trans (pow_le_pow_left₀ (norm_nonneg x) hx n)

private theorem strongStarTendsto_pow {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] {ι : Type*} {l : Filter ι}
    {a : ι → (H →L[ℂ] H)} {b : H →L[ℂ] H}
    (ha : StrongStarTendsto a l b) (C : ℝ) (hC : ∀ i, ‖a i‖≤C) (n : ℕ) :
    StrongStarTendsto (fun i => a i^n) l (b^n) := by
  induction n with
  | zero => simpa only [pow_zero] using strongStarTendsto_const (H:=H) l 1
  | succ n ih =>
    have hp := strongStarTendsto_mul_of_norm_bounds ih ha
      (Eventually.of_forall fun i => norm_pow_bound (a i) C (hC i) n)
      (Eventually.of_forall hC)
    simpa only [pow_succ] using hp

private def operatorInclusion {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (M : VonNeumannAlgebra H) :
    M →L[ℂ] (H →L[ℂ] H) where
  toLinearMap :=
    { toFun := Subtype.val
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  cont := continuous_subtype_val

universe u
variable {A : Type u} [CStarAlgebra A]
attribute [local instance] orderedA starOrderedA
attribute [local instance 2000] complexOrder complexStarOrder
attribute [local instance] complexNormedSpaceSelf predualNormedGroup predualNormedSpace
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2400000

private theorem lift_strongStarTendsto (T : A →L[ℂ] A) {ι : Type*} {l : Filter ι}
    (a : ι → algebra A) (x : algebra A)
    (ha : StrongStarTendsto (fun i => (a i : Hilbert A →L[ℂ] Hilbert A)) l
      (x : Hilbert A →L[ℂ] Hilbert A)) :
    StrongStarTendsto (fun i => (lift T (a i) : Hilbert A →L[ℂ] Hilbert A)) l
      (lift T x : Hilbert A →L[ℂ] Hilbert A) := by
  let V := (operatorInclusion (algebra A)).comp (lift T)
  have hV : UniversalNormalContinuity.HasNormalCoefficients A V :=
    fun ξ η => lift_vector_pairing T ξ η
  exact UniversalNormalContinuity.strongStarTendsto_map A V hV a x ha

/-- The actual bidual-model moment identity, including source powers 2 and 3.
The normal predual, density and lifted strong-star continuity are constructions,
not extra hypotheses. The theorem does not assume radius preservation on M_A. -/
theorem trace_entire_group_moments_universal (δ : A →L[ℂ] A)
    (hRad : ∀ z : ℂ, PreservesRadius
      (NormedSpace.exp (z • δ) : A →L[ℂ] A).toLinearMap)
    (Φ : predual A)
    (hpos : ∀ m : algebra A, 0 ≤ (Φ : StrongDual ℂ (algebra A)) (star m*m))
    (h1 : (Φ : StrongDual ℂ (algebra A)) 1=1)
    (htr : ∀ m n : algebra A,
      (Φ : StrongDual ℂ (algebra A)) (m*n)=(Φ : StrongDual ℂ (algebra A)) (n*m))
    (b : algebra A) (n : ℕ) (z : ℂ) :
    (Φ : StrongDual ℂ (algebra A)) ((lift (NormedSpace.exp (z • δ) : A →L[ℂ] A) b)^n) =
      (Φ : StrongDual ℂ (algebra A)) (b^n) := by
  let τ : A →ₗ[ℂ] ℂ := (restriction A Φ).toLinearMap
  have hτpos (a : A) : 0≤τ (star a*a) := by
    change 0≤(Φ : StrongDual ℂ (algebra A)) (inclusion A (star a*a))
    simpa only [map_mul, map_star] using hpos (inclusion A a)
  have hτ1 : τ 1=1 := by
    change (Φ : StrongDual ℂ (algebra A)) (inclusion A 1)=1
    simpa only [map_one] using h1
  have hτtr (a c : A) : τ (a*c)=τ (c*a) := by
    change (Φ : StrongDual ℂ (algebra A)) (inclusion A (a*c))=
      (Φ : StrongDual ℂ (algebra A)) (inclusion A (c*a))
    simpa only [map_mul] using htr (inclusion A a) (inclusion A c)
  let T : A →L[ℂ] A := NormedSpace.exp (z • δ)
  obtain ⟨a,haN,haT⟩ := UniversalApproximation.exists_bounded_net A b
  letI : (atTop : Filter (UniversalApproximation.Index A)).NeBot := UniversalApproximation.index_neBot A
  have haBound (i : UniversalApproximation.Index A) :
      ‖(inclusion A (a i) : Hilbert A →L[ℂ] Hilbert A)‖≤‖b‖ :=
    (inclusion_norm A (a i)).le.trans (haN i)
  have hVa := lift_strongStarTendsto T (fun i => inclusion A (a i)) b haT
  have hVaBound (i : UniversalApproximation.Index A) :
      ‖(lift T (inclusion A (a i)) : Hilbert A →L[ℂ] Hilbert A)‖≤‖lift T‖*‖b‖ :=
    ((lift T).le_opNorm _).trans
      (mul_le_mul_of_nonneg_left (by simpa only [inclusion_norm] using haN i) (norm_nonneg _))
  have hpA := strongStarTendsto_pow haT ‖b‖ haBound n
  have hpV := strongStarTendsto_pow hVa (‖lift T‖*‖b‖) hVaBound n
  have hscalarA := coefficientPredual_tendsto_of_strong (algebra A) (‖b‖^n)
    (a:=fun i => (inclusion A (a i))^n) (T:=b^n)
    (fun i => norm_pow_bound _ ‖b‖ (by simpa only [inclusion_norm] using haN i) n)
    (norm_pow_bound b ‖b‖ le_rfl n)
    (by
      intro η
      simpa only [SubmonoidClass.coe_pow] using hpA.1 η) Φ
  have hscalarV := coefficientPredual_tendsto_of_strong (algebra A) ((‖lift T‖*‖b‖)^n)
    (a:=fun i => (lift T (inclusion A (a i)))^n) (T:=(lift T b)^n)
    (fun i => norm_pow_bound _ (‖lift T‖*‖b‖) (hVaBound i) n)
    (norm_pow_bound _ (‖lift T‖*‖b‖) ((lift T).le_opNorm b) n)
    (by
      intro η
      simpa only [SubmonoidClass.coe_pow] using hpV.1 η) Φ
  have heach (i : UniversalApproximation.Index A) :
      (Φ : StrongDual ℂ (algebra A)) ((lift T (inclusion A (a i)))^n) =
        (Φ : StrongDual ℂ (algebra A)) ((inclusion A (a i))^n) := by
    have horiginal := SpectralIsometry.trace_entire_group_moments δ hRad τ hτpos hτ1 hτtr (a i) n z
    calc
      (Φ : StrongDual ℂ (algebra A)) ((lift T (inclusion A (a i)))^n) =
          (Φ : StrongDual ℂ (algebra A)) ((inclusion A (T (a i)))^n) :=
        congrArg (fun m : algebra A => (Φ : StrongDual ℂ (algebra A)) (m^n)) (lift_inclusion T (a i))
      _ = τ ((T (a i))^n) := congrArg (Φ : StrongDual ℂ (algebra A)) ((inclusion A).map_pow (T (a i)) n).symm
      _ = τ ((a i)^n) := horiginal
      _ = (Φ : StrongDual ℂ (algebra A)) ((inclusion A (a i))^n) :=
        congrArg (Φ : StrongDual ℂ (algebra A)) ((inclusion A).map_pow (a i) n)
  have heq : (fun i => (Φ : StrongDual ℂ (algebra A)) ((lift T (inclusion A (a i)))^n)) =
      (fun i => (Φ : StrongDual ℂ (algebra A)) ((inclusion A (a i))^n)) := funext heach
  have hright : Tendsto
      (fun i => (Φ : StrongDual ℂ (algebra A)) ((lift T (inclusion A (a i)))^n)) atTop
      (𝓝 ((Φ : StrongDual ℂ (algebra A)) (b^n))) :=
    (congrArg (fun f : UniversalApproximation.Index A → ℂ =>
      Tendsto f atTop (𝓝 ((Φ : StrongDual ℂ (algebra A)) (b^n)))) heq).mpr hscalarA
  exact tendsto_nhds_unique hscalarV hright

end SpectralIsometry.BidualFoundation.UniversalTraceMoments

