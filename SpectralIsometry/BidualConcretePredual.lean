module

public import OAI.Analysis.BoundedHochschild.UniversalGNSRepresentation
public import OAI.Analysis.Commutator.FiniteStrongTest
public import Mathlib.Analysis.Normed.Module.DoubleDual

/-!
# Bidual Concrete Predual

Supporting results for spectral isometries of complex unital C*-algebras.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace SpectralIsometry.BidualFoundation

universe u

/-- A Hilbert representation package, without public order or predual data. -/
structure FaithfulHilbertModel (A : Type u) [CStarAlgebra A] where
  H : Type u
  [normed : NormedAddCommGroup H]
  [innerSpace : InnerProductSpace ℂ H]
  [complete : CompleteSpace H]
  representation : A →⋆ₐ[ℂ] (H →L[ℂ] H)
  injective : Function.Injective representation
  norm_map : ∀ a : A, ‖representation a‖ = ‖a‖

attribute [instance] FaithfulHilbertModel.normed FaithfulHilbertModel.innerSpace
  FaithfulHilbertModel.complete

/-- Existing universal GNS proof with order constructed locally. Zero algebras,
nonseparable algebras and arbitrary universe u are retained. -/
def faithfulHilbertModel (A : Type u) [CStarAlgebra A] : FaithfulHilbertModel A := by
  letI := CStarAlgebra.spectralOrder A
  letI := CStarAlgebra.spectralOrderedRing A
  exact {
    H := OAI.BoundedHochschild.KadisonRingrose.UniversalGNS A
    representation := OAI.BoundedHochschild.KadisonRingrose.universalGNSRepresentation
    injective := OAI.BoundedHochschild.KadisonRingrose.universalGNSRepresentation_injective
    norm_map := OAI.BoundedHochschild.KadisonRingrose.universalGNSRepresentation_norm }

theorem faithfulHilbertModel_isometry (A : Type u) [CStarAlgebra A] :
    Isometry (faithfulHilbertModel A).representation := by
  apply isometry_iff_dist_eq.mpr
  intro a b
  rw [dist_eq_norm, dist_eq_norm, ← map_sub, (faithfulHilbertModel A).norm_map]

end SpectralIsometry.BidualFoundation

namespace SpectralIsometry.BidualFoundation.CoefficientPredual

open scoped InnerProductSpace

-- Keep the scalar self-module consistent with the normed operator-space API.
local instance complexNormedSpaceSelf : NormedSpace ℂ ℂ := NormedField.toNormedSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def vectorFunctional (M : VonNeumannAlgebra H) (ξ η : H) : StrongDual ℂ M :=
  (innerSL ℂ ξ).comp (OAI.Kadison.FiniteStrongTest.evaluation M η)

@[simp] theorem vectorFunctional_apply (M : VonNeumannAlgebra H) (ξ η : H) (T : M) :
    vectorFunctional M ξ η T = ⟪ξ, (T : H →L[ℂ] H) η⟫_ℂ := rfl

theorem vectorFunctional_norm_le (M : VonNeumannAlgebra H) (ξ η : H) :
    ‖vectorFunctional M ξ η‖ ≤ ‖ξ‖ * ‖η‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (norm_nonneg ξ) (norm_nonneg η))
  intro T
  calc
    ‖vectorFunctional M ξ η T‖ ≤ ‖ξ‖ * ‖(T : H →L[ℂ] H) η‖ := norm_inner_le_norm _ _
    _ ≤ ‖ξ‖ * (‖(T : H →L[ℂ] H)‖ * ‖η‖) :=
      mul_le_mul_of_nonneg_left ((T : H →L[ℂ] H).le_opNorm η) (norm_nonneg ξ)
    _ = (‖ξ‖ * ‖η‖) * ‖T‖ := by
      change ‖ξ‖ * (‖(T : H →L[ℂ] H)‖ * ‖η‖) =
        (‖ξ‖ * ‖η‖) * ‖(T : H →L[ℂ] H)‖
      ring

/-- An arbitrary-H predual candidate; no countable dense vector family is used. -/
local instance dualNormedGroup (M : VonNeumannAlgebra H) : NormedAddCommGroup (StrongDual ℂ M) :=
  inferInstance

local instance dualNormedSpace (M : VonNeumannAlgebra H) : NormedSpace ℂ (StrongDual ℂ M) :=
  inferInstance

abbrev coefficientPredual (M : VonNeumannAlgebra H) : Submodule ℂ (StrongDual ℂ M) :=
  (Submodule.span ℂ (Set.range (fun p : H × H => vectorFunctional M p.1 p.2))).topologicalClosure

instance (M : VonNeumannAlgebra H) : CompleteSpace (coefficientPredual M) := by
  dsimp only [coefficientPredual]
  infer_instance

local instance coefficientNormedGroup (M : VonNeumannAlgebra H) :
    NormedAddCommGroup (coefficientPredual M) := inferInstance

local instance coefficientNormedSpace (M : VonNeumannAlgebra H) :
    NormedSpace ℂ (coefficientPredual M) := inferInstance

def coefficientVector (M : VonNeumannAlgebra H) (ξ η : H) : coefficientPredual M :=
  ⟨vectorFunctional M ξ η, Submodule.le_topologicalClosure _
    (Submodule.subset_span (Set.mem_range_self (ξ, η)))⟩

@[simp] theorem coefficientVector_apply (M : VonNeumannAlgebra H) (ξ η : H) (T : M) :
    (coefficientVector M ξ η : StrongDual ℂ M) T = ⟪ξ, (T : H →L[ℂ] H) η⟫_ℂ := rfl

theorem coefficientVector_norm_le (M : VonNeumannAlgebra H) (ξ η : H) :
    ‖coefficientVector M ξ η‖ ≤ ‖ξ‖ * ‖η‖ := vectorFunctional_norm_le M ξ η

theorem coefficientVector_add_left (M : VonNeumannAlgebra H) (ξ ζ η : H) :
    coefficientVector M (ξ + ζ) η = coefficientVector M ξ η + coefficientVector M ζ η := by
  apply Subtype.ext
  ext T
  change ⟪ξ + ζ, (T : H →L[ℂ] H) η⟫_ℂ =
    ⟪ξ, (T : H →L[ℂ] H) η⟫_ℂ + ⟪ζ, (T : H →L[ℂ] H) η⟫_ℂ
  exact inner_add_left _ _ _

theorem coefficientVector_add_right (M : VonNeumannAlgebra H) (ξ η ζ : H) :
    coefficientVector M ξ (η + ζ) = coefficientVector M ξ η + coefficientVector M ξ ζ := by
  apply Subtype.ext
  ext T
  change ⟪ξ, (T : H →L[ℂ] H) (η + ζ)⟫_ℂ =
    ⟪ξ, (T : H →L[ℂ] H) η⟫_ℂ + ⟪ξ, (T : H →L[ℂ] H) ζ⟫_ℂ
  rw [map_add, inner_add_right]

theorem coefficientVector_smul_left (M : VonNeumannAlgebra H) (z : ℂ) (ξ η : H) :
    coefficientVector M (z • ξ) η = star z • coefficientVector M ξ η := by
  apply Subtype.ext
  ext T
  change ⟪z • ξ, (T : H →L[ℂ] H) η⟫_ℂ = star z * ⟪ξ, (T : H →L[ℂ] H) η⟫_ℂ
  simp only [inner_smul_left, Complex.star_def]

theorem coefficientVector_smul_right (M : VonNeumannAlgebra H) (z : ℂ) (ξ η : H) :
    coefficientVector M ξ (z • η) = z • coefficientVector M ξ η := by
  apply Subtype.ext
  ext T
  change ⟪ξ, (T : H →L[ℂ] H) (z • η)⟫_ℂ = z * ⟪ξ, (T : H →L[ℂ] H) η⟫_ℂ
  rw [map_smul, inner_smul_right]

theorem form_bound (M : VonNeumannAlgebra H)
    (F : StrongDual ℂ (coefficientPredual M)) (ξ η : H) :
    ‖star (F (coefficientVector M ξ η))‖ ≤ (‖F‖ * ‖η‖) * ‖ξ‖ := by
  calc
    ‖star (F (coefficientVector M ξ η))‖ = ‖F (coefficientVector M ξ η)‖ := norm_star _
    _ ≤ ‖F‖ * ‖coefficientVector M ξ η‖ := F.le_opNorm _
    _ ≤ ‖F‖ * (‖ξ‖ * ‖η‖) :=
      mul_le_mul_of_nonneg_left (coefficientVector_norm_le M ξ η) (norm_nonneg F)
    _ = (‖F‖ * ‖η‖) * ‖ξ‖ := by ring

def fiberFunctional (M : VonNeumannAlgebra H)
    (F : StrongDual ℂ (coefficientPredual M)) (η : H) : StrongDual ℂ H :=
  LinearMap.mkContinuous {
    toFun := fun ξ => star (F (coefficientVector M ξ η))
    map_add' := by
      intro ξ ζ
      rw [coefficientVector_add_left, map_add, star_add]
    map_smul' := by
      intro z ξ
      rw [coefficientVector_smul_left, map_smul, star_smul, star_star]
      rfl }
    (‖F‖ * ‖η‖) (fun ξ => form_bound M F ξ η)

def operatorValue (M : VonNeumannAlgebra H)
    (F : StrongDual ℂ (coefficientPredual M)) (η : H) : H :=
  (InnerProductSpace.toDual ℂ H).symm (fiberFunctional M F η)

theorem inner_operatorValue (M : VonNeumannAlgebra H)
    (F : StrongDual ℂ (coefficientPredual M)) (ξ η : H) :
    ⟪ξ, operatorValue M F η⟫_ℂ = F (coefficientVector M ξ η) := by
  have he : ⟪operatorValue M F η, ξ⟫_ℂ = star (F (coefficientVector M ξ η)) :=
    InnerProductSpace.toDual_symm_apply
  have hs := congrArg star he
  simpa only [Complex.star_def, inner_conj_symm, Complex.conj_conj] using hs

theorem operatorValue_norm_le (M : VonNeumannAlgebra H)
    (F : StrongDual ℂ (coefficientPredual M)) (η : H) :
    ‖operatorValue M F η‖ ≤ ‖F‖ * ‖η‖ := by
  calc
    ‖operatorValue M F η‖ = ‖fiberFunctional M F η‖ :=
      (InnerProductSpace.toDual ℂ H).symm.norm_map _
    _ ≤ ‖F‖ * ‖η‖ := by
      dsimp only [fiberFunctional]
      exact LinearMap.mkContinuous_norm_le _ (mul_nonneg (norm_nonneg F) (norm_nonneg η)) _

def operatorFromDual (M : VonNeumannAlgebra H)
    (F : StrongDual ℂ (coefficientPredual M)) : H →L[ℂ] H :=
  LinearMap.mkContinuous {
    toFun := operatorValue M F
    map_add' := by
      intro η ζ
      apply ext_inner_left ℂ
      intro ξ
      rw [inner_operatorValue, coefficientVector_add_right, map_add, inner_add_right,
        inner_operatorValue, inner_operatorValue]
    map_smul' := by
      intro z η
      apply ext_inner_left ℂ
      intro ξ
      rw [inner_operatorValue, coefficientVector_smul_right, map_smul, inner_smul_right,
        inner_operatorValue, smul_eq_mul]
      rfl }
    ‖F‖ (operatorValue_norm_le M F)

theorem operatorFromDual_norm_le (M : VonNeumannAlgebra H)
    (F : StrongDual ℂ (coefficientPredual M)) : ‖operatorFromDual M F‖ ≤ ‖F‖ := by
  dsimp only [operatorFromDual]
  exact LinearMap.mkContinuous_norm_le _ (norm_nonneg F) _

theorem inner_operatorFromDual (M : VonNeumannAlgebra H)
    (F : StrongDual ℂ (coefficientPredual M)) (ξ η : H) :
    ⟪ξ, operatorFromDual M F η⟫_ℂ = F (coefficientVector M ξ η) :=
  inner_operatorValue M F ξ η

theorem coefficientVector_commutant (M : VonNeumannAlgebra H)
    (b : H →L[ℂ] H) (hb : b ∈ M.commutant) (ξ η : H) :
    coefficientVector M ξ (b η) = coefficientVector M (star b ξ) η := by
  apply Subtype.ext
  ext T
  change ⟪ξ, (T : H →L[ℂ] H) (b η)⟫_ℂ =
    ⟪star b ξ, (T : H →L[ℂ] H) η⟫_ℂ
  have he := congrArg (fun U : H →L[ℂ] H => U η)
    ((VonNeumannAlgebra.mem_commutant_iff.mp hb) T T.property)
  change (T : H →L[ℂ] H) (b η) = b ((T : H →L[ℂ] H) η) at he
  rw [he, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_left]

/-- The reconstructed operator belongs to the bicommutant, with no separability
assumption on the Hilbert space. -/
theorem operatorFromDual_mem (M : VonNeumannAlgebra H)
    (F : StrongDual ℂ (coefficientPredual M)) : operatorFromDual M F ∈ M := by
  suffices h : operatorFromDual M F ∈ M.commutant.commutant by
    simpa only [M.commutant_commutant] using h
  apply VonNeumannAlgebra.mem_commutant_iff.mpr
  intro b hb
  ext η
  apply ext_inner_left ℂ
  intro ξ
  change ⟪ξ, b (operatorFromDual M F η)⟫_ℂ =
    ⟪ξ, operatorFromDual M F (b η)⟫_ℂ
  rw [← ContinuousLinearMap.adjoint_inner_left,
    inner_operatorFromDual, inner_operatorFromDual,
    coefficientVector_commutant M b hb, ContinuousLinearMap.star_eq_adjoint]

def elementFromDual (M : VonNeumannAlgebra H)
    (F : StrongDual ℂ (coefficientPredual M)) : M :=
  ⟨operatorFromDual M F, operatorFromDual_mem M F⟩

theorem elementFromDual_norm_le (M : VonNeumannAlgebra H)
    (F : StrongDual ℂ (coefficientPredual M)) : ‖elementFromDual M F‖ ≤ ‖F‖ :=
  operatorFromDual_norm_le M F

def evaluation (M : VonNeumannAlgebra H) (T : M) : StrongDual ℂ (coefficientPredual M) :=
  LinearMap.mkContinuous {
    toFun := fun φ => (φ : StrongDual ℂ M) T
    map_add' := by intros; rfl
    map_smul' := by intros; rfl }
    ‖T‖ (fun φ => by
      calc
        ‖(φ : StrongDual ℂ M) T‖ ≤ ‖(φ : StrongDual ℂ M)‖ * ‖T‖ := φ.val.le_opNorm T
        _ = ‖T‖ * ‖φ‖ := mul_comm _ _)

@[simp] theorem evaluation_apply (M : VonNeumannAlgebra H) (T : M)
    (φ : coefficientPredual M) : evaluation M T φ = (φ : StrongDual ℂ M) T := rfl

theorem evaluation_norm_le (M : VonNeumannAlgebra H) (T : M) :
    ‖evaluation M T‖ ≤ ‖T‖ := by
  dsimp only [evaluation]
  exact LinearMap.mkContinuous_norm_le _ (norm_nonneg T) _

theorem elementFromDual_evaluation (M : VonNeumannAlgebra H) (T : M) :
    elementFromDual M (evaluation M T) = T := by
  apply Subtype.ext
  ext η
  apply ext_inner_left ℂ
  intro ξ
  exact inner_operatorFromDual M (evaluation M T) ξ η

theorem evaluation_elementFromDual (M : VonNeumannAlgebra H)
    (F : StrongDual ℂ (coefficientPredual M)) :
    evaluation M (elementFromDual M F) = F := by
  obtain ⟨G, hG, _⟩ := exists_extension_norm_eq (coefficientPredual M) F
  let ev := NormedSpace.inclusionInDoubleDual ℂ M (elementFromDual M F)
  have hspan : Submodule.span ℂ (Set.range (fun p : H × H => vectorFunctional M p.1 p.2)) ≤
      (ev - G).ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨ξ, η⟩, rfl⟩
    change ⟪ξ, operatorFromDual M F η⟫_ℂ - G (vectorFunctional M ξ η) = 0
    rw [inner_operatorFromDual, ← hG (coefficientVector M ξ η)]
    exact sub_self _
  have hclosed : coefficientPredual M ≤ (ev - G).ker :=
    Submodule.topologicalClosure_minimal _ hspan (ev - G).isClosed_ker
  ext φ
  have hz := hclosed φ.property
  change (φ : StrongDual ℂ M) (elementFromDual M F) - G φ.val = 0 at hz
  exact (sub_eq_zero.mp hz).trans (hG φ)

/-- Evaluation identifies every concrete von Neumann algebra with the dual of
the norm-closed span of all its vector coefficient functionals. -/
def predualEvaluationEquiv (M : VonNeumannAlgebra H) :
    M ≃ₗᵢ[ℂ] StrongDual ℂ (coefficientPredual M) where
  toFun := evaluation M
  invFun := elementFromDual M
  left_inv := elementFromDual_evaluation M
  right_inv := evaluation_elementFromDual M
  map_add' := by intro S T; ext φ; exact φ.val.map_add S T
  map_smul' := by intro z T; ext φ; exact φ.val.map_smul z T
  norm_map' := by
    intro T
    apply le_antisymm (evaluation_norm_le M T)
    calc
      ‖T‖ = ‖elementFromDual M (evaluation M T)‖ := by rw [elementFromDual_evaluation]
      _ ≤ ‖evaluation M T‖ := elementFromDual_norm_le M _

/-- The conjugate-linear convention used by Mathlib's `WStarAlgebra`. -/
def concretePredualIsometry (M : VonNeumannAlgebra H) :
    StrongDual ℂ (coefficientPredual M) ≃ₗᵢ⋆[ℂ] M :=
  (predualEvaluationEquiv M).symm.trans (starₗᵢ ℂ)

/-- A Banach predual exists for every concrete von Neumann algebra, including
arbitrary nonseparable Hilbert spaces and the zero Hilbert space. -/
theorem concreteWStarAlgebra (M : VonNeumannAlgebra H) : WStarAlgebra M :=
  ⟨⟨coefficientPredual M, inferInstance, inferInstance, inferInstance,
    ⟨concretePredualIsometry M⟩⟩⟩

open Filter Topology ContinuousLinearMapWOT

/-- Continuity on every operator-norm bounded set equipped with WOT. -/
def BoundedWOTContinuous (M : VonNeumannAlgebra H) (f : StrongDual ℂ M) : Prop :=
  ∀ C : ℝ, Continuous (fun a : {T : H →WOT[ℂ] H // T.toCLM ∈ M ∧ ‖T.toCLM‖ ≤ C} =>
    f ⟨a.val.toCLM, a.property.1⟩)

def boundedNormal (M : VonNeumannAlgebra H) : Submodule ℂ (StrongDual ℂ M) where
  carrier := {f | BoundedWOTContinuous M f}
  zero_mem' := by intro C; exact continuous_const
  add_mem' := by intro f g hf hg C; exact (hf C).add (hg C)
  smul_mem' := by intro z f hf C; exact (hf C).const_smul z

/- The uniform-limit estimate below is adapted from openai/math,
OAI/Analysis/Commutator/NormalPredual.lean, normal_of_mem_closure
(same pinned revision and Apache-2.0 attribution as above). Its sufficient
direction has no separability hypothesis. Here the closed generating space uses
all vector coefficients, rather than coefficients of a fixed countable family. -/
theorem boundedNormal_isClosed (M : VonNeumannAlgebra H) :
    IsClosed (boundedNormal M : Set (StrongDual ℂ M)) := by
  apply IsSeqClosed.isClosed
  intro g f hg hlim
  change BoundedWOTContinuous M f
  intro C
  let D := {T : H →WOT[ℂ] H // T.toCLM ∈ M ∧ ‖T.toCLM‖ ≤ C}
  let a (T : D) : M := ⟨T.val.toCLM, T.property.1⟩
  have hn : Tendsto (fun n => ‖g n - f‖) atTop (𝓝 0) := by
    simpa only [sub_self, norm_zero] using
      (hlim.sub (tendsto_const_nhds (x := f))).norm
  have hu : TendstoUniformly (fun n (T : D) => g n (a T))
      (fun T => f (a T)) atTop := by
    apply Metric.tendstoUniformly_iff.mpr
    intro ε hε
    have hev := hn.eventually_lt_const (by positivity : (0 : ℝ) < ε / (|C| + 1))
    filter_upwards [hev] with n hn
    intro T
    have ha : ‖a T‖ ≤ |C| + 1 :=
      (show ‖a T‖ ≤ C from T.property.2).trans (by linarith [le_abs_self C])
    have hb : ‖(g n - f) (a T)‖ ≤ ‖g n - f‖ * (|C| + 1) :=
      ((g n - f).le_opNorm (a T)).trans
        (mul_le_mul_of_nonneg_left ha (norm_nonneg _))
    have hh : ‖g n - f‖ * (|C| + 1) < ε :=
      (lt_div_iff₀ (by positivity : (0 : ℝ) < |C| + 1)).mp hn
    rw [dist_eq_norm, norm_sub_rev]
    exact hb.trans_lt hh
  apply hu.continuous
  exact Filter.Eventually.frequently (Filter.Eventually.of_forall (fun n => hg n C))

theorem coefficientPredual_boundedWOT (M : VonNeumannAlgebra H)
    (φ : coefficientPredual M) : BoundedWOTContinuous M φ.val := by
  have hspan : Submodule.span ℂ (Set.range (fun p : H × H => vectorFunctional M p.1 p.2)) ≤
      boundedNormal M := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨ξ, η⟩, rfl⟩ C
    change Continuous (fun a : {T : H →WOT[ℂ] H // T.toCLM ∈ M ∧ ‖T.toCLM‖ ≤ C} =>
      ⟪ξ, a.val.toCLM η⟫_ℂ)
    exact ContinuousLinearMapWOT.continuous_inner_apply continuous_subtype_val η ξ
  exact (Submodule.topologicalClosure_minimal _ hspan (boundedNormal_isClosed M)) φ.property

theorem coefficientPredual_tendsto_of_strong (M : VonNeumannAlgebra H)
    {ι : Type*} {l : Filter ι} {a : ι → M} {T : M} (C : ℝ)
    (ha : ∀ i, ‖a i‖ ≤ C) (hT : ‖T‖ ≤ C)
    (hlim : ∀ η : H, Tendsto (fun i => (a i : H →L[ℂ] H) η) l
      (𝓝 ((T : H →L[ℂ] H) η))) (φ : coefficientPredual M) :
    Tendsto (fun i => (φ : StrongDual ℂ M) (a i)) l (𝓝 ((φ : StrongDual ℂ M) T)) := by
  let D := {U : H →WOT[ℂ] H // U.toCLM ∈ M ∧ ‖U.toCLM‖ ≤ C}
  let U (i : ι) : D := ⟨ContinuousLinearMapWOT.ofCLM (a i), (a i).property, ha i⟩
  let V : D := ⟨ContinuousLinearMapWOT.ofCLM T, T.property, hT⟩
  have hU : Tendsto U l (𝓝 V) := by
    apply tendsto_subtype_rng.mpr
    apply ContinuousLinearMapWOT.tendsto_iff_forall_inner_apply_tendsto.mpr
    intro η ξ
    exact tendsto_const_nhds.inner (hlim η)
  exact (coefficientPredual_boundedWOT M φ C).continuousAt.tendsto.comp hU

end SpectralIsometry.BidualFoundation.CoefficientPredual

