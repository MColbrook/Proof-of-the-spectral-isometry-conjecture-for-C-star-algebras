module

public import SpectralIsometry.FiniteBidualDecomposition
public import SpectralIsometry.Basic
public import SpectralIsometry.UniversalTraceMoments
public import SpectralIsometry.BidualExponentialGroup
public import SpectralIsometry.GenericCLMInverse

/-!
# Finite Quotient Assembly

Supporting results for spectral isometries of complex unital C*-algebras.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace SpectralIsometry.FiniteQuotientAssembly

open FiniteBidualDecomposition
open OAI.HochschildNormalPart OAI.BoundedHochschild.KadisonRingrose
open scoped ComplexOrder

universe u
variable {M X : Type u} [CStarAlgebra M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)

local instance orderedM : PartialOrder M := CStarAlgebra.spectralOrder M
local instance starOrderedM : StarOrderedRing M := CStarAlgebra.spectralOrderedRing M
local instance (priority := 2000) complexOrder : PartialOrder ℂ := Complex.partialOrder
local instance (priority := 2000) complexStarOrder : StarOrderedRing ℂ := RCLike.toStarOrderedRing

def normalTracialStates : Set (M →ₗ[ℂ] ℂ) :=
  {t | ∃ τ : M →ₚ[ℂ] ℂ, IsNormalTracialState e τ ∧ t=τ.toLinearMap}

theorem normal_tracial_states_separate (hfinite : FiniteAlgebra M) (x : M)
    (h : ∀ t ∈ normalTracialStates e, t (star x*x)=0) : x=0 := by
  apply eq_zero_of_all_normal_tracial_states e hfinite x
  intro τ hτ
  exact h τ.toLinearMap ⟨τ,hτ,rfl⟩

/-- The exact finite source reduction. Trace separation is proved from the
actual predual and finiteness, rather than supplied as a new hypothesis. -/
theorem finite_squares_of_moments (hfinite : FiniteAlgebra M) (K : M →ₗ[ℂ] M)
    (honto : Function.Surjective K)
    (h2 : ∀ τ : M →ₚ[ℂ] ℂ, IsNormalTracialState e τ →
      ∀ a : M, τ ((K a)^2)=τ (a^2))
    (h3 : ∀ τ : M →ₚ[ℂ] ℂ, IsNormalTracialState e τ →
      ∀ a : M, τ ((K a)^3)=τ (a^3)) :
    ∀ a : M, K (a^2)=(K a)^2 := by
  apply square_preserving_of_trace_pairings K honto (normalTracialStates e)
    (normal_tracial_states_separate e hfinite)
  intro t ht a b
  obtain ⟨τ,hτ,rfl⟩ := ht
  have hquad := trace_quadratic_polarization K τ.toLinearMap τ.toLinearMap
    hτ.2.2 hτ.2.2 (h2 τ hτ)
  have hcubic := trace_cubic_polarization K τ.toLinearMap τ.toLinearMap
    hτ.2.2 hτ.2.2 (h3 τ hτ)
  exact (hquad a (b^2)).trans (hcubic a b).symm

/-- Quadratic moments alone already prove injectivity on the finite part. -/
theorem finite_injective_of_quadratic_moments (hfinite : FiniteAlgebra M)
    (K : M →ₗ[ℂ] M)
    (h2 : ∀ τ : M →ₚ[ℂ] ℂ, IsNormalTracialState e τ →
      ∀ a : M, τ ((K a)^2)=τ (a^2)) : Function.Injective K := by
  have hz (x : M) (hx : K x=0) : x=0 := by
    apply eq_zero_of_all_normal_tracial_states e hfinite x
    intro τ hτ
    have hquad := trace_quadratic_polarization K τ.toLinearMap τ.toLinearMap
      hτ.2.2 hτ.2.2 (h2 τ hτ)
    simpa only [hx,mul_zero,map_zero,PositiveLinearMap.coe_toLinearMap] using
      (hquad (star x) x).symm
  intro a b hab
  apply sub_eq_zero.mp
  apply hz (a-b)
  rw [map_sub,hab,sub_self]

/-- A finite-quotient Jordan-isomorphism conclusion conditional only on its
explicit source moments and onto property. The entire-group assembly must
actually establish those inputs before claiming its principal conclusion. -/
theorem finite_jordan_of_moments (hfinite : FiniteAlgebra M) (K : M →ₗ[ℂ] M)
    (honto : Function.Surjective K)
    (h2 : ∀ τ : M →ₚ[ℂ] ℂ, IsNormalTracialState e τ →
      ∀ a : M, τ ((K a)^2)=τ (a^2))
    (h3 : ∀ τ : M →ₚ[ℂ] ℂ, IsNormalTracialState e τ →
      ∀ a : M, τ ((K a)^3)=τ (a^3)) : IsJordanIsomorphism K :=
  ⟨⟨finite_injective_of_quadratic_moments e hfinite K h2,honto⟩,
    finite_squares_of_moments e hfinite K honto h2 h3⟩

open OAI.HochschildCorners OAI.HochschildSakai OAI.BoundedHochschild

local instance canonicalCornerOrder (q : M) (hq : IsStarProjection q) :
    PartialOrder (Corner q hq) := CStarAlgebra.spectralOrder (Corner q hq)
local instance (priority := 2000) canonicalCornerLE (q : M) (hq : IsStarProjection q) :
    LE (Corner q hq) := (canonicalCornerOrder q hq).toLE
local instance canonicalCornerStarOrder (q : M) (hq : IsStarProjection q) :
    StarOrderedRing (Corner q hq) := CStarAlgebra.spectralOrderedRing (Corner q hq)

def centralCompressionHom (q : M) (hq : IsStarProjection q)
    (hqc : ∀ a : M, q*a=a*q) : M →⋆ₐ[ℂ] Corner q hq where
  toAlgHom := AlgHom.ofLinearMap (OAI.BoundedHochschild.CentralCorner.compressMap q hq hqc).toLinearMap
    (Subtype.ext (mul_one q)) (OAI.BoundedHochschild.CentralCorner.compressMap_mul q hq hqc)
  map_star' a := by
    apply Subtype.ext
    change q*star a=star (q*a)
    rw [star_mul,hq.isSelfAdjoint.star_eq,hqc]

@[simp] theorem centralCompressionHom_apply (q : M) (hq : IsStarProjection q)
    (hqc : ∀ a : M, q*a=a*q) (a : M) :
    (centralCompressionHom q hq hqc a : M)=q*a := rfl

theorem centralCompressionHom_nonneg (q : M) (hq : IsStarProjection q)
    (hqc : ∀ a : M, q*a=a*q) (a : M) (ha : 0≤a) :
    0≤centralCompressionHom q hq hqc a := by
  obtain ⟨b,rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp ha
  rw [map_mul (centralCompressionHom q hq hqc),map_star (centralCompressionHom q hq hqc)]
  exact star_mul_self_nonneg _

def centralPositiveTraceExtension (q : M) (hq : IsStarProjection q)
    (hqc : ∀ a : M, q*a=a*q) (τ : Corner q hq →ₚ[ℂ] ℂ) : M →ₚ[ℂ] ℂ where
  toLinearMap := τ.toLinearMap.comp (centralCompressionHom q hq hqc).toLinearMap
  monotone' := by
    exact (monotone_iff_map_nonneg
      (τ.toLinearMap.comp (centralCompressionHom q hq hqc).toLinearMap)).mpr
      (fun a ha => τ.map_nonneg (centralCompressionHom_nonneg q hq hqc a ha))

@[simp] theorem centralPositiveTraceExtension_apply (q : M) (hq : IsStarProjection q)
    (hqc : ∀ a : M, q*a=a*q) (τ : Corner q hq →ₚ[ℂ] ℂ) (a : M) :
    centralPositiveTraceExtension q hq hqc τ a=τ (centralCompressionHom q hq hqc a) := rfl

/-- A normal corner functional really extends normally through compression.
The actual quotient-predual representative and multiplication preadjoint
discharge normality; it is not an extra continuity hypothesis. -/
theorem centralFunctionalExtension_normal (q : M) (hq : IsStarProjection q)
    (hqc : ∀ a : M, q*a=a*q) (φ : StrongDual ℂ (Corner q hq))
    (hφ : φ ∈ normalDual (cornerPredualEquiv q hq e)) :
    φ.comp (OAI.BoundedHochschild.CentralCorner.compressMap q hq hqc) ∈ normalDual e := by
  obtain ⟨zq,hzq⟩ := (mem_normalDual (cornerPredualEquiv q hq e) φ).mp hφ
  obtain ⟨z,rfl⟩ := Submodule.Quotient.mk_surjective _ zq
  have heq : φ.comp (OAI.BoundedHochschild.CentralCorner.compressMap q hq hqc)=
      (predualEmbedding e z).comp (ContinuousLinearMap.mul ℂ M q) := by
    ext a
    change φ (OAI.BoundedHochschild.CentralCorner.compressMap q hq hqc a)=star (e.symm (q*a) z)
    simpa only [cornerPredualEquiv_symm_mk,OAI.BoundedHochschild.CentralCorner.compressMap_coe] using
      hzq (OAI.BoundedHochschild.CentralCorner.compressMap q hq hqc a)
  rw [heq]
  exact normalDual_comp e (show predualEmbedding e z ∈ normalDual e from ⟨z,rfl⟩)
    (ContinuousLinearMap.mul ℂ M q) ((abstract_multiplication_normal e).1 q)

theorem centralPositiveTraceExtension_normal (q : M) (hq : IsStarProjection q)
    (hqc : ∀ a : M, q*a=a*q) (τ : Corner q hq →ₚ[ℂ] ℂ)
    (hτ : TraceInPredual (cornerPredualEquiv q hq e) τ) :
    TraceInPredual e (centralPositiveTraceExtension q hq hqc τ) := by
  have hn : positiveFunctionalCLM τ ∈ normalDual (cornerPredualEquiv q hq e) :=
    (mem_normalDual (cornerPredualEquiv q hq e) _).mpr hτ
  have ht := centralFunctionalExtension_normal e q hq hqc (positiveFunctionalCLM τ) hn
  have heq : positiveFunctionalCLM (centralPositiveTraceExtension q hq hqc τ)=
      (positiveFunctionalCLM τ).comp (OAI.BoundedHochschild.CentralCorner.compressMap q hq hqc) := by
    ext a
    rfl
  exact (mem_normalDual e _).mp (heq.symm ▸ ht)

theorem centralPositiveTraceExtension_state (q : M) (hq : IsStarProjection q)
    (hqc : ∀ a : M, q*a=a*q) (τ : Corner q hq →ₚ[ℂ] ℂ)
    (hτ : IsNormalTracialState (cornerPredualEquiv q hq e) τ) :
    IsNormalTracialState e (centralPositiveTraceExtension q hq hqc τ) := by
  refine ⟨centralPositiveTraceExtension_normal e q hq hqc τ hτ.1,?_,?_⟩
  · change τ (centralCompressionHom q hq hqc 1)=1
    rw [map_one]
    exact hτ.2.1
  · intro a b
    change τ (centralCompressionHom q hq hqc (a*b))=
      τ (centralCompressionHom q hq hqc (b*a))
    rw [map_mul (centralCompressionHom q hq hqc) a b,
      map_mul (centralCompressionHom q hq hqc) b a]
    exact hτ.2.2 _ _

@[simp] theorem centralCompressionHom_include (q : M) (hq : IsStarProjection q)
    (hqc : ∀ a : M, q*a=a*q) (a : Corner q hq) :
    centralCompressionHom q hq hqc (a : M)=a := Subtype.ext a.property.1

/-- The actual finite-corner normal traces detect the compression kernel. -/
theorem centralCompression_eq_zero_iff (q : M) (hq : IsStarProjection q)
    (hqc : ∀ a : M, q*a=a*q) (hfinite : FiniteAlgebra (Corner q hq)) (x : M) :
    centralCompressionHom q hq hqc x=0 ↔
      ∀ τ : Corner q hq →ₚ[ℂ] ℂ,
        IsNormalTracialState (cornerPredualEquiv q hq e) τ →
        centralPositiveTraceExtension q hq hqc τ (star x*x)=0 := by
  constructor
  · intro hx τ hτ
    change τ (centralCompressionHom q hq hqc (star x*x))=0
    rw [map_mul (centralCompressionHom q hq hqc),
      map_star (centralCompressionHom q hq hqc),hx,mul_zero,map_zero]
  · intro h
    apply eq_zero_of_all_normal_tracial_states (cornerPredualEquiv q hq e) hfinite
    intro τ hτ
    simpa only [centralPositiveTraceExtension_apply,
      map_mul (centralCompressionHom q hq hqc),map_star (centralCompressionHom q hq hqc)] using h τ hτ

/-- Quadratic moments and onto already force invariance of the properly
infinite ideal, the kernel of the finite central compression. -/
theorem centralCompression_kernel_invariant (q : M) (hq : IsStarProjection q)
    (hqc : ∀ a : M, q*a=a*q) (hfinite : FiniteAlgebra (Corner q hq))
    (V : M →ₗ[ℂ] M) (honto : Function.Surjective V)
    (h2 : ∀ τ : M →ₚ[ℂ] ℂ, IsNormalTracialState e τ →
      ∀ a : M, τ ((V a)^2)=τ (a^2))
    (x : M) (hx : centralCompressionHom q hq hqc x=0) :
    centralCompressionHom q hq hqc (V x)=0 := by
  apply (centralCompression_eq_zero_iff e q hq hqc hfinite (V x)).mpr
  intro τ hτ
  let σ := centralPositiveTraceExtension q hq hqc τ
  have hσ := centralPositiveTraceExtension_state e q hq hqc τ hτ
  have hp := trace_quadratic_polarization V σ.toLinearMap σ.toLinearMap
    hσ.2.2 hσ.2.2 (h2 σ hσ)
  obtain ⟨y,hy⟩ := honto (star (V x))
  have heq := hp y x
  change σ (V y*V x)=σ (y*x) at heq
  rw [hy] at heq
  rw [heq]
  change τ (centralCompressionHom q hq hqc (y*x))=0
  rw [map_mul (centralCompressionHom q hq hqc),hx,mul_zero,map_zero]

/-- The finite block is defined by the actual corner inclusion/compression. -/
def finiteBlock (q : M) (hq : IsStarProjection q) (hqc : ∀ a : M, q*a=a*q)
    (V : M →ₗ[ℂ] M) : Corner q hq →ₗ[ℂ] Corner q hq :=
  (centralCompressionHom q hq hqc).toLinearMap.comp
    (V.comp (OAI.BoundedHochschild.CentralCorner.includeMap q hq).toLinearMap)

@[simp] theorem finiteBlock_apply (q : M) (hq : IsStarProjection q)
    (hqc : ∀ a : M, q*a=a*q) (V : M →ₗ[ℂ] M) (a : Corner q hq) :
    finiteBlock q hq hqc V a=centralCompressionHom q hq hqc (V (a : M)) := rfl

theorem finiteBlock_compression (q : M) (hq : IsStarProjection q)
    (hqc : ∀ a : M, q*a=a*q) (V : M →ₗ[ℂ] M)
    (hinv : ∀ x : M, centralCompressionHom q hq hqc x=0 →
      centralCompressionHom q hq hqc (V x)=0) (x : M) :
    finiteBlock q hq hqc V (centralCompressionHom q hq hqc x)=
      centralCompressionHom q hq hqc (V x) := by
  have hx : centralCompressionHom q hq hqc (x-(centralCompressionHom q hq hqc x : M))=0 := by
    rw [map_sub,centralCompressionHom_include,sub_self]
  have hv := hinv _ hx
  change centralCompressionHom q hq hqc (V (x-(centralCompressionHom q hq hqc x : M)))=0 at hv
  rw [map_sub,map_sub] at hv
  exact (sub_eq_zero.mp hv).symm

theorem finiteBlock_surjective (q : M) (hq : IsStarProjection q)
    (hqc : ∀ a : M, q*a=a*q) (V : M →ₗ[ℂ] M) (honto : Function.Surjective V)
    (hinv : ∀ x : M, centralCompressionHom q hq hqc x=0 →
      centralCompressionHom q hq hqc (V x)=0) :
    Function.Surjective (finiteBlock q hq hqc V) := by
  intro a
  obtain ⟨x,hx⟩ := honto (a : M)
  refine ⟨centralCompressionHom q hq hqc x,?_⟩
  rw [finiteBlock_compression q hq hqc V hinv,hx,centralCompressionHom_include]

theorem finiteBlock_one (q : M) (hq : IsStarProjection q)
    (hqc : ∀ a : M, q*a=a*q) (V : M →ₗ[ℂ] M) (h1 : V 1=1)
    (hinv : ∀ x : M, centralCompressionHom q hq hqc x=0 →
      centralCompressionHom q hq hqc (V x)=0) : finiteBlock q hq hqc V 1=1 := by
  simpa only [map_one,h1] using finiteBlock_compression q hq hqc V hinv 1

theorem finiteBlock_moment (q : M) (hq : IsStarProjection q)
    (hqc : ∀ a : M, q*a=a*q) (V : M →ₗ[ℂ] M) (n : ℕ)
    (hm : ∀ τ : M →ₚ[ℂ] ℂ, IsNormalTracialState e τ →
      ∀ a : M, τ ((V a)^n)=τ (a^n))
    (τ : Corner q hq →ₚ[ℂ] ℂ)
    (hτ : IsNormalTracialState (cornerPredualEquiv q hq e) τ) (a : Corner q hq) :
    τ ((finiteBlock q hq hqc V a)^n)=τ (a^n) := by
  have h := hm (centralPositiveTraceExtension q hq hqc τ)
    (centralPositiveTraceExtension_state e q hq hqc τ hτ) (a : M)
  simpa only [centralPositiveTraceExtension_apply,
    map_pow (centralCompressionHom q hq hqc),centralCompressionHom_include,
    finiteBlock_apply] using h

/-- Actual finite quotient assembly. Its explicit moment inputs will be
discharged by the universal entire-group moment identity. -/
theorem finiteBlock_jordan (q : M) (hq : IsStarProjection q)
    (hqc : ∀ a : M, q*a=a*q) (hfinite : FiniteAlgebra (Corner q hq))
    (V : M →ₗ[ℂ] M) (honto : Function.Surjective V)
    (h2 : ∀ τ : M →ₚ[ℂ] ℂ, IsNormalTracialState e τ →
      ∀ a : M, τ ((V a)^2)=τ (a^2))
    (h3 : ∀ τ : M →ₚ[ℂ] ℂ, IsNormalTracialState e τ →
      ∀ a : M, τ ((V a)^3)=τ (a^3)) :
    IsJordanIsomorphism (finiteBlock q hq hqc V) := by
  have hinv := centralCompression_kernel_invariant e q hq hqc hfinite V honto h2
  exact finite_jordan_of_moments (cornerPredualEquiv q hq e) hfinite
    (finiteBlock q hq hqc V) (finiteBlock_surjective q hq hqc V honto hinv)
    (finiteBlock_moment e q hq hqc V 2 h2) (finiteBlock_moment e q hq hqc V 3 h3)

theorem finiteBlock_comp (q : M) (hq : IsStarProjection q)
    (hqc : ∀ a : M, q*a=a*q) (V W : M →ₗ[ℂ] M)
    (hinv : ∀ x : M, centralCompressionHom q hq hqc x=0 →
      centralCompressionHom q hq hqc (V x)=0) :
    finiteBlock q hq hqc (V.comp W)=
      (finiteBlock q hq hqc V).comp (finiteBlock q hq hqc W) := by
  apply LinearMap.ext
  intro a
  exact (finiteBlock_compression q hq hqc V hinv (W (a:M))).symm

/-- The actual bounded corner block. This definition assumes neither that
the corner is finite nor that the original operator preserves it. -/
def centralBlockCLM (p : M) (hp : IsStarProjection p)
    (hpc : ∀ a : M, p*a=a*p) (V : M →L[ℂ] M) : Corner p hp →L[ℂ] Corner p hp :=
  (OAI.BoundedHochschild.CentralCorner.compressMap p hp hpc).comp
    (V.comp (OAI.BoundedHochschild.CentralCorner.includeMap p hp))

theorem centralBlockCLM_toLinearMap (p : M) (hp : IsStarProjection p)
    (hpc : ∀ a : M, p*a=a*p) (V : M →L[ℂ] M) :
    (centralBlockCLM p hp hpc V).toLinearMap=finiteBlock p hp hpc V.toLinearMap := rfl

theorem complement_corner_compression_zero (p q : M) (hp : IsStarProjection p)
    (hq : IsStarProjection q) (hqc : ∀ a : M, q*a=a*q) (hsum : p+q=1)
    (a : Corner p hp) : centralCompressionHom q hq hqc (a:M)=0 := by
  apply Subtype.ext
  change q*(a:M)=0
  have hqeq : q=1-p := by apply eq_sub_iff_add_eq.mpr; rw [add_comm,hsum]
  rw [hqeq,sub_mul,one_mul,a.property.1,sub_self]

theorem complement_projection_mul_of_kernel (p q : M) (hq : IsStarProjection q)
    (hqc : ∀ a : M, q*a=a*q) (hsum : p+q=1) (x : M)
    (hx : centralCompressionHom q hq hqc x=0) : p*x=x := by
  have hzero : q*x=0 := congrArg Subtype.val hx
  calc
    p*x=(p+q)*x := by rw [add_mul,hzero,add_zero]
    _ = x := by rw [hsum,one_mul]

/-- On the complementary corner this block is the genuine restriction,
provided the proved q-kernel invariance holds. No q-complement invariance is
assumed and the value at the corner unit is not replaced with the unit. -/
theorem centralBlockCLM_coe_of_kernel (p q : M) (hp : IsStarProjection p)
    (hq : IsStarProjection q) (hpc : ∀ a : M, p*a=a*p)
    (hqc : ∀ a : M, q*a=a*q) (hsum : p+q=1) (V : M →L[ℂ] M)
    (hinv : ∀ x : M, centralCompressionHom q hq hqc x=0 →
      centralCompressionHom q hq hqc (V x)=0) (a : Corner p hp) :
    (centralBlockCLM p hp hpc V a : M)=V (a:M) := by
  change p*V (a:M)=V (a:M)
  exact complement_projection_mul_of_kernel p q hq hqc hsum _
    (hinv _ (complement_corner_compression_zero p q hp hq hqc hsum a))

/-- Box the restriction composition identity in an abstract C*-algebra before
instantiating the much larger concrete universal-model dictionaries. -/
theorem centralBlockCLM_comp_of_kernel (p q : M) (hp : IsStarProjection p)
    (hq : IsStarProjection q) (hpc : ∀ a : M, p*a=a*p)
    (hqc : ∀ a : M, q*a=a*q) (hsum : p+q=1) (V W : M →L[ℂ] M)
    (hV : ∀ x : M, centralCompressionHom q hq hqc x=0 →
      centralCompressionHom q hq hqc (V x)=0)
    (hW : ∀ x : M, centralCompressionHom q hq hqc x=0 →
      centralCompressionHom q hq hqc (W x)=0) :
    centralBlockCLM p hp hpc (V.comp W)=
      (centralBlockCLM p hp hpc V).comp (centralBlockCLM p hp hpc W) := by
  apply ContinuousLinearMap.ext
  intro a
  apply Subtype.ext
  change p*V (W (a:M))=
    (centralBlockCLM p hp hpc V (centralBlockCLM p hp hpc W a):M)
  rw [centralBlockCLM_coe_of_kernel p q hp hq hpc hqc hsum V hV,
    centralBlockCLM_coe_of_kernel p q hp hq hpc hqc hsum W hW]
  exact complement_projection_mul_of_kernel p q hq hqc hsum _
    (hV _ (hW _ (complement_corner_compression_zero p q hp hq hqc hsum a)))

section ActualUniversalModel
open SpectralIsometry.BidualFoundation
open UniversalWeakClosure CoefficientPredual OperatorExtension
attribute [local instance] complexNormedSpaceSelf predualNormedGroup predualNormedSpace
attribute [local instance] orderedA starOrderedA
attribute [local instance 2000] UniversalWeakClosure.complexOrder UniversalWeakClosure.complexStarOrder

variable {A : Type u} [CStarAlgebra A]

local instance (priority := 3000) universalModelOrder : PartialOrder (algebra A) :=
  CStarAlgebra.spectralOrder (algebra A)
local instance (priority := 3000) universalModelLE : LE (algebra A) :=
  (universalModelOrder (A:=A)).toLE
local instance (priority := 3000) universalModelStarOrder : StarOrderedRing (algebra A) :=
  CStarAlgebra.spectralOrderedRing (algebra A)
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2400000

/-- Every actual normal tracial state on the canonical universal model has
all the original entire-family moments. Normal membership, not an assumed
extension principle, supplies the coefficient-predual functional. -/
theorem universal_normal_trace_moments (δ : A →L[ℂ] A)
    (hRad : ∀ z : ℂ, PreservesRadius
      (NormedSpace.exp (z • δ) : A →L[ℂ] A).toLinearMap)
    (τ : algebra A →ₚ[ℂ] ℂ)
    (hτ : IsNormalTracialState (concretePredualIsometry (algebra A)) τ)
    (n : ℕ) (z : ℂ) (b : algebra A) :
    τ ((lift (NormedSpace.exp (z • δ) : A →L[ℂ] A) b)^n)=τ (b^n) := by
  let Φ : predual A := ⟨positiveFunctionalCLM τ,by
    exact (le_of_eq (normalDual_eq_coefficientPredual (algebra A)))
      ((mem_normalDual (concretePredualIsometry (algebra A)) _).mpr hτ.1)⟩
  have hpos (m : algebra A) : 0≤(Φ : StrongDual ℂ (algebra A)) (star m*m) :=
    τ.map_nonneg (star_mul_self_nonneg m)
  exact UniversalTraceMoments.trace_entire_group_moments_universal δ hRad Φ hpos
    hτ.2.1 hτ.2.2 b n z

/-- The properly infinite ideal is invariant for the actual lifted family.
The finite central projection and its finiteness come from the proved central
decomposition; moments are discharged from the original radius hypothesis. -/
theorem universal_compression_kernel_invariant (q : algebra A) (hq : IsStarProjection q)
    (hqc : ∀ a : algebra A, q*a=a*q) (hfinite : FiniteAlgebra (Corner q hq))
    (δ : A →L[ℂ] A)
    (hRad : ∀ z : ℂ, PreservesRadius
      (NormedSpace.exp (z • δ) : A →L[ℂ] A).toLinearMap)
    (z : ℂ) (x : algebra A) (hx : centralCompressionHom q hq hqc x=0) :
    centralCompressionHom q hq hqc
      (lift (NormedSpace.exp (z • δ) : A →L[ℂ] A) x)=0 := by
  apply centralCompression_kernel_invariant (concretePredualIsometry (algebra A))
    q hq hqc hfinite (lift (NormedSpace.exp (z • δ) : A →L[ℂ] A)).toLinearMap
    (lift_exp_bijective δ z).2 ?_ x hx
  intro τ hτ b
  exact universal_normal_trace_moments δ hRad τ hτ 2 z b

/-- The actual induced finite map is Jordan for every complex parameter,
under only the original radius-family hypothesis. No moment or invariant-ideal
hypothesis remains in this conclusion. -/
theorem universal_finiteBlock_jordan (q : algebra A) (hq : IsStarProjection q)
    (hqc : ∀ a : algebra A, q*a=a*q) (hfinite : FiniteAlgebra (Corner q hq))
    (δ : A →L[ℂ] A)
    (hRad : ∀ z : ℂ, PreservesRadius
      (NormedSpace.exp (z • δ) : A →L[ℂ] A).toLinearMap) (z : ℂ) :
    IsJordanIsomorphism (finiteBlock q hq hqc
      (lift (NormedSpace.exp (z • δ) : A →L[ℂ] A)).toLinearMap) := by
  apply finiteBlock_jordan (concretePredualIsometry (algebra A)) q hq hqc hfinite
    (lift (NormedSpace.exp (z • δ) : A →L[ℂ] A)).toLinearMap (lift_exp_bijective δ z).2
  · intro τ hτ b
    exact universal_normal_trace_moments δ hRad τ hτ 2 z b
  · intro τ hτ b
    exact universal_normal_trace_moments δ hRad τ hτ 3 z b

theorem universal_finiteBlock_one (q : algebra A) (hq : IsStarProjection q)
    (hqc : ∀ a : algebra A, q*a=a*q) (hfinite : FiniteAlgebra (Corner q hq))
    (δ : A →L[ℂ] A)
    (h1 : ∀ z : ℂ, (NormedSpace.exp (z • δ) : A →L[ℂ] A) 1=1)
    (hRad : ∀ z : ℂ, PreservesRadius
      (NormedSpace.exp (z • δ) : A →L[ℂ] A).toLinearMap) (z : ℂ) :
    finiteBlock q hq hqc (lift (NormedSpace.exp (z • δ) : A →L[ℂ] A)).toLinearMap 1=1 :=
  finiteBlock_one q hq hqc _ (lift_exp_unital δ h1 z)
    (universal_compression_kernel_invariant q hq hqc hfinite δ hRad z)

/-- The properly infinite block keeps its original weight V_z(p); no
unitality of this restriction is assumed. -/
theorem universal_complementBlock_coe (p q : algebra A) (hp : IsStarProjection p)
    (hq : IsStarProjection q) (hpc : ∀ a : algebra A, p*a=a*p)
    (hqc : ∀ a : algebra A, q*a=a*q) (hsum : p+q=1)
    (hfinite : FiniteAlgebra (Corner q hq)) (δ : A →L[ℂ] A)
    (hRad : ∀ z : ℂ, PreservesRadius
      (NormedSpace.exp (z • δ) : A →L[ℂ] A).toLinearMap)
    (z : ℂ) (a : Corner p hp) :
    (centralBlockCLM p hp hpc (lift (NormedSpace.exp (z • δ) : A →L[ℂ] A)) a : algebra A)=
      lift (NormedSpace.exp (z • δ) : A →L[ℂ] A) (a:algebra A) :=
  centralBlockCLM_coe_of_kernel p q hp hq hpc hqc hsum _
    (universal_compression_kernel_invariant q hq hqc hfinite δ hRad z) a

theorem universal_complementBlock_inverse (p q : algebra A) (hp : IsStarProjection p)
    (hq : IsStarProjection q) (hpc : ∀ a : algebra A, p*a=a*p)
    (hqc : ∀ a : algebra A, q*a=a*q) (hsum : p+q=1)
    (hfinite : FiniteAlgebra (Corner q hq)) (δ : A →L[ℂ] A)
    (hRad : ∀ z : ℂ, PreservesRadius
      (NormedSpace.exp (z • δ) : A →L[ℂ] A).toLinearMap)
    (z : ℂ) (a : Corner p hp) :
    centralBlockCLM p hp hpc (lift (NormedSpace.exp ((-z) • δ) : A →L[ℂ] A))
      (centralBlockCLM p hp hpc (lift (NormedSpace.exp (z • δ) : A →L[ℂ] A)) a)=a := by
  apply Subtype.ext
  rw [universal_complementBlock_coe p q hp hq hpc hqc hsum hfinite δ hRad,
    universal_complementBlock_coe p q hp hq hpc hqc hsum hfinite δ hRad]
  exact lift_inverse_apply (expOperatorEquiv δ z) (a:algebra A)

/-- A genuine bounded equivalence of the properly infinite corner, with
inverse the negative parameter. Only the q-kernel invariance is used. -/
def universalComplementEquiv (p q : algebra A) (hp : IsStarProjection p)
    (hq : IsStarProjection q) (hpc : ∀ a : algebra A, p*a=a*p)
    (hqc : ∀ a : algebra A, q*a=a*q) (hsum : p+q=1)
    (hfinite : FiniteAlgebra (Corner q hq)) (δ : A →L[ℂ] A)
    (hRad : ∀ z : ℂ, PreservesRadius
      (NormedSpace.exp (z • δ) : A →L[ℂ] A).toLinearMap) (z : ℂ) :
    Corner p hp ≃L[ℂ] Corner p hp :=
  GenericCLMInverse.ofInverses
    (centralBlockCLM p hp hpc (lift (NormedSpace.exp (z • δ) : A →L[ℂ] A)))
    (centralBlockCLM p hp hpc (lift (NormedSpace.exp ((-z) • δ) : A →L[ℂ] A)))
    (universal_complementBlock_inverse p q hp hq hpc hqc hsum hfinite δ hRad z)
    (GenericCLMInverse.rightInv_of_negLeftInv
      (fun w : ℂ => (centralBlockCLM p hp hpc (lift (NormedSpace.exp (w • δ) : A →L[ℂ] A)) : Corner p hp → Corner p hp))
      (universal_complementBlock_inverse p q hp hq hpc hqc hsum hfinite δ hRad) z)

theorem universal_complementBlock_group (p q : algebra A) (hp : IsStarProjection p)
    (hq : IsStarProjection q) (hpc : ∀ a : algebra A, p*a=a*p)
    (hqc : ∀ a : algebra A, q*a=a*q) (hsum : p+q=1)
    (hfinite : FiniteAlgebra (Corner q hq)) (δ : A →L[ℂ] A)
    (hRad : ∀ z : ℂ, PreservesRadius
      (NormedSpace.exp (z • δ) : A →L[ℂ] A).toLinearMap) (z w : ℂ) :
    centralBlockCLM p hp hpc (lift (NormedSpace.exp ((z+w) • δ) : A →L[ℂ] A))=
      (centralBlockCLM p hp hpc (lift (NormedSpace.exp (z • δ) : A →L[ℂ] A))).comp
        (centralBlockCLM p hp hpc (lift (NormedSpace.exp (w • δ) : A →L[ℂ] A))) := by
  exact (congrArg (fun V : algebra A →L[ℂ] algebra A => centralBlockCLM p hp hpc V)
    (lift_exp_group δ z w)).trans
    (centralBlockCLM_comp_of_kernel p q hp hq hpc hqc hsum _ _
      (universal_compression_kernel_invariant q hq hqc hfinite δ hRad z)
      (universal_compression_kernel_invariant q hq hqc hfinite δ hRad w))

theorem universal_complementBlock_weight (p q : algebra A) (hp : IsStarProjection p)
    (hq : IsStarProjection q) (hpc : ∀ a : algebra A, p*a=a*p)
    (hqc : ∀ a : algebra A, q*a=a*q) (hsum : p+q=1)
    (hfinite : FiniteAlgebra (Corner q hq)) (δ : A →L[ℂ] A)
    (hRad : ∀ z : ℂ, PreservesRadius
      (NormedSpace.exp (z • δ) : A →L[ℂ] A).toLinearMap) (z : ℂ) :
    (centralBlockCLM p hp hpc (lift (NormedSpace.exp (z • δ) : A →L[ℂ] A)) 1 : algebra A)=
      lift (NormedSpace.exp (z • δ) : A →L[ℂ] A) p :=
  universal_complementBlock_coe p q hp hq hpc hqc hsum hfinite δ hRad z 1

theorem universal_complementBlock_weight_differentiable (p : algebra A) (hp : IsStarProjection p)
    (hpc : ∀ a : algebra A, p*a=a*p) (δ : A →L[ℂ] A) :
    Differentiable ℂ (fun z : ℂ =>
      centralBlockCLM p hp hpc (lift (NormedSpace.exp (z • δ) : A →L[ℂ] A)) 1) := by
  change Differentiable ℂ (fun z : ℂ =>
    OAI.BoundedHochschild.CentralCorner.compressMap p hp hpc
      (lift (NormedSpace.exp (z • δ) : A →L[ℂ] A) p))
  exact (OAI.BoundedHochschild.CentralCorner.compressMap p hp hpc).differentiable.comp
    (differentiable_lift_exp_apply δ p)

end ActualUniversalModel
end SpectralIsometry.FiniteQuotientAssembly

