module

public import SpectralIsometry.FiniteBidualDecomposition
public import OAI.Analysis.TracialCohomology.CenterTrace

/-!
# Center Trace Pieces

Supporting results for spectral isometries of complex unital C*-algebras.
-/

 

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace SpectralIsometry.CenterTracePieces

open OAI.BoundedHochschild OAI.BoundedHochschild.KadisonRingrose
open OAI.HochschildCorners OAI.HochschildNormalPart OAI.HochschildSakai
open scoped ComplexOrder

universe u
variable {M X : Type u} [CStarAlgebra M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

local instance orderedM : PartialOrder M := CStarAlgebra.spectralOrder M
local instance starOrderedM : StarOrderedRing M := CStarAlgebra.spectralOrderedRing M

structure TracePiece (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (p : M) (hp : IsStarProjection p) where
  trace : Corner p hp →ₚ[ℂ] ℂ
  normal : TraceInPredual (cornerPredualEquiv p hp e) trace
  one : trace 1=1
  tracial : ∀ a b, trace (a*b)=trace (b*a)
  faithful : ∀ a, trace (star a*a)=0 → a=0

theorem exists_tracePiece (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (hf : FiniteAlgebra M) (p : M) (hp : IsStarProjection p)
    (hc : ∀ a, p*a=a*p) (hs : HasCentralFaithfulNormalState e p) :
    Nonempty (TracePiece e p hp) := by
  obtain ⟨ψ,hψ,hψ1,hfaith⟩ := central_faithful_state_on_corner e hp hc hs
  have hfin : FiniteAlgebra (Corner p hp) :=
    (finiteCorner_iff p hp).mp (finiteCorner_of_finiteAlgebra hf p hp)
  obtain ⟨τ,hτ,h1,htr,hτf⟩ := faithful_normal_trace_of_center_state
    (cornerPredualEquiv p hp e) hfin ψ hψ hψ1 hfaith
  exact ⟨⟨τ,hτ,h1,htr,hτf⟩⟩

variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
  (p : M) (hp : IsStarProjection p) (hc : ∀ a : M, p*a=a*p)
  (t : TracePiece e p hp)

def average : M →L[ℂ] M := (CentralCorner.includeMap p hp).comp
  ((OAI.PopaCenter.expectation (cornerPredualEquiv p hp e) t.trace t.normal
    t.tracial t.faithful t.one).comp (CentralCorner.compressMap p hp hc))

theorem average_coe (a : M) : average e p hp hc t a=
    (OAI.PopaCenter.average (cornerPredualEquiv p hp e) t.trace t.normal
      t.tracial t.faithful (CentralCorner.compressMap p hp hc a) : Corner p hp) := rfl

theorem average_left (a : M) : p*average e p hp hc t a=average e p hp hc t a :=
  (OAI.PopaCenter.average (cornerPredualEquiv p hp e) t.trace t.normal
    t.tracial t.faithful (CentralCorner.compressMap p hp hc a)).property.1

theorem average_right (a : M) : average e p hp hc t a*p=average e p hp hc t a :=
  (OAI.PopaCenter.average (cornerPredualEquiv p hp e) t.trace t.normal
    t.tracial t.faithful (CentralCorner.compressMap p hp hc a)).property.2

theorem average_norm (a : M) : ‖average e p hp hc t a‖≤‖a‖ :=
  (OAI.PopaCenter.average_norm (cornerPredualEquiv p hp e) t.trace t.normal
    t.tracial t.faithful _).trans (CentralCorner.compressMap_norm p hp hc a)

theorem average_central (a b : M) : average e p hp hc t a*b=b*average e p hp hc t a :=
  centralCorner_central hp hc _ (fun c =>
    (OAI.PopaCenter.average_central (cornerPredualEquiv p hp e) t.trace t.normal
      t.tracial t.faithful _ c).eq) b

theorem average_one : average e p hp hc t 1=p := by
  have hcomp : CentralCorner.compressMap p hp hc 1=1 := Subtype.ext (mul_one p)
  rw [average_coe,hcomp,OAI.PopaCenter.average_id (cornerPredualEquiv p hp e)
    t.trace t.normal t.tracial t.faithful t.one (fun a => Commute.one_left a)]
  rfl

theorem average_tracial (a b : M) : average e p hp hc t (a*b)=average e p hp hc t (b*a) := by
  rw [average_coe,average_coe,CentralCorner.compressMap_mul,
    CentralCorner.compressMap_mul,OAI.PopaCenter.average_trace
      (cornerPredualEquiv p hp e) t.trace t.normal t.tracial t.faithful t.one]

theorem average_positive (a : M) (ha : 0≤a) : 0≤average e p hp hc t a := by
  have hs (b : M) : CentralCorner.compressMap p hp hc (star b)=
      star (CentralCorner.compressMap p hp hc b) := by
    apply Subtype.ext
    change p*star b=star (p*b)
    rw [star_mul,hp.isSelfAdjoint.star_eq,hc]
  have hpos : 0≤CentralCorner.compressMap p hp hc a := by
    obtain ⟨b,rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp ha
    rw [CentralCorner.compressMap_mul,hs]
    exact star_mul_self_nonneg _
  exact OAI.PopaCenter.average_nonneg (cornerPredualEquiv p hp e) t.trace
    t.normal t.tracial t.faithful hpos

theorem compress_central (z : M) (hz : ∀ b : M,z*b=b*z) :
    OAI.PopaCenter.Central (CentralCorner.compressMap p hp hc z) := by
  intro a
  change CentralCorner.compressMap p hp hc z*a=a*CentralCorner.compressMap p hp hc z
  have h := congrArg (CentralCorner.compressMap p hp hc) (hz (a:M))
  have ha : CentralCorner.compressMap p hp hc (a:M)=a := Subtype.ext a.property.1
  simpa only [CentralCorner.compressMap_mul,ha] using h

theorem average_center_module (z : M) (hz : ∀ b : M,z*b=b*z) (a : M) :
    average e p hp hc t (z*a)=z*average e p hp hc t a := by
  rw [average_coe,CentralCorner.compressMap_mul,
    OAI.PopaCenter.average_bimodule (cornerPredualEquiv p hp e) t.trace t.normal
      t.tracial t.faithful t.one (compress_central p hp hc z hz)]
  change (p*z)*average e p hp hc t a=z*average e p hp hc t a
  rw [hc,mul_assoc,average_left]

def scalar : M →ₚ[ℂ] ℂ where
  toLinearMap := t.trace.toLinearMap.comp (CentralCorner.compressMap p hp hc).toLinearMap
  monotone' := by
    apply (monotone_iff_map_nonneg
      (t.trace.toLinearMap.comp (CentralCorner.compressMap p hp hc).toLinearMap)).mpr
    intro a ha
    have hs (b : M) : CentralCorner.compressMap p hp hc (star b)=
        star (CentralCorner.compressMap p hp hc b) := by
      apply Subtype.ext
      change p*star b=star (p*b)
      rw [star_mul,hp.isSelfAdjoint.star_eq,hc]
    obtain ⟨b,rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp ha
    change 0≤t.trace (CentralCorner.compressMap p hp hc (star b*b))
    rw [CentralCorner.compressMap_mul,hs]
    exact t.trace.map_nonneg (star_mul_self_nonneg _)

theorem scalar_normal : TraceInPredual e (scalar e p hp hc t) := by
  obtain ⟨w,hw⟩ := t.normal
  obtain ⟨z,rfl⟩ := Submodule.Quotient.mk_surjective _ w
  obtain ⟨z',hz'⟩ := mul_hasPreadjoint e p z
  refine ⟨z',fun a => ?_⟩
  change t.trace (CentralCorner.compressMap p hp hc a)=_
  rw [hw,cornerPredualEquiv_symm_mk]
  exact congrArg star (hz' a)

theorem scalar_average (a : M) :
    scalar e p hp hc t (average e p hp hc t a)=scalar e p hp hc t a := by
  change t.trace (CentralCorner.compressMap p hp hc
    (CentralCorner.includeMap p hp
      (OAI.PopaCenter.average (cornerPredualEquiv p hp e) t.trace t.normal
        t.tracial t.faithful (CentralCorner.compressMap p hp hc a))))=_
  rw [CentralCorner.compressMap_includeMap,OAI.PopaCenter.trace_average
    (cornerPredualEquiv p hp e) t.trace t.normal t.tracial t.faithful t.one]
  rfl

theorem scalar_faithful_piece (a : M) (ha : scalar e p hp hc t (star a*a)=0) : p*a=0 := by
  have hs : CentralCorner.compressMap p hp hc (star a)=
      star (CentralCorner.compressMap p hp hc a) := by
    apply Subtype.ext
    change p*star a=star (p*a)
    rw [star_mul,hp.isSelfAdjoint.star_eq,hc]
  have hzero : CentralCorner.compressMap p hp hc a=0 := by
    apply t.faithful
    change t.trace (CentralCorner.compressMap p hp hc (star a*a))=0 at ha
    rwa [CentralCorner.compressMap_mul,hs] at ha
  exact congrArg (fun c : Corner p hp => (c:M)) hzero

end SpectralIsometry.CenterTracePieces

