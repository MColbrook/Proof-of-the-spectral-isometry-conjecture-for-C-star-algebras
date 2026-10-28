module

public import OAI.Analysis.BoundedHochschild.Corners
public import SpectralIsometry.SquareZeroTrace
import Mathlib.Tactic.NoncommRing

/-!
# Square Zero Corner Span

Supporting results for spectral isometries of complex unital C*-algebras.
-/

 

@[expose] public section
set_option autoImplicit false
noncomputable section

open scoped ComplexOrder CStarAlgebra
open OAI.HochschildCorners

namespace SpectralIsometry.SquareZeroPreserver

variable {M X : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

def supportedSquareZero (p : M) : Set M :=
  {a | a ^ 2 = 0 ∧ p * a = a ∧ a * p = a}

theorem trace_on_corner_of_zero_on_squareZero
    (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) {p : M} (hp : IsStarProjection p)
    (F : StrongDual ℂ M) (hF : ∀ a ∈ supportedSquareZero p, F a = 0)
    {a b : M} (ha : a ∈ corner p hp) (hb : b ∈ corner p hp) :
    F (a * b) = F (b * a) := by
  let D : M →L[ℂ] M := (ContinuousLinearMap.mul ℂ M).flip b - ContinuousLinearMap.mul ℂ M b
  have hzero : F (a * b - b * a) = 0 := by
    apply OAI.HochschildCorners.dual_zero_on_corner e (F.comp D) hp ?_ ha
    intro q hq hqp
    have hqm := projection_mem_corner hp hq hqp
    have hqp0 : (p - q) * q = 0 := by rw [sub_mul, hqm.1, hq.isIdempotentElem.eq, sub_self]
    have hqq0 : q * (p - q) = 0 := by rw [mul_sub, hqm.2, hq.isIdempotentElem.eq, sub_self]
    let x := q * b * (p - q)
    let y := (p - q) * b * q
    have hx : x ∈ supportedSquareZero p := by
      refine ⟨?_, ?_, ?_⟩
      · change (q * b * (p - q)) ^ 2 = 0
        calc
          (q * b * (p - q)) ^ 2 = q * b * ((p - q) * q) * b * (p - q) := by noncomm_ring
          _ = 0 := by rw [hqp0]; simp
      · change p * (q * b * (p - q)) = q * b * (p - q)
        rw [← mul_assoc, ← mul_assoc, hqm.1]
      · change q * b * (p - q) * p = q * b * (p - q)
        calc
          q * b * (p - q) * p = q * b * ((p - q) * p) := mul_assoc _ _ _
          _ = q * b * (p - q) := by rw [sub_mul, hp.isIdempotentElem.eq, hqm.2]
    have hy : y ∈ supportedSquareZero p := by
      refine ⟨?_, ?_, ?_⟩
      · change ((p - q) * b * q) ^ 2 = 0
        calc
          ((p - q) * b * q) ^ 2 = (p - q) * b * (q * (p - q)) * b * q := by noncomm_ring
          _ = 0 := by rw [hqq0]; simp
      · change p * ((p - q) * b * q) = (p - q) * b * q
        rw [← mul_assoc, ← mul_assoc, mul_sub, hp.isIdempotentElem.eq, hqm.1]
      · change (p - q) * b * q * p = (p - q) * b * q
        rw [mul_assoc, hqm.2]
    have he : q * b - b * q = x - y := by
      calc
        q * b - b * q = q * b * p - p * b * q := by rw [mul_assoc q b p, hb.2, hb.1]
        _ = x - y := by dsimp [x, y]; noncomm_ring
    change F (q * b - b * q) = 0
    rw [he, map_sub, hF x hx, hF y hy, sub_self]
  exact sub_eq_zero.mp (by simpa only [map_sub] using hzero)

theorem dual_zero_on_corner_of_two_copies
    (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) {p : M} (hp : IsStarProjection p)
    (r s : Corner p hp) (hr : star r * r = 1) (hs : star s * s = 1)
    (hrs : star r * s = 0)
    (F : StrongDual ℂ M) (hF : ∀ a ∈ supportedSquareZero p, F a = 0)
    {a : M} (ha : a ∈ corner p hp) : F a = 0 := by
  let G : StrongDual ℂ (Corner p hp) :=
    { toFun := fun x => F (x : M)
      map_add' := fun x y => F.map_add (x : M) (y : M)
      map_smul' := fun c x => F.map_smul c (x : M)
      cont := F.continuous.comp continuous_subtype_val }
  have hG : G = 0 := bounded_trace_zero_of_two_copies (1 : Corner p hp) r s
    (fun b => ⟨one_mul b, mul_one b⟩) hr hs hrs G (fun b c =>
      trace_on_corner_of_zero_on_squareZero e hp F hF b.property c.property)
  exact congrArg (fun H : StrongDual ℂ (Corner p hp) => H ⟨a, ha⟩) hG

theorem supportedSquareZero_span_dense_in_corner
    (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) {p : M} (hp : IsStarProjection p)
    (r s : Corner p hp) (hr : star r * r = 1) (hs : star s * s = 1)
    (hrs : star r * s = 0) {a : M} (ha : a ∈ corner p hp) :
    a ∈ (Submodule.span ℂ (supportedSquareZero p)).topologicalClosure := by
  let S := (Submodule.span ℂ (supportedSquareZero p)).topologicalClosure
  let : IsClosed (S : Set M) := Submodule.isClosed_topologicalClosure _
  change a ∈ S
  apply (Submodule.Quotient.mk_eq_zero S).mp
  apply SeparatingDual.eq_zero_of_forall_dual_eq_zero (R := ℂ)
  intro F
  apply dual_zero_on_corner_of_two_copies e hp r s hr hs hrs (F.comp S.mkQL) ?_ ha
  intro b hb
  have hm : b ∈ S := Submodule.le_topologicalClosure _ (Submodule.subset_span hb)
  have hh : (Submodule.Quotient.mk (p := S) b : M ⧸ S) = 0 :=
    (Submodule.Quotient.mk_eq_zero S).mpr hm
  change F (Submodule.Quotient.mk b) = 0
  rw [hh, map_zero]

end SpectralIsometry.SquareZeroPreserver

