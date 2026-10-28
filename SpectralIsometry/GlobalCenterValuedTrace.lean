module

public import SpectralIsometry.CenterTracePieces
public import SpectralIsometry.CenterTraceGluing
public import SpectralIsometry.CenterTraceNormality

/-!
# Global Center Valued Trace

Supporting results for spectral isometries of complex unital C*-algebras.
-/

 

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace SpectralIsometry.GlobalCenterValuedTrace

open OAI.BoundedHochschild OAI.BoundedHochschild.KadisonRingrose
open OAI.HochschildCorners OAI.HochschildNormalPart
open CenterTracePieces
open scoped ComplexOrder

universe u
variable {M X : Type u} [CStarAlgebra M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

local instance orderedM : PartialOrder M := CStarAlgebra.spectralOrder M
local instance starOrderedM : StarOrderedRing M := CStarAlgebra.spectralOrderedRing M

structure FaithfulNormalCenterTrace (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    extends NormalCentralAverage e where
  fixes_center : ∀ z : M, (∀ a : M,z*a=a*z) → map z=z
  center_module : ∀ z : M, (∀ a : M,z*a=a*z) → ∀ a : M,map (z*a)=z*map a
  contractive : ∀ a : M, ‖map a‖≤‖a‖

theorem exists_faithful_normal_center_trace (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (hf : FiniteAlgebra M) : Nonempty (FaithfulNormalCenterTrace e) := by
  classical
  obtain ⟨D⟩ := exists_maximal_central_partition e (HasCentralFaithfulNormalState e)
  have hD0 : D.complement=0 := by
    by_contra hn
    obtain ⟨p,hp,hpc,hple,hp0,hstate⟩ := exists_central_normal_state_subprojection e
      D.complement_isProjection D.complement_central hn
    exact hp0 (D.maximal p hp hpc hple hstate)
  have htotal (a : M) (ha : ∀ i,D.projection i*a=0) : a=0 :=
    D.total a (by rw [hD0,zero_mul]) ha
  let t : ∀ i : D.Index, TracePiece e (D.projection i) (D.isProjection i) :=
    fun i => Classical.choice (exists_tracePiece e hf (D.projection i)
      (D.isProjection i) (D.central i) (D.property i))
  let g : D.Index → M →L[ℂ] M := fun i =>
    average e (D.projection i) (D.isProjection i) (D.central i) (t i)
  have hleft (i : D.Index) (a : M) : D.projection i*g i a=g i a :=
    average_left e _ _ _ _ a
  have hright (i : D.Index) (a : M) : g i a*D.projection i=g i a :=
    average_right e _ _ _ _ a
  have hbound (i : D.Index) (a : M) : ‖g i a‖≤‖a‖ :=
    average_norm e _ _ _ _ a
  have hpos (i : D.Index) (a : M) (ha : 0≤a) : 0≤g i a :=
    average_positive e _ _ _ _ a ha
  obtain ⟨E,hEnorm,hpiece,hEpos⟩ := CenterTraceGluing.exists_positive_gluing e
    D.projection D.isProjection D.orthogonal htotal g hleft hright hbound hpos
  have hEcentral (a b : M) : E a*b=b*E a := by
    apply sub_eq_zero.mp
    apply htotal
    intro i
    calc
      D.projection i*(E a*b-b*E a) = g i a*b-b*g i a := by
        rw [mul_sub,←mul_assoc,hpiece,←mul_assoc,D.central i b,mul_assoc,hpiece]
      _ = 0 := by rw [show g i a*b=b*g i a from average_central e _ _ _ _ a b,sub_self]
  have hE1 : E 1=1 := by
    apply sub_eq_zero.mp
    apply htotal
    intro i
    rw [mul_sub,hpiece,show g i 1=D.projection i from average_one e _ _ _ _,mul_one,sub_self]
  have hEtr (a b : M) : E (a*b)=E (b*a) := by
    apply sub_eq_zero.mp
    apply htotal
    intro i
    rw [mul_sub,hpiece,hpiece,
      show g i (a*b)=g i (b*a) from average_tracial e _ _ _ _ a b,sub_self]
  have hEmodule (z : M) (hz : ∀ b : M,z*b=b*z) (a : M) : E (z*a)=z*E a := by
    apply sub_eq_zero.mp
    apply htotal
    intro i
    calc
      D.projection i*(E (z*a)-z*E a)=g i (z*a)-z*g i a := by
        rw [mul_sub,hpiece,←mul_assoc,D.central i z,mul_assoc,hpiece]
      _=0 := by
        rw [show g i (z*a)=z*g i a from average_center_module e _ _ _ _ z hz a,sub_self]
  let φ : D.Index → M →ₚ[ℂ] ℂ := fun i =>
    scalar e (D.projection i) (D.isProjection i) (D.central i) (t i)
  have hφnormal (i : D.Index) : positiveFunctionalCLM (φ i) ∈ normalDual e :=
    (mem_normalDual e _).mpr (scalar_normal e _ _ _ _)
  have hφE (i : D.Index) (a : M) : φ i (E a)=φ i a := by
    have heq : CentralCorner.compressMap (D.projection i) (D.isProjection i) (D.central i) (E a)=
        CentralCorner.compressMap (D.projection i) (D.isProjection i) (D.central i) (g i a) := by
      apply Subtype.ext
      change D.projection i*E a=D.projection i*g i a
      rw [hpiece,hleft]
    change (t i).trace (CentralCorner.compressMap (D.projection i)
      (D.isProjection i) (D.central i) (E a))=φ i a
    rw [heq]
    exact scalar_average e _ _ _ _ a
  have hsep (a : M) (ha : ∀ i,φ i (star a*a)=0) : a=0 := by
    apply htotal
    intro i
    exact scalar_faithful_piece e _ _ _ _ a (ha i)
  have hEnormal : HasPreadjoint e E := CenterTraceNormality.normal_of_central_pairings
    e E hEcentral (fun i => positiveFunctionalCLM (φ i)) hφnormal
    (fun i z hz a => by
      change φ i (z*E a)=φ i (z*a)
      rw [←hEmodule z hz a,hφE])
    (fun a _ ha => hsep a ha)
  refine ⟨{ map := E
            normal := hEnormal
            positive := hEpos
            unital := hE1
            central := hEcentral
            tracial := hEtr
            faithful := ?_
            fixes_center := ?_
            center_module := hEmodule
            contractive := hEnorm }⟩
  · intro a ha
    apply hsep
    intro i
    rw [←hφE i (star a*a),ha,map_zero]
  · intro z hz
    simpa only [mul_one,hE1] using hEmodule z hz 1

end SpectralIsometry.GlobalCenterValuedTrace

