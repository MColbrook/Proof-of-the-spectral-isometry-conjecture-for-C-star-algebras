module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Topology.Algebra.Algebra
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Topology.Algebra.Module.Equiv.Basic
public import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Tactic.NoncommRing

/-!
# Transport Kernel

Supporting results for spectral isometries of complex unital C*-algebras.
-/

 

@[expose] public section
noncomputable section

namespace SpectralIsometry.MainTransport

section Algebraic

variable {A B : Type*} [Ring A] [Ring B] [Algebra ℂ A] [Algebra ℂ B]

def transportedInner (T : A ≃ₗ[ℂ] B) (x : A) : B →ₗ[ℂ] B where
  toFun b := T (x * T.symm b - T.symm b * x)
  map_add' a b := by
    rw [T.symm.map_add, ← T.map_add]
    congr 1
    noncomm_ring
  map_smul' c b := by
    simp only [map_smul, mul_smul_comm, smul_mul_assoc, ← smul_sub, RingHom.id_apply]

theorem transportedInner_zero_iff (T : A ≃ₗ[ℂ] B) (x : A) (b : B) :
    transportedInner T x b = 0 ↔ x * T.symm b = T.symm b * x := by
  change T (x * T.symm b - T.symm b * x) = 0 ↔ _
  rw [← T.map_zero, T.injective.eq_iff, sub_eq_zero]

/-- Exact algebraic image/common-kernel identity, for an arbitrary set of inner generators. -/
theorem image_centralizer_eq_common_kernel (T : A ≃ₗ[ℂ] B) (s : Set A) :
    T '' s.centralizer = {b : B | ∀ x ∈ s, transportedInner T x b = 0} := by
  ext b
  constructor
  · rintro ⟨a, ha, rfl⟩ x hx
    rw [transportedInner_zero_iff, T.symm_apply_apply]
    exact Set.mem_centralizer_iff.mp ha x hx
  · intro hb
    refine ⟨T.symm b, Set.mem_centralizer_iff.mpr ?_, T.apply_symm_apply b⟩
    intro x hx
    exact (transportedInner_zero_iff T x b).mp (hb x hx)

private theorem inverse_one (T : A ≃ₗ[ℂ] B) (h1 : T 1 = 1) : T.symm 1 = 1 :=
  T.injective (by rw [T.apply_symm_apply, h1])

/-- The associative image algebra, constructed without assuming T preserves products. -/
def transportedCentralizerAlgebra (T : A ≃ₗ[ℂ] B) (h1 : T 1 = 1) (s : Set A)
    (hder : ∀ x ∈ s, ∀ a b : B,
      transportedInner T x (a * b) = transportedInner T x a * b + a * transportedInner T x b) :
    Subalgebra ℂ B where
  carrier := {b | T.symm b ∈ Subalgebra.centralizer ℂ s}
  zero_mem' := by rw [Set.mem_ofPred_eq, map_zero]; exact (Subalgebra.centralizer ℂ s).zero_mem
  one_mem' := by
    rw [Set.mem_ofPred_eq, inverse_one T h1]
    exact (Subalgebra.centralizer ℂ s).one_mem
  add_mem' := by
    intro a b ha hb
    change T.symm (a + b) ∈ Subalgebra.centralizer ℂ s
    rw [map_add]
    exact (Subalgebra.centralizer ℂ s).add_mem ha hb
  mul_mem' := by
    intro a b ha hb
    change T.symm (a * b) ∈ Subalgebra.centralizer ℂ s
    change ∀ x ∈ s, x * T.symm (a * b) = T.symm (a * b) * x
    intro x hx
    have hxa : transportedInner T x a = 0 :=
      (transportedInner_zero_iff T x a).mpr (Set.mem_centralizer_iff.mp ha x hx)
    have hxb : transportedInner T x b = 0 :=
      (transportedInner_zero_iff T x b).mpr (Set.mem_centralizer_iff.mp hb x hx)
    apply (transportedInner_zero_iff T x (a * b)).mp
    rw [hder x hx, hxa, hxb, zero_mul, mul_zero, add_zero]
  algebraMap_mem' c := by
    change T.symm (algebraMap ℂ B c) ∈ Subalgebra.centralizer ℂ s
    rw [Algebra.algebraMap_eq_smul_one, map_smul, inverse_one T h1,
      ← Algebra.algebraMap_eq_smul_one]
    exact (Subalgebra.centralizer ℂ s).algebraMap_mem c

theorem transportedCentralizerAlgebra_coe (T : A ≃ₗ[ℂ] B) (h1 : T 1 = 1) (s : Set A)
    (hder : ∀ x ∈ s, ∀ a b : B,
      transportedInner T x (a * b) = transportedInner T x a * b + a * transportedInner T x b) :
    (transportedCentralizerAlgebra T h1 s hder : Set B) = T '' s.centralizer := by
  ext b
  constructor
  · intro hb
    exact ⟨T.symm b, hb, T.apply_symm_apply b⟩
  · rintro ⟨a, ha, rfl⟩
    change T.symm (T a) ∈ Subalgebra.centralizer ℂ s
    rw [T.symm_apply_apply]
    exact ha

end Algebraic

section Topological

variable {A B : Type*} [NormedRing A] [NormedRing B]
  [NormedAlgebra ℂ A] [NormedAlgebra ℂ B]

theorem continuous_equiv_image_centralizer_isClosed (T : A ≃L[ℂ] B) (s : Set A) :
    IsClosed (T '' s.centralizer) :=
  T.toHomeomorph.isClosedMap _ (Set.isClosed_centralizer s)

theorem transportedCentralizerAlgebra_isClosed (T : A ≃L[ℂ] B) (h1 : T 1 = 1) (s : Set A)
    (hder : ∀ x ∈ s, ∀ a b : B,
      transportedInner T.toLinearEquiv x (a * b) =
        transportedInner T.toLinearEquiv x a * b + a * transportedInner T.toLinearEquiv x b) :
    IsClosed (transportedCentralizerAlgebra T.toLinearEquiv h1 s hder : Set B) := by
  rw [transportedCentralizerAlgebra_coe]
  exact continuous_equiv_image_centralizer_isClosed T s

end Topological

end SpectralIsometry.MainTransport

