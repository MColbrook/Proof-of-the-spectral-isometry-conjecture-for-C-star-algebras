module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Algebra.Star.Subalgebra
public import Mathlib.Topology.Algebra.StarSubalgebra
public import Mathlib.Topology.Algebra.Group.Basic

/-!
# Bicommutant

Supporting results for spectral isometries of complex unital C*-algebras.
-/

 

@[expose] public section
noncomputable section

open scoped Pointwise

namespace SpectralIsometry

variable {A : Type*} [CStarAlgebra A]

def relativeBicommutant (h : selfAdjoint A) : StarSubalgebra ℂ A :=
  StarSubalgebra.centralizer ℂ (StarSubalgebra.centralizer ℂ ({(h : A)} : Set A) : Set A)

theorem relativeBicommutant_coe (h : selfAdjoint A) :
    (relativeBicommutant h : Set A) = ({(h : A)} : Set A).centralizer.centralizer := by
  rw [relativeBicommutant, StarSubalgebra.coe_centralizer_centralizer]
  simp only [Set.star_singleton, h.property.star_eq, Set.union_self]

theorem mem_relativeBicommutant_iff (h : selfAdjoint A) (a : A) :
    a ∈ relativeBicommutant h ↔
      ∀ x : A, (h : A) * x = x * (h : A) → x * a = a * x := by
  rw [← SetLike.mem_coe, relativeBicommutant_coe]
  simp only [Set.mem_centralizer_iff, Set.mem_singleton_iff, forall_eq]

theorem self_mem_relativeBicommutant (h : selfAdjoint A) : (h : A) ∈ relativeBicommutant h :=
  (mem_relativeBicommutant_iff h h).mpr (fun _ hx => hx.symm)

theorem relativeBicommutant_isClosed (h : selfAdjoint A) :
    IsClosed (relativeBicommutant h : Set A) := by
  rw [relativeBicommutant_coe]
  exact Set.isClosed_centralizer _

theorem relativeBicommutant_mul_comm (h : selfAdjoint A) (a b : relativeBicommutant h) :
    a * b = b * a := by
  apply Subtype.ext
  change (a : A) * (b : A) = (b : A) * (a : A)
  have hb : (h : A) * (b : A) = (b : A) * (h : A) :=
    (mem_relativeBicommutant_iff h b).mp b.property h rfl
  exact ((mem_relativeBicommutant_iff h a).mp a.property b hb).symm

/-- The actual relative bicommutant has its inherited commutative C*-algebra
structure, even though the ambient algebra need not be commutative. -/
noncomputable instance relativeBicommutant_commCStarAlgebra (h : selfAdjoint A) :
    CommCStarAlgebra (relativeBicommutant h) := by
  letI : IsClosed (relativeBicommutant h : Set A) := relativeBicommutant_isClosed h
  letI : CStarAlgebra (relativeBicommutant h) := StarSubalgebra.cstarAlgebra (relativeBicommutant h)
  exact { (inferInstance : CStarAlgebra (relativeBicommutant h)) with
    mul_comm := relativeBicommutant_mul_comm h }

end SpectralIsometry

