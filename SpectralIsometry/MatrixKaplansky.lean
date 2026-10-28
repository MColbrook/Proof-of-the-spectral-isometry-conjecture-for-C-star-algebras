module

public import OAI.Analysis.Commutator.KaplanskyDensity
public import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

/-!
# Matrix Kaplansky

Supporting results for spectral isometries of complex unital C*-algebras.
-/

@[expose] public section
noncomputable section

open scoped BigOperators InnerProductSpace
open OAI.Kadison.OperatorAmplification OAI.Kadison.CyclicColumns

namespace SpectralIsometry.MatrixKaplansky

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

-- Use one finite-index dictionary consistently with the reused representation.
local instance : DecidableEq (Fin 2) := Classical.decEq _

abbrev Double := SumSpace (H := H) (Fin 2)

def offDiagonal (T : H →L[ℂ] H) : Double (H := H) →L[ℂ] Double (H := H) :=
  matrixAction (fun i j : Fin 2 =>
    if i = 0 ∧ j = 1 then T else if i = 1 ∧ j = 0 then star T else 0)

@[simp] theorem offDiagonal_apply_zero (T : H →L[ℂ] H) (x : Double (H := H)) :
    offDiagonal T x 0 = T (x 1) := by
  simp [offDiagonal, Fin.sum_univ_two]

@[simp] theorem offDiagonal_apply_one (T : H →L[ℂ] H) (x : Double (H := H)) :
    offDiagonal T x 1 = star T (x 0) := by
  simp [offDiagonal, Fin.sum_univ_two]

theorem offDiagonal_selfAdjoint (T : H →L[ℂ] H) : IsSelfAdjoint (offDiagonal T) := by
  change star (offDiagonal T) = offDiagonal T
  rw [ContinuousLinearMap.star_eq_adjoint]
  symm
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro x y
  simp only [PiLp.inner_apply, Fin.sum_univ_two, offDiagonal_apply_zero,
    offDiagonal_apply_one, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.adjoint_inner_right]
  exact add_comm _ _

theorem offDiagonal_norm_le_one (T : H →L[ℂ] H) (hT : ‖T‖ ≤ 1) :
    ‖offDiagonal T‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  have h₁ : ‖T (x 1)‖ ≤ ‖x 1‖ := by
    simpa using (T.le_opNorm (x 1)).trans
      (mul_le_mul_of_nonneg_right hT (norm_nonneg (x 1)))
  have h₀ : ‖star T (x 0)‖ ≤ ‖x 0‖ := by
    have hs : ‖star T‖ ≤ 1 := by simpa using hT
    simpa using ((star T).le_opNorm (x 0)).trans
      (mul_le_mul_of_nonneg_right hs (norm_nonneg (x 0)))
  have hsq₁ := (sq_le_sq₀ (norm_nonneg (T (x 1))) (norm_nonneg (x 1))).mpr h₁
  have hsq₀ := (sq_le_sq₀ (norm_nonneg (star T (x 0))) (norm_nonneg (x 0))).mpr h₀
  have hx := PiLp.norm_sq_eq_of_L2 _ (offDiagonal T x)
  have hy := PiLp.norm_sq_eq_of_L2 _ x
  simp only [Fin.sum_univ_two, offDiagonal_apply_zero, offDiagonal_apply_one] at hx hy
  nlinarith [norm_nonneg (offDiagonal T x), norm_nonneg x,
    norm_nonneg (T (x 1)), norm_nonneg (star T (x 0)), norm_nonneg (x 0),
    norm_nonneg (x 1)]

theorem single_norm (i : Fin 2) (x : H) : ‖single (H := H) (Fin 2) i x‖ = ‖x‖ := by
  have he : single (H := H) (Fin 2) i x = PiLp.single 2 i x := by
    ext j
    simp [PiLp.single_apply]
  rw [he, PiLp.norm_single]

theorem entry_norm_le (T : Double (H := H) →L[ℂ] Double (H := H)) (i j : Fin 2) :
    ‖entry (Fin 2) T i j‖ ≤ ‖T‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg T)
  intro x
  calc
    ‖entry (Fin 2) T i j x‖ ≤ ‖T (single (Fin 2) j x)‖ := PiLp.norm_apply_le _ i
    _ ≤ ‖T‖ * ‖single (Fin 2) j x‖ := T.le_opNorm _
    _ = ‖T‖ * ‖x‖ := by rw [single_norm]

section Amplification

variable (S : StarSubalgebra ℂ (H →L[ℂ] H)) [IsClosed (S : Set (H →L[ℂ] H))]

def representation : CStarMatrix (Fin 2) (Fin 2) S →⋆ₐ[ℂ]
    (Double (H := H) →L[ℂ] Double (H := H)) :=
  matrixRepresentation (ι := Fin 2) S.subtype

@[simp] theorem entry_representation (X : CStarMatrix (Fin 2) (Fin 2) S) (i j : Fin 2) :
    entry (Fin 2) (representation S X) i j = (X i j : H →L[ℂ] H) := by
  ext x
  fin_cases i <;> fin_cases j <;>
    simp [representation, matrixRepresentation, matrixAction_apply, Fin.sum_univ_two]

theorem representation_injective : Function.Injective (representation S) := by
  intro X Y h
  ext i j : 2
  have he := congrArg (fun T => entry (Fin 2) T i j) h
  simpa only [entry_representation] using he

theorem representation_isometry : Isometry (representation S) :=
  NonUnitalStarAlgHom.isometry (representation S) (representation_injective S)

def amplified : StarSubalgebra ℂ (Double (H := H) →L[ℂ] Double (H := H)) :=
  (representation S).range

theorem amplified_isClosed : IsClosed (amplified S : Set (Double (H := H) →L[ℂ] Double (H := H))) := by
  exact (representation_isometry S).isClosedEmbedding.isClosed_range

theorem entry_mem_of_mem_amplified {T : Double (H := H) →L[ℂ] Double (H := H)}
    (hT : T ∈ amplified S) (i j : Fin 2) : entry (Fin 2) T i j ∈ S := by
  obtain ⟨X, rfl⟩ := hT
  change entry (Fin 2) (representation S X) i j ∈ S
  rw [entry_representation]
  exact (X i j).property

def matrixUnit (i j : Fin 2) : Double (H := H) →L[ℂ] Double (H := H) :=
  representation S (fun p q => if p = i ∧ q = j then 1 else 0)

theorem matrixUnit_mem (i j : Fin 2) : matrixUnit S i j ∈ amplified S :=
  ⟨_, rfl⟩

@[simp] theorem matrixUnit_apply (i j k : Fin 2) (x : Double (H := H)) :
    matrixUnit S i j x k = if k = i then x j else 0 := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    simp [matrixUnit, representation, matrixRepresentation,
      matrixAction_apply, Fin.sum_univ_two, one_apply_eq_self]

theorem matrixUnit_apply_eq_single (i j : Fin 2) (x : Double (H := H)) :
    matrixUnit S i j x = single (Fin 2) i (x j) := by
  ext k
  simp only [matrixUnit_apply, single_apply]

theorem diagonal_mem_amplified (a : S) :
    diagonal (H := H) (Fin 2) (a : H →L[ℂ] H) ∈ amplified S := by
  refine ⟨(fun i j => if i = j then a else 0), ?_⟩
  ext x i
  fin_cases i <;> simp [representation, matrixRepresentation,
    matrixAction_apply, Fin.sum_univ_two]

theorem centralizer_eq_diagonal {R : Double (H := H) →L[ℂ] Double (H := H)}
    (hR : R ∈ Set.centralizer (amplified S : Set (Double (H := H) →L[ℂ] Double (H := H)))) :
    R = diagonal (H := H) (Fin 2) (entry (Fin 2) R 0 0) := by
  have h₀ (x : Double (H := H)) : R x 0 = entry (Fin 2) R 0 0 (x 0) := by
    have he := congrArg (fun Q : Double (H := H) →L[ℂ] Double (H := H) => Q x 0)
      (hR (matrixUnit S 0 0) (matrixUnit_mem S 0 0))
    simpa [mul_apply_eq_comp, matrixUnit_apply_eq_single, single_apply, entry_apply] using he
  have h₁ (x : Double (H := H)) : R x 1 = entry (Fin 2) R 1 1 (x 1) := by
    have he := congrArg (fun Q : Double (H := H) →L[ℂ] Double (H := H) => Q x 1)
      (hR (matrixUnit S 1 1) (matrixUnit_mem S 1 1))
    simpa [mul_apply_eq_comp, matrixUnit_apply_eq_single, single_apply, entry_apply] using he
  have hd : entry (Fin 2) R 1 1 = entry (Fin 2) R 0 0 := by
    ext v
    have he := congrArg (fun Q : Double (H := H) →L[ℂ] Double (H := H) => Q (single (Fin 2) 1 v) 0)
      (hR (matrixUnit S 0 1) (matrixUnit_mem S 0 1))
    simpa [mul_apply_eq_comp, matrixUnit_apply_eq_single, single_apply, entry_apply] using he
  ext x i
  fin_cases i
  · simpa [diagonal_apply] using h₀ x
  · simpa [diagonal_apply, hd] using h₁ x

theorem centralizer_entry_mem {R : Double (H := H) →L[ℂ] Double (H := H)}
    (hR : R ∈ Set.centralizer (amplified S : Set (Double (H := H) →L[ℂ] Double (H := H)))) :
    entry (Fin 2) R 0 0 ∈ Set.centralizer (S : Set (H →L[ℂ] H)) := by
  intro a ha
  exact entry_commutes (Fin 2) R a
    (hR (diagonal (H := H) (Fin 2) a) (diagonal_mem_amplified S ⟨a, ha⟩)) 0 0

theorem offDiagonal_mem_bicommutant {T : H →L[ℂ] H}
    (hT : T ∈ Set.centralizer (Set.centralizer (S : Set (H →L[ℂ] H)))) :
    offDiagonal T ∈ Set.centralizer (Set.centralizer
      (amplified S : Set (Double (H := H) →L[ℂ] Double (H := H)))) := by
  intro R hR
  let r := entry (Fin 2) R 0 0
  have hr : r ∈ Set.centralizer (S : Set (H →L[ℂ] H)) := centralizer_entry_mem S hR
  have hrs : star r ∈ Set.centralizer (S : Set (H →L[ℂ] H)) := by
    intro a ha
    have he := congrArg star (hr (star a) (star_mem ha))
    simpa only [star_mul, star_star] using he.symm
  have hc : r * T = T * r := hT r hr
  have hcs : r * star T = star T * r := by
    have he := congrArg star (hT (star r) hrs)
    simpa only [star_mul, star_star] using he.symm
  rw [centralizer_eq_diagonal S hR]
  ext x i
  fin_cases i
  · simpa [mul_apply_eq_comp, diagonal_apply, offDiagonal_apply_zero, r] using
      congrArg (fun Q : H →L[ℂ] H => Q (x 1)) hc
  · simpa [mul_apply_eq_comp, diagonal_apply, offDiagonal_apply_one, r] using
      congrArg (fun Q : H →L[ℂ] H => Q (x 0)) hcs

theorem contraction_finite_approx (ι : Type*) [Fintype ι] [DecidableEq ι]
    {T : H →L[ℂ] H}
    (hT : T ∈ Set.centralizer (Set.centralizer (S : Set (H →L[ℂ] H))))
    (hnT : ‖T‖ ≤ 1) (x : ι → H) (ε : ℝ) (hε : 0 < ε) :
    ∃ a : H →L[ℂ] H, a ∈ S ∧ ‖a‖ ≤ 1 ∧ ∀ i, ‖a (x i) - T (x i)‖ < ε := by
  obtain ⟨B, hB, hsB, hnB, happ⟩ :=
    OAI.Kadison.Kaplansky.selfAdjoint_contraction_finite_approx ι (amplified S)
      (amplified_isClosed S) (offDiagonal_mem_bicommutant S hT)
      (offDiagonal_selfAdjoint T) (offDiagonal_norm_le_one T hnT)
      (fun i => single (Fin 2) 1 (x i)) ε hε
  refine ⟨entry (Fin 2) B 0 1, entry_mem_of_mem_amplified S hB 0 1,
    (entry_norm_le B 0 1).trans hnB, ?_⟩
  intro i
  calc
    ‖entry (Fin 2) B 0 1 (x i) - T (x i)‖ =
        ‖(B (single (Fin 2) 1 (x i)) - offDiagonal T (single (Fin 2) 1 (x i))) 0‖ := by
          simp [PiLp.sub_apply, offDiagonal_apply_zero, single_apply, entry_apply]
    _ ≤ ‖B (single (Fin 2) 1 (x i)) - offDiagonal T (single (Fin 2) 1 (x i))‖ :=
      PiLp.norm_apply_le _ 0
    _ < ε := happ i

theorem entry_star_of_mem_amplified {B : Double (H := H) →L[ℂ] Double (H := H)}
    (hB : B ∈ amplified S) (i j : Fin 2) :
    entry (Fin 2) (star B) i j = star (entry (Fin 2) B j i) := by
  obtain ⟨X, rfl⟩ := hB
  change entry (Fin 2) (star (representation S X)) i j =
    star (entry (Fin 2) (representation S X) j i)
  rw [← map_star (representation S) X, entry_representation, entry_representation]
  rfl

theorem contraction_strongStar_finite_approx (ι : Type*) [Fintype ι] [DecidableEq ι]
    {T : H →L[ℂ] H}
    (hT : T ∈ Set.centralizer (Set.centralizer (S : Set (H →L[ℂ] H))))
    (hnT : ‖T‖ ≤ 1) (x : ι → H) (ε : ℝ) (hε : 0 < ε) :
    ∃ a : H →L[ℂ] H, a ∈ S ∧ ‖a‖ ≤ 1 ∧
      ∀ i, ‖a (x i) - T (x i)‖ < ε ∧ ‖star a (x i) - star T (x i)‖ < ε := by
  let v : ι ⊕ ι → Double (H := H) :=
    Sum.elim (fun i => single (Fin 2) 1 (x i)) (fun i => single (Fin 2) 0 (x i))
  obtain ⟨B, hB, hsB, hnB, happ⟩ :=
    OAI.Kadison.Kaplansky.selfAdjoint_contraction_finite_approx (ι ⊕ ι) (amplified S)
      (amplified_isClosed S) (offDiagonal_mem_bicommutant S hT)
      (offDiagonal_selfAdjoint T) (offDiagonal_norm_le_one T hnT) v ε hε
  have hstar : star (entry (Fin 2) B 0 1) = entry (Fin 2) B 1 0 := by
    have he := entry_star_of_mem_amplified S hB 1 0
    rw [hsB.star_eq] at he
    exact he.symm
  refine ⟨entry (Fin 2) B 0 1, entry_mem_of_mem_amplified S hB 0 1,
    (entry_norm_le B 0 1).trans hnB, ?_⟩
  intro i
  constructor
  · calc
      ‖entry (Fin 2) B 0 1 (x i) - T (x i)‖ =
          ‖(B (v (Sum.inl i)) - offDiagonal T (v (Sum.inl i))) 0‖ := by
            simp [v, PiLp.sub_apply, offDiagonal_apply_zero, single_apply, entry_apply]
      _ ≤ ‖B (v (Sum.inl i)) - offDiagonal T (v (Sum.inl i))‖ := PiLp.norm_apply_le _ 0
      _ < ε := happ (Sum.inl i)
  · rw [hstar]
    calc
      ‖entry (Fin 2) B 1 0 (x i) - star T (x i)‖ =
          ‖(B (v (Sum.inr i)) - offDiagonal T (v (Sum.inr i))) 1‖ := by
            simp [v, PiLp.sub_apply, offDiagonal_apply_one, single_apply, entry_apply]
      _ ≤ ‖B (v (Sum.inr i)) - offDiagonal T (v (Sum.inr i))‖ := PiLp.norm_apply_le _ 1
      _ < ε := happ (Sum.inr i)

end Amplification

end SpectralIsometry.MatrixKaplansky

