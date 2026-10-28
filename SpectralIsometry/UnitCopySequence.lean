module

public import OAI.Analysis.BoundedHochschild.ProperlyInfiniteIsometries

/-!
# Unit Copy Sequence

Supporting results for spectral isometries of complex unital C*-algebras.
-/

@[expose] public section
noncomputable section

open scoped ComplexOrder CStarAlgebra
open OAI.HochschildComparison OAI.BoundedHochschild.KadisonRingrose

namespace SpectralIsometry.SquareZeroPreserver

variable {M : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]

theorem exists_orthogonal_unitCopy_sequence (r s : M)
    (hr : star r * r = 1) (hs : star s * s = 1) (hrs : star r * s = 0) :
    ∃ c : ℕ → PartialIso M, (∀ n, (c n).initial = 1) ∧
      ∀ i j, i ≠ j → (c i).final * (c j).final = 0 := by
  let p := isometryDefect r
  have hp : IsStarProjection p := isometryDefect_projection hr
  let S : PartialIso M := ⟨s,by rw [mul_assoc,hs,mul_one]⟩
  have hps : p * s = s := by
    dsimp [p,isometryDefect]
    rw [sub_mul,one_mul,mul_assoc,hrs,mul_zero,sub_zero]
  have hSf : S.final ≤ p := by
    apply (S.final_proj.le_iff_mul_eq_right hp).mpr
    change p * (s * star s) = s * star s
    rw [←mul_assoc,hps]
  let b (n : ℕ) := isometryColumn r hr p hp n
  let c (n : ℕ) := composePartialIso (b n) S (by
    rw [isometryColumn_initial]
    exact hSf)
  have hci (n : ℕ) : (c n).initial = 1 := by rw [composePartialIso_initial]; exact hs
  have hcf (n : ℕ) : (c n).final ≤ (b n).final := composePartialIso_final_le ..
  refine ⟨c,hci,?_⟩
  intro i j hij
  have horth : (b i).final * (b j).final = 0 :=
    isometryColumn_final_orthogonal hr hp (isometryDefect_mul hr) hij
  exact projection_mul_zero_of_bounds (b i).final_proj (b j).final_proj
    (c i).final_proj (c j).final_proj horth (hcf i) (hcf j)

end SpectralIsometry.SquareZeroPreserver

