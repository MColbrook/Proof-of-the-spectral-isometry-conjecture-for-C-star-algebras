module

public import Mathlib.Analysis.Normed.Algebra.GelfandFormula
public import Mathlib.Topology.Algebra.Algebra

/-!
# Subalgebra Radius

Supporting results for spectral isometries of complex unital C*-algebras.
-/

 

@[expose] public section
noncomputable section

namespace SpectralIsometry

variable {A B : Type*} [NormedRing A] [NormedRing B]
  [NormedAlgebra ℂ A] [NormedAlgebra ℂ B] [CompleteSpace A] [CompleteSpace B]

theorem isometric_algHom_spectralRadius (f : A →ₐ[ℂ] B) (hf : Isometry f) (a : A) :
    spectralRadius ℂ (f a) = spectralRadius ℂ a := by
  have hn (x : A) : ‖f x‖₊ = ‖x‖₊ := by
    apply Subtype.ext
    change ‖f x‖ = ‖x‖
    simpa only [map_zero, dist_zero_right] using hf.dist_eq x 0
  apply tendsto_nhds_unique (spectrum.pow_nnnorm_pow_one_div_tendsto_nhds_spectralRadius (f a))
  simpa only [← map_pow f, hn] using
    spectrum.pow_nnnorm_pow_one_div_tendsto_nhds_spectralRadius a

end SpectralIsometry

namespace SpectralIsometry

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]

/-- Intrinsic and ambient radii agree, including zero algebras. No star-closedness
or equality of the actual spectra is assumed or concluded. -/
theorem closed_subalgebra_spectralRadius (S : Subalgebra ℂ A)
    (hS : IsClosed (S : Set A)) (a : S) :
    spectralRadius ℂ a = spectralRadius ℂ (a : A) := by
  letI : CompleteSpace S := hS.completeSpace_coe
  exact (isometric_algHom_spectralRadius S.val isometry_subtype_coe a).symm

end SpectralIsometry

