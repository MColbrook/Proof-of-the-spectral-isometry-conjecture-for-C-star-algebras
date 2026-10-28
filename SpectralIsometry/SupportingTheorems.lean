module

public import SpectralIsometry.MainReduction
public import SpectralIsometry.SquareZeroContour
public import SpectralIsometry.SupportFunctionLimit
public import SpectralIsometry.InvertiblePolarDistance

/-!
# Supporting Theorems

Supporting results for spectral isometries of complex unital C*-algebras.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open Complex Filter Topology

namespace SpectralIsometry.SourceClaims

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]
local instance orderedA : PartialOrder A := CStarAlgebra.spectralOrder A
local instance starOrderedA : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A

theorem square_zero_preservation (T : A →ₗ[ℂ] B) (honto : Function.Surjective T)
    (h1 : T 1=1) (hr : PreservesRadius T) (n : A) (hn : n^2=0) : (T n)^2=0 :=
  SquareZeroPreservation.image_square_zero (MainReduction.radiusEquiv T honto hr) hr h1 n hn

theorem square_zero_contour (T : A →ₗ[ℂ] B) (honto : Function.Surjective T)
    (h1 : T 1=1) (hr : PreservesRadius T) (n : A) (hn : n^2=0)
    (ε : ℝ) (hε : 0<ε) (hε1 : ε≤1) :
    (T n)^2=(2*(Real.pi:ℂ)*I)⁻¹ •
      (∮ z in C(0,ε), z^2 • Ring.inverse (algebraMap ℂ B z-T n)) :=
  SquareZeroContour.image_contour (MainReduction.radiusEquiv T honto hr) hr h1 n hn ε hε hε1

theorem angular_support_limit (K : Set ℂ) (hK : IsCompact K) (hne : K.Nonempty) (θ : ℝ) :
    Tendsto (fun t : ℝ => sSup ((fun w : ℂ => ‖w-(-(t:ℂ)*exp ((θ:ℂ)*I))‖) '' K)-t)
      atTop (𝓝 (sSup ((fun w : ℂ => (exp (-((θ:ℂ)*I))*w).re) '' K))) := by
  simpa only [SupportFunctionLimit.farthestDistance,SupportFunctionLimit.support] using
    SupportFunctionLimit.angular_support_limit K hK hne θ

theorem polar_nearest_nonunit [Nontrivial A] (c : A) (hc : IsUnit c) :
    ∃ v : A, v ∈ unitary A ∧ c=v*CFC.abs c ∧
      IsLeast (spectrum ℝ (CFC.abs c)) ‖Ring.inverse c‖⁻¹ ∧
      ¬IsUnit (c-‖Ring.inverse c‖⁻¹ • v) ∧
      ‖c-(c-‖Ring.inverse c‖⁻¹ • v)‖=‖Ring.inverse c‖⁻¹ := by
  refine ⟨InvertiblePolarDistance.polarFactor c,
    InvertiblePolarDistance.polarFactor_mem_unitary c hc,
    InvertiblePolarDistance.polar_decomposition c hc,
    InvertiblePolarDistance.modulus_spectrum_isLeast c hc,
    InvertiblePolarDistance.polar_boundary_nonunit c hc,
    InvertiblePolarDistance.polar_boundary_distance c hc⟩

end SpectralIsometry.SourceClaims

