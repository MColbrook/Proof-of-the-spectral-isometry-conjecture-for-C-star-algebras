module

public import SpectralIsometry.Basic
public import SpectralIsometry.ConcreteCornerRange

/-!
# Corner Holomorphic Weight

Supporting results for spectral isometries of complex unital C*-algebras.
-/

 

@[expose] public section
set_option autoImplicit false
noncomputable section

open OAI.HochschildCorners

namespace SpectralIsometry.ConcreteCorner

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem selfAdjoint_of_central_of_ambient_real_spectrum
    (M : VonNeumannAlgebra H) (p : M) (hp : IsStarProjection p)
    (u : Corner p hp) (hcentral : ∀ a : Corner p hp, Commute u a)
    (hreal : ∀ z ∈ spectrum ℂ (u : M), z.im = 0) : IsSelfAdjoint u := by
  letI : IsStarNormal (u : M) := ⟨by
    change star (u : M) * (u : M) = (u : M) * star (u : M)
    exact congrArg (fun a : Corner p hp => (a : M)) (hcentral (star u)).symm.eq⟩
  have hsa : IsSelfAdjoint (u : M) := normal_real_spectrum_selfadjoint (u : M) hreal
  change star u = u
  exact Subtype.ext hsa.star_eq

theorem holomorphic_central_weight_eq_one
    (M : VonNeumannAlgebra H) (p : M) (hp : IsStarProjection p)
    (u : ℂ → Corner p hp) (hu : Differentiable ℂ u)
    (hcentral : ∀ z : ℂ, ∀ a : Corner p hp, Commute (u z) a)
    (hreal : ∀ z : ℂ, ∀ ζ ∈ spectrum ℂ (u z : M), ζ.im = 0)
    (hzero : u 0 = 1) : ∀ z : ℂ, u z = 1 := by
  have hsa (z : ℂ) : IsSelfAdjoint (u z) :=
    selfAdjoint_of_central_of_ambient_real_spectrum M p hp (u z) (hcentral z) (hreal z)
  intro z
  exact (holomorphic_selfadjoint_const u hu hsa z 0).trans hzero

end SpectralIsometry.ConcreteCorner

