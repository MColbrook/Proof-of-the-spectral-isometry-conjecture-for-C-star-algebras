module
public import SpectralIsometry.NormalCornerFamilyJordan

/-!
# Generic Corner Lift

Supporting results for spectral isometries of complex unital C*-algebras.
-/

 

@[expose] public section
set_option autoImplicit false
noncomputable section
open Filter Topology OAI.HochschildCorners

namespace SpectralIsometry.EntireAssemblyGeneric
open StrongStarApproximation

section StrongStar
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem restriction_strongStarTendsto (M : VonNeumannAlgebra H)
    (p : M) (hp : IsStarProjection p)
    (R : Corner p hp →L[ℂ] Corner p hp) (V : M →L[ℂ] M)
    (hcoe : ∀ a : Corner p hp, (R a:M)=V (a:M))
    {ι : Type*} {l : Filter ι} (a : ι → Corner p hp) (b : Corner p hp)
    (hV : StrongStarTendsto (fun i => (V (a i:M):H →L[ℂ] H)) l
      (V (b:M):H →L[ℂ] H)) :
    StrongStarTendsto (fun i => ((R (a i):M):H →L[ℂ] H)) l
      ((R b:M):H →L[ℂ] H) := by
  simpa only [hcoe] using hV
end StrongStar

end SpectralIsometry.EntireAssemblyGeneric

