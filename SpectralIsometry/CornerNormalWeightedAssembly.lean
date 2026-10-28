module

public import SpectralIsometry.ConcreteCornerPreserverTransport
public import SpectralIsometry.NormalWeightedProjection

/-!
# Corner Normal Weighted Assembly

Supporting results for spectral isometries of complex unital C*-algebras.
-/

 

@[expose] public section
set_option autoImplicit false
noncomputable section

open Filter Topology
open scoped ComplexOrder CStarAlgebra
open OAI.HochschildCorners
open SpectralIsometry.StrongStarApproximation
open SpectralIsometry.ConcreteCorner

namespace SpectralIsometry.SquareZeroPreserver

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem central_weight_of_corner_bounded_strongStar_continuity
    (M : VonNeumannAlgebra H) (p : M) (hp : IsStarProjection p)
    (R : Corner p hp →L[ℂ] Corner p hp)
    (hR : PreservesSquareZero R.toLinearMap) (honto : Function.Surjective R)
    (r s : Corner p hp) (hr : star r*r=1) (hs : star s*s=1) (hrs : star r*s=0)
    (hseq : ∀ (a : ℕ → Corner p hp) (b : Corner p hp), (∀ n, ‖a n‖ ≤ 1) →
      StrongStarTendsto (fun n => ((a n : M) : H →L[ℂ] H)) atTop ((b : M) : H →L[ℂ] H) →
      StrongStarTendsto (fun n => ((R (a n) : M) : H →L[ℂ] H)) atTop ((R b : M) : H →L[ℂ] H)) :
    ∀ b : Corner p hp, Commute (R 1) b := by
  obtain ⟨hr',hs',hrs'⟩ := transport_unit_isometries M p hp r s hr hs hrs
  have hcentral := central_weight_of_bounded_strongStar_continuity
    (model M p hp) (model M p hp) (transport M p hp R)
    (transport_preservesSquareZero M p hp R hR) (transport_surjective M p hp R honto)
    ((equivalence M p hp).symm r) ((equivalence M p hp).symm s) hr' hs' hrs'
    (transport_bounded_sequence_continuity M p hp R hseq)
  exact central_weight_of_transport M p hp R hcentral

end SpectralIsometry.SquareZeroPreserver

