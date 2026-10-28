module
public import Mathlib.Topology.Neighborhoods
public import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# Generic Neighborhood Reindex

Supporting results for spectral isometries of complex unital C*-algebras.
-/

 

@[expose] public section
set_option autoImplicit false
noncomputable section
open Filter Topology

namespace SpectralIsometry.NeighborhoodReindex

def Index (E : Type*) (t : TopologicalSpace E) (x : E) :=
  OrderDual {U : Set E // U∈@nhds E t x}

instance indexPartialOrder (E : Type*) (t : TopologicalSpace E) (x : E) :
    PartialOrder (Index E t x) :=
  inferInstanceAs (PartialOrder (OrderDual {U : Set E // U∈@nhds E t x}))

instance indexNonempty (E : Type*) (t : TopologicalSpace E) (x : E) :
    Nonempty (Index E t x) := ⟨⟨Set.univ,Filter.univ_mem⟩⟩

instance indexDirected (E : Type*) (t : TopologicalSpace E) (x : E) :
    IsDirectedOrder (Index E t x) where
  directed U V := ⟨⟨U.val∩V.val,Filter.inter_mem U.property V.property⟩,
    Set.inter_subset_left,Set.inter_subset_right⟩

theorem index_atTop_neBot (E : Type*) (t : TopologicalSpace E) (x : E) :
    (atTop : Filter (Index E t x)).NeBot := inferInstance

theorem exists_reindex {E A I : Type*} (t : TopologicalSpace E) (x : E)
    (f : A → E) {l : Filter I} [l.NeBot] (a : I → A)
    (ha : Tendsto (fun i => f (a i)) l (@nhds E t x))
    (P : A → Prop) (hP : ∀ i, P (a i)) :
    ∃ b : Index E t x → A, (∀ U, P (b U)) ∧
      Tendsto (fun U => f (b U)) atTop (@nhds E t x) := by
  have hex (U : Index E t x) : ∃ i, f (a i)∈U.val := by
    have h : ∀ᶠ i in l, f (a i)∈U.val := ha U.property
    exact Filter.Eventually.exists h
  choose j hj using hex
  refine ⟨fun U => a (j U),fun U => hP (j U),?_⟩
  apply Filter.tendsto_def.mpr
  intro S hS
  refine Filter.eventually_atTop.2 ⟨⟨S,hS⟩,?_⟩
  intro U hU
  exact hU (hj U)

end SpectralIsometry.NeighborhoodReindex

