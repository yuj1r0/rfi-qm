module
public import FoliationQM.LocallyFiniteChartShrinking
public import Mathlib.Topology.Compactness.Paracompact
public import Mathlib.Topology.ShrinkingLemma

/-!
# Shrinking an open cover of a paracompact normal base

For the frame-bundle construction in v13 `prop:takabayasi`, first choose
a locally finite open refinement with the original chart indices. Shrink
this point-finite cover again inside the intermediate opens, so the
resulting closures lie in the designated original charts.
-/

@[expose] public section
noncomputable section
open Set TopologicalSpace
namespace FoliationQM.ParacompactChartShrinking

variable {B ι : Type*} [TopologicalSpace B] [ParacompactSpace B] [NormalSpace B]
  (U : ι → Opens B) (hU : ∀ x : B, ∃ i, x ∈ U i)

include hU

/-- Any indexed open cover of this base has locally finite open carriers whose closures lie
in their respective original charts. -/
theorem nonempty : Nonempty (LocallyFiniteChartShrinking.Data U) := by
  obtain ⟨v, hvOpen, hvCover, hvFinite, hvSub⟩ :=
    precise_refinement (fun i => (U i : Set B)) (fun i => (U i).isOpen) (iUnion_eq_univ_iff.mpr hU)
  obtain ⟨w, hwCover, hwOpen, hwClosure⟩ :=
    exists_iUnion_eq_closure_subset hvOpen hvFinite.point_finite hvCover
  exact ⟨{ carrier := fun i => ⟨w i, hwOpen i⟩
           covers := iUnion_eq_univ_iff.mp hwCover
           locallyFinite := hvFinite.subset (fun i => subset_closure.trans (hwClosure i))
           closure_subset := fun i => (hwClosure i).trans (hvSub i) }⟩

/-- A choice of such a shrinking on exactly the original index type. -/
def shrinking : LocallyFiniteChartShrinking.Data U := (nonempty U hU).some

end FoliationQM.ParacompactChartShrinking
