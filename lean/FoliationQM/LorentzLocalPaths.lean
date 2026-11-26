module
public import FoliationQM.ContractibleTransitionPaths
public import FoliationQM.LorentzManifold
public import Mathlib.Analysis.Convex.Contractible
public import Mathlib.Topology.Homotopy.LocallyContractible

/-!
# Local paths to actual proper future Lorentz elements

For the frame-bundle component of v13 `prop:takabayasi`, every neighborhood
of a Lorentz matrix contains the inverse image of a convex model ball under
its actual translated Cayley chart. The resulting contractible open sets
give joint paths from the group identity to every point of a neighborhood.
These paths can be composed with continuous chart gauges after shrinking.
-/

@[expose] public section
noncomputable section
open Set Topology TopologicalSpace
namespace FoliationQM.LorentzLocalPaths
open LorentzMatrixGroup LorentzCayleyCharts

/-- Every open neighborhood contains a contractible open neighborhood obtained
by transporting a nonempty model ball through the inverse Cayley chart. -/
theorem exists_contractible_open_subset (g : ProperFutureLorentz)
    (U : Opens ProperFutureLorentz) (hg : g ∈ U) :
    ∃ V : Opens ProperFutureLorentz, g ∈ V ∧ V ≤ U ∧ ContractibleSpace ↥V := by
  let e := chart g
  have hgs : g ∈ e.source := mem_chart_source g
  have hgt : e g ∈ e.target ∩ e.symm ⁻¹' (U : Set ProperFutureLorentz) := by
    refine ⟨e.map_source hgs, ?_⟩
    change e.symm (e g) ∈ U
    rw [e.left_inv hgs]
    exact hg
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp (e.isOpen_inter_preimage_symm U.isOpen) (e g) hgt
  let ball := Metric.ball (e g) r
  have ht : ball ⊆ e.target := fun y hy => (hball hy).1
  let V : Opens ProperFutureLorentz :=
    ⟨e.symm '' ball, e.isOpen_image_symm_of_subset_target Metric.isOpen_ball ht⟩
  have hcenter : e g ∈ ball := Metric.mem_ball_self hr
  have hballC : ContractibleSpace ball := (convex_ball (e g) r).contractibleSpace ⟨_, hcenter⟩
  refine ⟨V, ⟨e g, hcenter, e.left_inv hgs⟩, ?_, ?_⟩
  · rintro _ ⟨y, hy, rfl⟩
    exact (hball hy).2
  · exact (e.symm.homeomorphOfImageSubsetSource ht rfl).contractibleSpace_iff.mp hballC

/-- The original proper future matrix group has a basis of contractible neighborhoods. -/
instance instStronglyLocallyContractible : StronglyLocallyContractibleSpace ProperFutureLorentz where
  contractible_basis g := by
    rw [Filter.hasBasis_self]
    intro s hs
    obtain ⟨u, hus, hu, hgu⟩ := mem_nhds_iff.mp hs
    obtain ⟨V, hg, hVu, hV⟩ := exists_contractible_open_subset g ⟨u, hu⟩ hgu
    exact ⟨V, V.isOpen.mem_nhds hg, hV, fun _ hx => hus (hVu hx)⟩

/-- A contractible open neighborhood selected from the actual chart at `g`. -/
def neighborhood (g : ProperFutureLorentz) : Opens ProperFutureLorentz :=
  Classical.choose (exists_contractible_open_subset g ⊤ (Set.mem_univ g))

/-- The selected neighborhood contains its original Lorentz matrix. -/
theorem mem_neighborhood (g : ProperFutureLorentz) : g ∈ neighborhood g :=
  (Classical.choose_spec (exists_contractible_open_subset g ⊤ (Set.mem_univ g))).1

/-- The selected neighborhood is contractible with its actual subtype topology. -/
theorem contractible_neighborhood (g : ProperFutureLorentz) :
    ContractibleSpace ↥(neighborhood g) :=
  (Classical.choose_spec (exists_contractible_open_subset g ⊤ (Set.mem_univ g))).2.2

/-- The group identity and the inclusion of the selected Cayley neighborhood
are joined by an actual homotopy with values in the original matrix group. -/
def homotopy (g : ProperFutureLorentz) :
    (ContinuousMap.const ↥(neighborhood g) (1 : ProperFutureLorentz)).Homotopy
      ⟨Subtype.val, continuous_subtype_val⟩ := by
  letI := contractible_neighborhood g
  exact ContractibleTransitionPaths.fromOne _

/-- The joint local path map on time and a Lorentz neighborhood point. -/
def joint (g : ProperFutureLorentz) : C(unitInterval × ↥(neighborhood g), ProperFutureLorentz) :=
  (homotopy g).toContinuousMap

/-- All the local paths start at the actual group identity. -/
theorem joint_zero (g : ProperFutureLorentz) (x : neighborhood g) : joint g (0, x) = 1 :=
  (homotopy g).apply_zero x

/-- Each local path ends at the specified Lorentz group element. -/
theorem joint_one (g : ProperFutureLorentz) (x : neighborhood g) : joint g (1, x) = x.val :=
  (homotopy g).apply_one x

end FoliationQM.LorentzLocalPaths
