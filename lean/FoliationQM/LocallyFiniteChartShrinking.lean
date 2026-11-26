module
public import Mathlib.Topology.LocallyFinite
public import Mathlib.Topology.Sets.Opens

/-!
# Locally finite chart neighborhoods

For the frame-bundle construction in v13 `prop:takabayasi`, a locally
finite open shrinking places each carrier closure inside its original
chart. Around a point, only finitely many such closures occur. One open
neighborhood can satisfy their simultaneous constraints and exclude
every carrier whose closure misses the point.
-/

@[expose] public section
noncomputable section
open Set Filter TopologicalSpace
open scoped Topology
namespace FoliationQM.LocallyFiniteChartShrinking

variable {B ι : Type*} [TopologicalSpace B]

/-- Open carriers covering the base, locally finite and with closures in the designated charts. -/
structure Data (U : ι → Opens B) where
  /-- The smaller open region assigned to each original chart. -/
  carrier : ι → Opens B
  /-- Every point belongs to one of the smaller open regions. -/
  covers : ∀ x : B, ∃ i, x ∈ carrier i
  /-- Each point has a neighborhood meeting only finitely many carriers. -/
  locallyFinite : LocallyFinite (fun i => (carrier i : Set B))
  /-- The entire closure of a carrier is contained in its original chart. -/
  closure_subset : ∀ i, closure (carrier i : Set B) ⊆ U i

variable {U : ι → Opens B} (S : Data U)

/-- Choose a parent whose open carrier contains the point. -/
def parent (x : B) : ι := (S.covers x).choose

/-- The point lies in its chosen parent's carrier. -/
theorem mem_parent (x : B) : x ∈ S.carrier (parent S x) := (S.covers x).choose_spec

/-- Only finitely many carrier closures contain a given point. -/
theorem finite_active (x : B) : {j | x ∈ closure (S.carrier j : Set B)}.Finite :=
  S.locallyFinite.closure.point_finite x

/-- One open neighborhood excludes all carriers outside the closures through its
center and fits inside every prescribed open for those finitely many indices. -/
theorem exists_control (x : B) (O : ι → Opens B)
    (hO : ∀ j, x ∈ closure (S.carrier j : Set B) → x ∈ O j) :
    ∃ W : Opens B, x ∈ W ∧ W ≤ S.carrier (parent S x) ∧
      (∀ y ∈ W, ∀ j, y ∈ S.carrier j → x ∈ closure (S.carrier j : Set B)) ∧
      (∀ j, x ∈ closure (S.carrier j : Set B) → W ≤ O j) := by
  have hnear := S.locallyFinite.closure.eventually_subset (fun _ => isClosed_closure) x
  have hopen : ∀ᶠ y in 𝓝 x, ∀ j ∈ {i | x ∈ closure (S.carrier i : Set B)}, y ∈ O j :=
    (finite_active S x).eventually_all.mpr (fun j hj => (O j).isOpen.mem_nhds (hO j hj))
  have hcontrol : {y | y ∈ S.carrier (parent S x) ∧
      (∀ j, y ∈ S.carrier j → x ∈ closure (S.carrier j : Set B)) ∧
      (∀ j, x ∈ closure (S.carrier j : Set B) → y ∈ O j)} ∈ 𝓝 x := by
    filter_upwards [(S.carrier (parent S x)).isOpen.mem_nhds (mem_parent S x), hnear, hopen]
      with y hy hsub hinc
    exact ⟨hy, fun _ hj => hsub (subset_closure hj), hinc⟩
  obtain ⟨w, hw, hwo, hx⟩ := mem_nhds_iff.mp hcontrol
  exact ⟨⟨w, hwo⟩, hx, fun _ hy => (hw hy).1, fun _ hy => (hw hy).2.1,
    fun j hj _ hy => (hw hy).2.2 j hj⟩

end FoliationQM.LocallyFiniteChartShrinking
