module
public import Mathlib.Topology.FiberBundle.Basic
public import Mathlib.Topology.Algebra.Group.Basic

/-!
# Independent geometric principal bundle atlases

Source scope: the geometric bundle bridge underlying the Spin-frame
interpretation of v13 `prop:takabayasi`. The total space and projection
are supplied independently, with their original topologies and actual
Mathlib local trivializations covering the base. A candidate right
operation preserves the base and is right multiplication in those
trivializations. The group action laws, free and transitive fibers,
projection surjectivity, local sections, and transition cocycle laws are
proved from these geometric coordinate premises rather than assumed.

The canonical sections and transition coordinates are continuous only
on their genuine chart domains. Joint continuity of the right operation
is derived when multiplication in the supplied group is continuous.
No smooth atlas, metric frame identification, existence of a geometric
Spin lift, or dynamics is assumed or concluded here.
-/

@[expose] public section
noncomputable section
open Set Function Bundle Topology
open scoped Topology
namespace FoliationQM.GeometricPrincipalAtlas

variable {B P G : Type*} [TopologicalSpace B] [TopologicalSpace P]
  [TopologicalSpace G] [Group G]

/-- Independent geometric principal-atlas data: actual local trivializations and local right multiplication, without assumed action laws or fiber transitivity. -/
structure Data (proj : P → B) (ι : Type*) where
  /-- The supplied actual local bundle trivializations of the original projection. -/
  triv : ι → Bundle.Trivialization G proj
  /-- The actual trivialization domains cover the entire base. -/
  covers : ∀ x : B, ∃ i, x ∈ (triv i).baseSet
  /-- The candidate geometric right operation on the original total space. -/
  right : P → G → P
  /-- The right operation preserves the actual projection. -/
  proj_right : ∀ p g, proj (right p g) = proj p
  /-- In each actual trivialization the operation is literal right multiplication in the group. -/
  right_local : ∀ i p g, proj p ∈ (triv i).baseSet →
    (triv i (right p g)).2 = (triv i p).2 * g

namespace Data

variable {proj : P → B} {ι : Type*} (A : Data (G := G) proj ι)

/-- Actual points in one principal chart are determined by their original base point and group coordinate. -/
theorem coordinate_injective (i : ι) {p q : P}
    (hp : proj p ∈ (A.triv i).baseSet) (hq : proj q ∈ (A.triv i).baseSet)
    (hbase : proj p = proj q) (hcoord : (A.triv i p).2 = (A.triv i q).2) : p = q := by
  apply (A.triv i).toOpenPartialHomeomorph.injOn
    ((A.triv i).mem_source.mpr hp) ((A.triv i).mem_source.mpr hq)
  exact Prod.ext (((A.triv i).coe_fst' hp).trans (hbase.trans ((A.triv i).coe_fst' hq).symm)) hcoord

/-- The geometric right operation has the group identity law, derived from the covering trivializations. -/
theorem right_one (p : P) : A.right p 1 = p := by
  obtain ⟨i, hi⟩ := A.covers (proj p)
  apply A.coordinate_injective i (by rw [A.proj_right]; exact hi) hi (A.proj_right p 1)
  rw [A.right_local i p 1 hi, mul_one]

/-- The geometric right operation has the genuine right-action composition order, derived in actual local coordinates. -/
theorem right_mul (p : P) (g h : G) : A.right (A.right p g) h = A.right p (g * h) := by
  obtain ⟨i, hi⟩ := A.covers (proj p)
  have hpg : proj (A.right p g) ∈ (A.triv i).baseSet := by rw [A.proj_right]; exact hi
  apply A.coordinate_injective i
    (by rw [A.proj_right, A.proj_right]; exact hi)
    (by rw [A.proj_right]; exact hi)
    (by rw [A.proj_right, A.proj_right, A.proj_right])
  rw [A.right_local i (A.right p g) h hpg, A.right_local i p g hi,
    A.right_local i p (g * h) hi, mul_assoc]

/-- The actual right operation is free: a point's two right translates agree only for equal group elements. -/
theorem right_injective (p : P) : Injective (A.right p) := by
  obtain ⟨i, hi⟩ := A.covers (proj p)
  intro g h he
  have hc := congrArg (fun q : P => (A.triv i q).2) he
  rw [A.right_local i p g hi, A.right_local i p h hi] at hc
  exact mul_left_cancel hc

/-- Any two actual points over the same base point differ by exactly one group element under the derived right action. -/
theorem existsUnique_right (p q : P) (hbase : proj p = proj q) : ∃! g : G, A.right p g = q := by
  obtain ⟨i, hi⟩ := A.covers (proj p)
  have hq : proj q ∈ (A.triv i).baseSet := hbase ▸ hi
  let g := (A.triv i p).2⁻¹ * (A.triv i q).2
  have hg : A.right p g = q := by
    apply A.coordinate_injective i (by rw [A.proj_right]; exact hi) hq
      ((A.proj_right p g).trans hbase)
    rw [A.right_local i p g hi]
    simp [g]
  exact ⟨g, hg, fun h hh => A.right_injective p (hh.trans hg.symm)⟩

/-- The canonical chart section is the actual inverse trivialization of the group unit. -/
def localSection (i : ι) (x : B) : P :=
  (A.triv i).toOpenPartialHomeomorph.symm (x, 1)

/-- The canonical section has exactly its original base point on the actual chart domain. -/
theorem proj_localSection (i : ι) (x : B) (hx : x ∈ (A.triv i).baseSet) :
    proj (A.localSection i x) = x := (A.triv i).proj_symm_apply' hx

/-- The canonical section has exactly the identity group coordinate in its own actual chart. -/
theorem localSection_coordinate (i : ι) (x : B) (hx : x ∈ (A.triv i).baseSet) :
    A.triv i (A.localSection i x) = (x, 1) := (A.triv i).apply_symm_apply' hx

include A in
/-- The actual projection is surjective because the supplied base-covering charts contain their unit sections. -/
theorem proj_surjective : Surjective proj := by
  intro x
  obtain ⟨i, hi⟩ := A.covers x
  exact ⟨A.localSection i x, A.proj_localSection i x hi⟩

include A in
/-- The original projection is continuous, as proved in the actual covering family of bundle charts. -/
theorem continuous_proj : Continuous proj := by
  apply continuous_iff_continuousAt.mpr
  intro p
  obtain ⟨i, hi⟩ := A.covers (proj p)
  exact (A.triv i).continuousAt_proj ((A.triv i).mem_source.mpr hi)

/-- Each canonical local section is continuous precisely on its original chart domain. -/
theorem continuousOn_localSection (i : ι) :
    ContinuousOn (A.localSection i) (A.triv i).baseSet :=
  (A.triv i).continuousOn_symm_prodMk_left

/-- Actual right translation is given by inverse trivialization of the original base and right-multiplied group coordinate on any containing chart. -/
theorem right_eq_symm (i : ι) (p : P) (g : G) (hp : proj p ∈ (A.triv i).baseSet) :
    A.right p g = (A.triv i).toOpenPartialHomeomorph.symm (proj p, (A.triv i p).2 * g) := by
  have hs := (A.triv i).proj_symm_apply' (x := (A.triv i p).2 * g) hp
  apply A.coordinate_injective i (by rw [A.proj_right]; exact hp)
    (by rw [hs]; exact hp) ((A.proj_right p g).trans hs.symm)
  rw [A.right_local i p g hp, (A.triv i).apply_symm_apply' hp]

/-- Every actual point in a principal chart is its canonical unit section translated by its own group coordinate. -/
theorem localSection_right_coordinate (i : ι) (p : P) (hp : proj p ∈ (A.triv i).baseSet) :
    A.right (A.localSection i (proj p)) (A.triv i p).2 = p := by
  rw [A.right_eq_symm i _ _ (by rw [A.proj_localSection i (proj p) hp]; exact hp),
    A.proj_localSection i (proj p) hp, A.localSection_coordinate i (proj p) hp, one_mul]
  exact (A.triv i).symm_apply_mk_proj ((A.triv i).mem_source.mpr hp)

/-- The actual chart-i-to-chart-j transition is the group coordinate of the canonical i-section in chart j. -/
def transition (i j : ι) (x : B) : G := (A.triv j (A.localSection i x)).2

/-- Actual principal coordinates change by left multiplication in the original chart-i-to-chart-j order. -/
theorem change_coordinate (i j : ι) (p : P)
    (hi : proj p ∈ (A.triv i).baseSet) (hj : proj p ∈ (A.triv j).baseSet) :
    (A.triv j p).2 = A.transition i j (proj p) * (A.triv i p).2 := by
  have hs : proj (A.localSection i (proj p)) ∈ (A.triv j).baseSet := by
    rw [A.proj_localSection i (proj p) hi]
    exact hj
  have he := A.right_local j (A.localSection i (proj p)) (A.triv i p).2 hs
  rw [A.localSection_right_coordinate i p hi] at he
  exact he

/-- The actual geometric self-transition is the group identity on its chart domain. -/
theorem transition_self (i : ι) (x : B) (hx : x ∈ (A.triv i).baseSet) :
    A.transition i i x = 1 := congrArg Prod.snd (A.localSection_coordinate i x hx)

/-- The actual geometric transitions obey the genuine ordered cocycle law on triple overlaps, derived from the original independent total-space charts. -/
theorem transition_comp (i j k : ι) (x : B)
    (hi : x ∈ (A.triv i).baseSet) (hj : x ∈ (A.triv j).baseSet)
    (hk : x ∈ (A.triv k).baseSet) :
    A.transition j k x * A.transition i j x = A.transition i k x := by
  have he := A.change_coordinate j k (A.localSection i x)
    (by rw [A.proj_localSection i x hi]; exact hj)
    (by rw [A.proj_localSection i x hi]; exact hk)
  rw [A.proj_localSection i x hi] at he
  exact he.symm

/-- Actual geometric transition functions are continuous on their true pair overlap, without requiring their off-overlap values to be continuous. -/
theorem continuousOn_transition (i j : ι) :
    ContinuousOn (A.transition i j) ((A.triv i).baseSet ∩ (A.triv j).baseSet) := by
  have hs : ContinuousOn (A.localSection i)
      ((A.triv i).baseSet ∩ (A.triv j).baseSet) :=
    (A.continuousOn_localSection i).mono inter_subset_left
  have htr := (A.triv j).toOpenPartialHomeomorph.continuousOn.comp hs (by
    intro x hx
    apply (A.triv j).mem_source.mpr
    rw [A.proj_localSection i x hx.1]
    exact hx.2)
  exact htr.snd

/-- Joint continuity of the geometric right operation follows from actual chart regularity and continuous multiplication in the supplied group. -/
theorem continuous_right [ContinuousMul G] : Continuous (fun z : P × G => A.right z.1 z.2) := by
  apply continuous_iff_continuousAt.mpr
  intro z
  obtain ⟨i, hi⟩ := A.covers (proj z.1)
  have ht : ContinuousAt (A.triv i) z.1 :=
    (A.triv i).toOpenPartialHomeomorph.continuousAt ((A.triv i).mem_source.mpr hi)
  have hb : ContinuousAt (fun y : P × G => proj y.1) z :=
    A.continuous_proj.continuousAt.comp continuous_fst.continuousAt
  have hc : ContinuousAt (fun y : P × G => (proj y.1, (A.triv i y.1).2 * y.2)) z :=
    hb.prodMk ((ht.comp continuous_fst.continuousAt).snd.mul continuous_snd.continuousAt)
  have hs := ((A.triv i).toOpenPartialHomeomorph.continuousAt_symm
    ((A.triv i).mem_target.mpr hi)).comp hc
  apply hs.congr_of_eventuallyEq
  filter_upwards [hb.preimage_mem_nhds ((A.triv i).open_baseSet.mem_nhds hi)] with y hy
  exact A.right_eq_symm i y.1 y.2 hy

end Data
end FoliationQM.GeometricPrincipalAtlas
