module
public import FoliationQM.SmoothCocycleBundle
public import Mathlib.Geometry.Manifold.ContMDiffMap

/-!
# Smooth dependent sections and compatible local families

Source: smooth-section infrastructure for the supplied-transition interpretation
of v13 `prop:takabayasi`. The actual FiberBundleCore total space retains its
core-generated topology and uses the independently constructed atlas of bundle
trivializations followed by base-and-fiber product charts. A smooth section is
defined independently by smoothness of its actual dependent total-space graph.

Local families are bundled smooth maps on the actual open base domains, with
an independently stated compatibility relation using the actual core changes.
They reconstruct a dependent section using indexAt only pointwise. Its prescribed
coordinate formula is proved in every available chart before any regularity
claim. Actual smooth trivializations and inverses then prove the equivalence,
both inverse laws, and uniqueness. No smooth selection of chart indices or
global individual polar representatives is assumed or asserted.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold
open Function Set Topology Bundle
namespace FoliationQM.SmoothCocycleSections
attribute [local instance] SmoothCocycleBundle.totalChartedSpace
variable {E H E' H' B F ι : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  [TopologicalSpace B] [ChartedSpace H B]
  [TopologicalSpace F] [ChartedSpace H' F]
  (I : ModelWithCorners ℝ E H) (J : ModelWithCorners ℝ E' H')
  (Z : FiberBundleCore ι B F) (n : WithTop ℕ∞)

/-- The actual open base domain of a core trivialization. -/
def baseDomain (i : ι) : TopologicalSpace.Opens B := ⟨Z.baseSet i, Z.isOpen_baseSet i⟩

/-- The actual total-space graph of a dependent section. -/
def sectionGraph (s : ∀ x : B, Z.Fiber x) : B → Z.TotalSpace := fun x => ⟨x, s x⟩

/-- The actual fiber coordinate of a dependent section in a core trivialization. -/
def sectionCoordinate (s : ∀ x : B, Z.Fiber x) (i : ι) (x : baseDomain Z i) : F :=
  ((Z.localTriv i) (sectionGraph Z s x)).2

/-- Bundled smooth maps on the actual open base domains of the core. -/
abbrev RawSmoothFamily := ∀ i : ι, C^n⟮I, baseDomain Z i; J, F⟯

/-- Independent compatibility of local smooth coordinates uses the actual core transition maps. -/
def Compatible (f : RawSmoothFamily I J Z n) : Prop :=
  ∀ (i j : ι) (x : B) (hi : x ∈ Z.baseSet i) (hj : x ∈ Z.baseSet j),
    f j ⟨x, hj⟩ = Z.coordChange i j x (f i ⟨x, hi⟩)

/-- Smooth local families with independently stated actual transition compatibility. -/
def SmoothFamily := {f : RawSmoothFamily I J Z n // Compatible I J Z n f}

/-- A compatible local family determines a dependent section using the core's chosen chart only pointwise. -/
def familySection (f : SmoothFamily I J Z n) (x : B) : Z.Fiber x :=
  f.val (Z.indexAt x) ⟨x, Z.mem_baseSet_at x⟩

/-- The constructed section has the prescribed coordinates in every available chart, independently of the pointwise chosen chart. -/
theorem localTriv_familySection (f : SmoothFamily I J Z n) (i : ι) (x : B)
    (hx : x ∈ Z.baseSet i) :
    Z.localTriv i (sectionGraph Z (familySection I J Z n f) x) = (x, f.val i ⟨x, hx⟩) := by
  apply Prod.ext
  · rfl
  · exact (f.property (Z.indexAt x) i x (Z.mem_baseSet_at x) hx).symm

/-- Coordinates of any actual dependent section satisfy the genuine core transition identity wherever both charts are defined. -/
theorem sectionCoordinate_compatible (s : ∀ x : B, Z.Fiber x) (i j : ι) (x : B)
    (hi : x ∈ Z.baseSet i) (hj : x ∈ Z.baseSet j) :
    sectionCoordinate Z s j ⟨x, hj⟩ =
      Z.coordChange i j x (sectionCoordinate Z s i ⟨x, hi⟩) := by
  exact (Z.coordChange_comp (Z.indexAt x) i j x
    ⟨⟨Z.mem_baseSet_at x, hi⟩, hj⟩ (s x)).symm

/-- The selected chart coordinate of an actual section is its actual fiber value. -/
theorem sectionCoordinate_indexAt (s : ∀ x : B, Z.Fiber x) (x : B) :
    sectionCoordinate Z s (Z.indexAt x) ⟨x, Z.mem_baseSet_at x⟩ = s x :=
  Z.coordChange_self (Z.indexAt x) x (Z.mem_baseSet_at x) (s x)

/-- Smoothness is defined independently by the actual total-space graph of a dependent section. -/
def SmoothSection := {s : ∀ x : B, Z.Fiber x // ContMDiff I (I.prod J) n (sectionGraph Z s)}

variable [IsManifold I n B] [IsManifold J n F]
  (hchange : ∀ i j, ContMDiffOn (I.prod J) J n
    (fun p : B × F => Z.coordChange i j p.1 p.2)
    ((Z.baseSet i ∩ Z.baseSet j) ×ˢ univ))

include hchange in
/-- A graph-smooth section has actual smooth coordinates on every open base domain. -/
theorem contMDiff_sectionCoordinate (s : SmoothSection I J Z n) (i : ι) :
    ContMDiff I J n (sectionCoordinate Z s.val i) := by
  have hgraph : ContMDiff I (I.prod J) n
      (fun x : baseDomain Z i => sectionGraph Z s.val x) :=
    s.property.comp contMDiff_subtype_val
  have hlocal := (SmoothCocycleBundle.contMDiffOn_localTriv I J Z hchange i).comp_contMDiff hgraph (fun x => x.property)
  exact hlocal.snd

include hchange in
/-- Local compatible smooth coordinates give a genuinely smooth total-space section graph. -/
theorem contMDiff_familySection (f : SmoothFamily I J Z n) :
    ContMDiff I (I.prod J) n (sectionGraph Z (familySection I J Z n f)) := by
  intro x
  let i := Z.indexAt x
  have hx : x ∈ Z.baseSet i := Z.mem_baseSet_at x
  have hp : ContMDiff I (I.prod J) n
      (fun y : baseDomain Z i => (y.val, f.val i y)) :=
    contMDiff_subtype_val.prodMk (f.val i).contMDiff
  have hs := (SmoothCocycleBundle.contMDiffOn_localTriv_symm I J Z hchange i).comp_contMDiff hp (fun y => (Z.localTriv i).mem_target.mpr y.property)
  have he : (fun y : baseDomain Z i =>
      (Z.localTriv i).toOpenPartialHomeomorph.symm (y.val, f.val i y)) =
      (fun y : baseDomain Z i => sectionGraph Z (familySection I J Z n f) y) := by
    funext y
    rw [← localTriv_familySection I J Z n f i y y.property]
    exact (Z.localTriv i).toOpenPartialHomeomorph.left_inv y.property
  simp only [Function.comp_def] at hs
  rw [he] at hs
  exact contMDiffAt_subtype_iff.mp (hs ⟨x, hx⟩)


include hchange in
/-- Actual graph smoothness is equivalent to smoothness of the independently defined local section coordinates on every open base domain. -/
theorem contMDiff_graph_iff (s : ∀ x : B, Z.Fiber x) :
    ContMDiff I (I.prod J) n (sectionGraph Z s) ↔
      ∀ i, ContMDiff I J n (sectionCoordinate Z s i) := by
  constructor
  · intro hs i
    exact contMDiff_sectionCoordinate I J Z n hchange ⟨s, hs⟩ i
  · intro hs
    let f : SmoothFamily I J Z n := ⟨fun i => ⟨sectionCoordinate Z s i, hs i⟩,
      sectionCoordinate_compatible Z s⟩
    have he : familySection I J Z n f = s := by
      funext x
      exact sectionCoordinate_indexAt Z s x
    have hc := contMDiff_familySection I J Z n hchange f
    rw [he] at hc
    exact hc

/-- Genuine graph-smooth dependent sections correspond exactly to independently compatible smooth local families. -/
def sectionEquiv : SmoothSection I J Z n ≃ SmoothFamily I J Z n where
  toFun s := ⟨fun i => ⟨sectionCoordinate Z s.val i,
    contMDiff_sectionCoordinate I J Z n hchange s i⟩,
    sectionCoordinate_compatible Z s.val⟩
  invFun f := ⟨familySection I J Z n f, contMDiff_familySection I J Z n hchange f⟩
  left_inv s := by
    apply Subtype.ext
    funext x
    exact sectionCoordinate_indexAt Z s.val x
  right_inv f := by
    apply Subtype.ext
    funext i
    apply ContMDiffMap.ext
    intro x
    exact congrArg Prod.snd (localTriv_familySection I J Z n f i x x.property)

/-- The section correspondence reads exactly the actual core-trivialization fiber coordinate of each graph. -/
theorem sectionEquiv_apply (s : SmoothSection I J Z n) (i : ι) (x : baseDomain Z i) :
    (sectionEquiv I J Z n hchange s).val i x =
      sectionCoordinate Z s.val i x := rfl

/-- The inverse correspondence uses the selected local field value only pointwise, without any regularity assumption on the index selection. -/
theorem sectionEquiv_symm_apply (f : SmoothFamily I J Z n) (x : B) :
    ((sectionEquiv I J Z n hchange).symm f).val x =
      f.val (Z.indexAt x) ⟨x, Z.mem_baseSet_at x⟩ := rfl

/-- The reconstructed graph has the exact prescribed local coordinates in every available trivialization. -/
theorem sectionEquiv_symm_localTriv (f : SmoothFamily I J Z n) (i : ι) (x : B)
    (hx : x ∈ Z.baseSet i) :
    Z.localTriv i (sectionGraph Z ((sectionEquiv I J Z n hchange).symm f).val x) =
      (x, f.val i ⟨x, hx⟩) := localTriv_familySection I J Z n f i x hx

include hchange in
/-- Every compatible smooth local family determines exactly one graph-smooth dependent section with those actual local coordinates. -/
theorem existsUnique_section (f : SmoothFamily I J Z n) :
    ∃! s : SmoothSection I J Z n, ∀ (i : ι) (x : baseDomain Z i),
      sectionCoordinate Z s.val i x = f.val i x := by
  refine ⟨(sectionEquiv I J Z n hchange).symm f, ?_, ?_⟩
  · intro i x
    exact congrArg Prod.snd (localTriv_familySection I J Z n f i x x.property)
  · intro s hs
    apply (sectionEquiv I J Z n hchange).injective
    rw [Equiv.apply_symm_apply]
    apply Subtype.ext
    funext i
    apply ContMDiffMap.ext
    intro x
    exact hs i x

end FoliationQM.SmoothCocycleSections
