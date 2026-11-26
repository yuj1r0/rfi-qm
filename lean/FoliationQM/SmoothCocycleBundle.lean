module
public import Mathlib.Topology.FiberBundle.Basic
public import Mathlib.Geometry.Manifold.ContMDiff.Atlas
public import Mathlib.Geometry.Manifold.LocalDiffeomorph

/-!
# Smooth atlases on actual cocycle bundle total spaces

Source: smooth bundle infrastructure for the supplied-transition interpretation
of v13 `prop:takabayasi`. The input is an actual `FiberBundleCore`, independently
specified base and fiber atlases, and smoothness of the actual fiber coordinate
changes on their precise overlap domains. The existing core-generated total
space topology is retained.

The total atlas consists of genuine bundle trivializations followed by actual
base-and-fiber product charts. Actual overlap formulas prove its manifold
compatibility. Smoothness of each original trivialization and its inverse is
then derived through maximal-atlas charts. These give genuine partial
diffeomorphisms and local criteria for maps into the actual total space.
The atlas is an explicit definition used locally; no total-space smoothness
conclusion or smooth chart-index selection is included in the hypotheses.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold Topology
open Bundle Set Function StructureGroupoid
namespace FoliationQM.SmoothCocycleBundle

section Atlas
variable (H H' : Type*) [TopologicalSpace H] [TopologicalSpace H']
  {B F ι : Type*} [TopologicalSpace B] [TopologicalSpace F]
  [ChartedSpace H B] [ChartedSpace H' F] (Z : FiberBundleCore ι B F)

/-- The actual core total space uses the atlas of genuine bundle trivializations followed by the independent base-and-fiber product charts, retaining its existing topology. -/
@[instance_reducible]
def totalChartedSpace : ChartedSpace (ModelProd H H') Z.TotalSpace where
  atlas := {e | ∃ i, ∃ (c : OpenPartialHomeomorph (B × F) (ModelProd H H')),
    c ∈ atlas (ModelProd H H') (B × F) ∧ e = (Z.localTriv i).toOpenPartialHomeomorph.trans c}
  chartAt p := (Z.localTrivAt p.proj).toOpenPartialHomeomorph.trans
    (chartAt (ModelProd H H') (Z.localTrivAt p.proj p))
  mem_chart_source p := ⟨Z.mk_mem_localTrivAt_source p.proj p.2,
    mem_chart_source (ModelProd H H') (Z.localTrivAt p.proj p)⟩
  chart_mem_atlas p := ⟨Z.indexAt p.proj, _,
    chart_mem_atlas (ModelProd H H') (Z.localTrivAt p.proj p), rfl⟩
end Atlas
attribute [local instance] totalChartedSpace

section Smooth
variable {E E' H H' B F ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H] [TopologicalSpace H']
  (I : ModelWithCorners ℝ E H) (J : ModelWithCorners ℝ E' H')
  [TopologicalSpace B] [TopologicalSpace F] [ChartedSpace H B] [ChartedSpace H' F]
  (Z : FiberBundleCore ι B F) {n : WithTop ℕ∞}
  (hchange : ∀ i j, ContMDiffOn (I.prod J) J n
    (fun p : B × F => Z.coordChange i j p.1 p.2)
    ((Z.baseSet i ∩ Z.baseSet j) ×ˢ univ))

include hchange

/-- Actual changes between core trivializations are smooth on their precise domains, derived from the supplied overlap coordinate-change regularity. -/
theorem contMDiffOn_trivTransition (i j : ι) :
    ContMDiffOn (I.prod J) (I.prod J) n
      ((Z.localTriv i).toOpenPartialHomeomorph.symm.trans
        (Z.localTriv j).toOpenPartialHomeomorph)
      ((Z.localTriv i).toOpenPartialHomeomorph.symm.trans
        (Z.localTriv j).toOpenPartialHomeomorph).source := by
  have he := Z.localTrivAsPartialEquiv_trans i j
  have hs : ((Z.localTriv i).toOpenPartialHomeomorph.symm.trans
        (Z.localTriv j).toOpenPartialHomeomorph).source =
      ((Z.baseSet i ∩ Z.baseSet j) ×ˢ univ) := he.source_eq
  rw [hs]
  apply (contMDiffOn_fst.prodMk (hchange i j)).congr
  intro p hp
  exact he.eqOn (by rwa [he.source_eq])

variable [IsManifold I n B] [IsManifold J n F]

/-- The explicit core total-space atlas is a manifold to the supplied order when the base, fiber, and actual overlap coordinate changes have that regularity. -/
theorem isManifold_total : IsManifold (I.prod J) n Z.TotalSpace where
  compatible := by
    rintro e e' ⟨i,c,hc,rfl⟩ ⟨j,d,hd,rfl⟩
    have hh := symm_trans_trans_mem_contDiffGroupoid_of_contMDiffOn
      (StructureGroupoid.subset_maximalAtlas (G := contDiffGroupoid n (I.prod J)) hc)
      (StructureGroupoid.subset_maximalAtlas (G := contDiffGroupoid n (I.prod J)) hd)
      (contMDiffOn_trivTransition I J Z hchange i j)
      (contMDiffOn_trivTransition I J Z hchange j i)
    simpa only [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
      OpenPartialHomeomorph.symm_symm, OpenPartialHomeomorph.trans_assoc] using hh

/-- An actual core trivialization is smooth at each point of its actual source for the independently constructed total-space atlas. -/
theorem contMDiffAt_localTriv (i : ι) (p : Z.TotalSpace)
    (hp : p ∈ (Z.localTriv i).source) :
    ContMDiffAt (I.prod J) (I.prod J) n (Z.localTriv i) p := by
  let := isManifold_total I J Z hchange
  let c := chartAt (ModelProd H H') (Z.localTriv i p)
  let a := (Z.localTriv i).toOpenPartialHomeomorph.trans c
  have hcm : c ∈ IsManifold.maximalAtlas (I.prod J) n (B × F) :=
    IsManifold.chart_mem_maximalAtlas (Z.localTriv i p)
  have ham : a ∈ IsManifold.maximalAtlas (I.prod J) n Z.TotalSpace :=
    StructureGroupoid.subset_maximalAtlas (G := contDiffGroupoid n (I.prod J))
      (show a ∈ atlas (ModelProd H H') Z.TotalSpace from
        ⟨i, c, chart_mem_atlas (ModelProd H H') (Z.localTriv i p), rfl⟩)
  have hcp : Z.localTriv i p ∈ c.source := mem_chart_source _ _
  have hap : p ∈ a.source := ⟨hp, hcp⟩
  have hc := contMDiffAt_symm_of_mem_maximalAtlas hcm (c.map_source hcp)
  have ha := contMDiffAt_of_mem_maximalAtlas ham hap
  have h := hc.comp p ha
  apply h.congr_of_eventuallyEq
  filter_upwards [a.open_source.mem_nhds hap] with q hq
  exact (c.left_inv hq.2).symm

/-- Every actual core trivialization is smooth on its actual source domain. -/
theorem contMDiffOn_localTriv (i : ι) :
    ContMDiffOn (I.prod J) (I.prod J) n (Z.localTriv i) (Z.localTriv i).source :=
  fun p hp => (contMDiffAt_localTriv I J Z hchange i p hp).contMDiffWithinAt

/-- The actual inverse of a core trivialization is smooth at each point of its actual target. -/
theorem contMDiffAt_localTriv_symm (i : ι) (q : B × F)
    (hq : q ∈ (Z.localTriv i).target) :
    ContMDiffAt (I.prod J) (I.prod J) n
      (Z.localTriv i).toOpenPartialHomeomorph.symm q := by
  let := isManifold_total I J Z hchange
  let c := chartAt (ModelProd H H') q
  let a := (Z.localTriv i).toOpenPartialHomeomorph.trans c
  have hcm : c ∈ IsManifold.maximalAtlas (I.prod J) n (B × F) :=
    IsManifold.chart_mem_maximalAtlas q
  have ham : a ∈ IsManifold.maximalAtlas (I.prod J) n Z.TotalSpace :=
    StructureGroupoid.subset_maximalAtlas (G := contDiffGroupoid n (I.prod J))
      (show a ∈ atlas (ModelProd H H') Z.TotalSpace from
        ⟨i, c, chart_mem_atlas (ModelProd H H') q, rfl⟩)
  have hcq : q ∈ c.source := mem_chart_source _ _
  have haq : c q ∈ a.target := ⟨c.map_source hcq, by
    change c.symm (c q) ∈ (Z.localTriv i).target
    rwa [c.left_inv hcq]⟩
  have hc := contMDiffAt_of_mem_maximalAtlas hcm hcq
  have ha := contMDiffAt_symm_of_mem_maximalAtlas ham haq
  have h := ha.comp q hc
  apply h.congr_of_eventuallyEq
  filter_upwards [c.open_source.mem_nhds hcq] with y hy
  change (Z.localTriv i).toOpenPartialHomeomorph.symm y =
    (Z.localTriv i).toOpenPartialHomeomorph.symm (c.symm (c y))
  rw [c.left_inv hy]

/-- Every actual inverse core trivialization is smooth on its actual target domain. -/
theorem contMDiffOn_localTriv_symm (i : ι) :
    ContMDiffOn (I.prod J) (I.prod J) n (Z.localTriv i).toOpenPartialHomeomorph.symm
      (Z.localTriv i).target :=
  fun q hq => (contMDiffAt_localTriv_symm I J Z hchange i q hq).contMDiffWithinAt

/-- The actual core bundle projection is smooth for the independently constructed total-space and supplied base atlases. -/
theorem contMDiff_proj : ContMDiff (I.prod J) I n Z.proj := by
  intro p
  exact (contMDiffAt_localTriv I J Z hchange (Z.indexAt p.proj) p
    (Z.mem_baseSet_at p.proj)).fst

/-- Each original core trivialization, with its actual source, target, and inverse, is a genuine partial diffeomorphism. -/
def localTrivDiffeomorph (i : ι) :
    PartialDiffeomorph (I.prod J) (I.prod J) Z.TotalSpace (B × F) n where
  toPartialEquiv := (Z.localTriv i).toPartialEquiv
  open_source := (Z.localTriv i).open_source
  open_target := (Z.localTriv i).open_target
  contMDiffOn_toFun := contMDiffOn_localTriv I J Z hchange i
  contMDiffOn_invFun := contMDiffOn_localTriv_symm I J Z hchange i

/-- The partial diffeomorphism retains exactly the original core trivialization as its topological map. -/
theorem localTrivDiffeomorph_toOpenPartialHomeomorph (i : ι) :
    (localTrivDiffeomorph I J Z hchange i).toOpenPartialHomeomorph =
      (Z.localTriv i).toOpenPartialHomeomorph := rfl

variable {E₀ H₀ M : Type*} [NormedAddCommGroup E₀] [NormedSpace ℝ E₀]
  [TopologicalSpace H₀] {K : ModelWithCorners ℝ E₀ H₀}
  [TopologicalSpace M] [ChartedSpace H₀ M]

/-- Within any subset, smoothness of a map into the total space is equivalent to smoothness in any containing actual bundle trivialization; base continuity is derived from its first coordinate. -/
theorem contMDiffWithinAt_iff_localTriv {f : M → Z.TotalSpace} {s : Set M} {x : M}
    (i : ι) (hx : f x ∈ (Z.localTriv i).source) :
    ContMDiffWithinAt K (I.prod J) n f s x ↔
      ContMDiffWithinAt K (I.prod J) n ((Z.localTriv i) ∘ f) s x := by
  constructor
  · intro hf
    exact (contMDiffAt_localTriv I J Z hchange i (f x) hx).comp_contMDiffWithinAt x hf
  · intro hf
    have hback := (contMDiffAt_localTriv_symm I J Z hchange i
      ((Z.localTriv i) (f x)) ((Z.localTriv i).map_source hx)).comp_contMDiffWithinAt x hf
    apply hback.congr_of_eventuallyEq
    · have hproj : ContinuousWithinAt (Z.proj ∘ f) s x := hf.continuousWithinAt.fst
      have hs := hproj ((Z.isOpen_baseSet i).mem_nhds hx)
      filter_upwards [hs] with y hy
      exact ((Z.localTriv i).left_inv hy).symm
    · exact ((Z.localTriv i).left_inv hx).symm

/-- At a point, smoothness into the actual total space is equivalent to smoothness in any actual bundle trivialization containing the image. -/
theorem contMDiffAt_iff_localTriv {f : M → Z.TotalSpace} {x : M}
    (i : ι) (hx : f x ∈ (Z.localTriv i).source) :
    ContMDiffAt K (I.prod J) n f x ↔
      ContMDiffAt K (I.prod J) n ((Z.localTriv i) ∘ f) x := by
  simpa only [contMDiffWithinAt_univ] using
    (contMDiffWithinAt_iff_localTriv I J Z hchange (s := univ) i hx)

/-- On a subset mapped into one actual trivialization source, smoothness into the total space is exactly smoothness of the actual local product expression. -/
theorem contMDiffOn_iff_localTriv {f : M → Z.TotalSpace} {s : Set M}
    (i : ι) (hs : MapsTo f s (Z.localTriv i).source) :
    ContMDiffOn K (I.prod J) n f s ↔
      ContMDiffOn K (I.prod J) n ((Z.localTriv i) ∘ f) s :=
  forall₂_congr (fun _x hx => contMDiffWithinAt_iff_localTriv I J Z hchange i (hs hx))

end Smooth
end FoliationQM.SmoothCocycleBundle
