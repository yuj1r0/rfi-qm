module
public import FoliationQM.GeometricPrincipalSmoothAtlas
public import FoliationQM.SmoothCocycleBundle

/-!
# Direct smooth atlases on independent geometric principal bundles

Source scope: the geometric principal-frame bridge underlying v13
`prop:takabayasi`. The original total space, topology, projection and
principal trivializations are supplied independently. Its atlas is
constructed directly by composing those actual trivializations with the
original base/group product charts. Smoothness of the actual extracted
transition functions proves manifold compatibility and smoothness of
the original trivializations and their inverses on their genuine domains.

The original topology is retained. No atlas is transported through a
desired reconstruction equivalence, and no smoothness of the chart-index
selection or existence of an arbitrary geometric Spin lift is assumed.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Function Bundle Topology StructureGroupoid
open scoped Manifold Topology
namespace FoliationQM.GeometricPrincipalManifold

section Atlas
variable (HB HG : Type*) [TopologicalSpace HB] [TopologicalSpace HG]
  {B P G : Type*} [TopologicalSpace B] [TopologicalSpace P]
  [TopologicalSpace G] [Group G] [ChartedSpace HB B] [ChartedSpace HG G]
  {proj : P → B} {ι : Type*} (A : GeometricPrincipalAtlas.Data (G := G) proj ι)

/-- The direct principal atlas consists of the original geometric trivializations followed by actual base/group product charts, with the original total-space topology unchanged. -/
@[instance_reducible]
def chartedSpace : ChartedSpace (ModelProd HB HG) P where
  atlas := {e | ∃ i, ∃ (c : OpenPartialHomeomorph (B × G) (ModelProd HB HG)),
    c ∈ atlas (ModelProd HB HG) (B × G) ∧ e = (A.triv i).toOpenPartialHomeomorph.trans c}
  chartAt p :=
    let i := Classical.choose (A.covers (proj p))
    (A.triv i).toOpenPartialHomeomorph.trans (chartAt (ModelProd HB HG) (A.triv i p))
  mem_chart_source p := ⟨(A.triv _).mem_source.mpr (Classical.choose_spec (A.covers (proj p))),
    mem_chart_source (ModelProd HB HG) (A.triv (Classical.choose (A.covers (proj p))) p)⟩
  chart_mem_atlas p := ⟨Classical.choose (A.covers (proj p)), _,
    chart_mem_atlas (ModelProd HB HG) (A.triv (Classical.choose (A.covers (proj p))) p), rfl⟩

end Atlas

section Transition
variable {B P G : Type*} [TopologicalSpace B] [TopologicalSpace P]
  [TopologicalSpace G] [Group G]
  {proj : P → B} {ι : Type*} (A : GeometricPrincipalAtlas.Data (G := G) proj ι)

/-- The true source of a change between independent principal trivializations is exactly the common base domain times the whole group. -/
theorem trivTransition_source (i j : ι) :
    ((A.triv i).toOpenPartialHomeomorph.symm.trans (A.triv j).toOpenPartialHomeomorph).source =
      ((A.triv i).baseSet ∩ (A.triv j).baseSet) ×ˢ (univ : Set G) := by
  ext p
  change (p ∈ (A.triv i).target ∧
    (A.triv i).toOpenPartialHomeomorph.symm p ∈ (A.triv j).source) ↔ _
  constructor
  · rintro ⟨hi, hj⟩
    have hi' := (A.triv i).mem_target.mp hi
    have hj' := (A.triv j).mem_source.mp hj
    rw [(A.triv i).proj_symm_apply' hi'] at hj'
    exact ⟨⟨hi', hj'⟩, mem_univ _⟩
  · rintro ⟨⟨hi, hj⟩, _⟩
    refine ⟨(A.triv i).mem_target.mpr hi, (A.triv j).mem_source.mpr ?_⟩
    rw [(A.triv i).proj_symm_apply' hi]
    exact hj

/-- Actual independent principal chart changes are literal left multiplication by the geometrically extracted transition on the genuine pair overlap. -/
theorem trivTransition_apply (i j : ι) (p : B × G)
    (hi : p.1 ∈ (A.triv i).baseSet) (hj : p.1 ∈ (A.triv j).baseSet) :
    (A.triv j) ((A.triv i).toOpenPartialHomeomorph.symm p) =
      (p.1, A.transition i j p.1 * p.2) := by
  have hb := (A.triv i).proj_symm_apply' (x := p.2) hi
  have hqj : proj ((A.triv i).toOpenPartialHomeomorph.symm p) ∈ (A.triv j).baseSet := by
    rw [hb]
    exact hj
  apply Prod.ext
  · exact ((A.triv j).coe_fst' hqj).trans hb
  · have h := A.change_coordinate i j ((A.triv i).toOpenPartialHomeomorph.symm p)
      (by rw [hb]; exact hi) hqj
    rw [hb, (A.triv i).apply_symm_apply' hi] at h
    exact h

end Transition

section Smooth
variable {EB EG HB HG B G P : Type*}
  [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [TopologicalSpace HB] [TopologicalSpace HG]
  (I : ModelWithCorners ℝ EB HB) (J : ModelWithCorners ℝ EG HG)
  [TopologicalSpace B] [ChartedSpace HB B]
  [TopologicalSpace G] [ChartedSpace HG G] [Group G]
  [TopologicalSpace P] {proj : P → B} {ι : Type*}
  (A : GeometricPrincipalAtlas.Data (G := G) proj ι) {n : WithTop ℕ∞}
  (htransition : ∀ i j, ContMDiffOn I J n (A.transition i j)
    ((A.triv i).baseSet ∩ (A.triv j).baseSet)) [ContMDiffMul J n G]

include htransition

/-- Smoothness of the actual geometric transition functions proves joint smoothness of the genuine changes between original principal trivializations on their exact overlap domains. -/
theorem contMDiffOn_trivTransition (i j : ι) :
    ContMDiffOn (I.prod J) (I.prod J) n
      ((A.triv i).toOpenPartialHomeomorph.symm.trans (A.triv j).toOpenPartialHomeomorph)
      ((A.triv i).toOpenPartialHomeomorph.symm.trans (A.triv j).toOpenPartialHomeomorph).source := by
  rw [trivTransition_source]
  have ht : ContMDiffOn (I.prod J) J n (fun p : B × G => A.transition i j p.1)
      (((A.triv i).baseSet ∩ (A.triv j).baseSet) ×ˢ univ) :=
    (htransition i j).comp contMDiff_fst.contMDiffOn (fun _ hx => hx.1)
  have hm := (contMDiff_mul J n).comp_contMDiffOn (ht.prodMk contMDiff_snd.contMDiffOn)
  apply (contMDiffOn_fst.prodMk hm).congr
  intro p hp
  exact trivTransition_apply A i j p hp.1.1 hp.1.2

variable [IsManifold I n B]

/-- The directly constructed original-trivialization atlas is a manifold of the supplied order, with compatibility proved from actual independent principal coordinate changes. -/
theorem isManifold :
    letI := chartedSpace HB HG A
    IsManifold (I.prod J) n P := by
  let := chartedSpace HB HG A
  refine { compatible := ?_ }
  rintro e e' ⟨i, c, hc, rfl⟩ ⟨j, d, hd, rfl⟩
  have hh := symm_trans_trans_mem_contDiffGroupoid_of_contMDiffOn
    (StructureGroupoid.subset_maximalAtlas (G := contDiffGroupoid n (I.prod J)) hc)
    (StructureGroupoid.subset_maximalAtlas (G := contDiffGroupoid n (I.prod J)) hd)
    (contMDiffOn_trivTransition I J A htransition i j)
    (contMDiffOn_trivTransition I J A htransition j i)
  simpa only [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
    OpenPartialHomeomorph.symm_symm, OpenPartialHomeomorph.trans_assoc] using hh

/-- Each original principal trivialization is smooth at every point of its actual source for the atlas directly constructed from those same original charts. -/
theorem contMDiffAt_triv (i : ι) (p : P) (hp : proj p ∈ (A.triv i).baseSet) :
    letI := chartedSpace HB HG A
    ContMDiffAt (I.prod J) (I.prod J) n (A.triv i) p := by
  let := chartedSpace HB HG A
  let := isManifold I J A htransition
  let c := chartAt (ModelProd HB HG) (A.triv i p)
  let a := (A.triv i).toOpenPartialHomeomorph.trans c
  have hcm : c ∈ IsManifold.maximalAtlas (I.prod J) n (B × G) :=
    IsManifold.chart_mem_maximalAtlas (A.triv i p)
  have ham : a ∈ IsManifold.maximalAtlas (I.prod J) n P :=
    StructureGroupoid.subset_maximalAtlas (G := contDiffGroupoid n (I.prod J))
      (show a ∈ atlas (ModelProd HB HG) P from
        ⟨i, c, chart_mem_atlas (ModelProd HB HG) (A.triv i p), rfl⟩)
  have hcp : A.triv i p ∈ c.source := mem_chart_source _ _
  have hap : p ∈ a.source := ⟨(A.triv i).mem_source.mpr hp, hcp⟩
  have hc := contMDiffAt_symm_of_mem_maximalAtlas hcm (c.map_source hcp)
  have ha := contMDiffAt_of_mem_maximalAtlas ham hap
  apply (hc.comp p ha).congr_of_eventuallyEq
  filter_upwards [a.open_source.mem_nhds hap] with q hq
  exact (c.left_inv hq.2).symm

/-- Every actual original principal trivialization is smooth on its genuine source for the direct geometric atlas. -/
theorem contMDiffOn_triv (i : ι) :
    letI := chartedSpace HB HG A
    ContMDiffOn (I.prod J) (I.prod J) n (A.triv i) (A.triv i).source := by
  let := chartedSpace HB HG A
  intro p hp
  exact (contMDiffAt_triv I J A htransition i p ((A.triv i).mem_source.mp hp)).contMDiffWithinAt

/-- Each original inverse principal trivialization is smooth at every point of its genuine target for the directly constructed original total-space atlas. -/
theorem contMDiffAt_symm (i : ι) (q : B × G) (hq : q.1 ∈ (A.triv i).baseSet) :
    letI := chartedSpace HB HG A
    ContMDiffAt (I.prod J) (I.prod J) n (A.triv i).toOpenPartialHomeomorph.symm q := by
  let := chartedSpace HB HG A
  let := isManifold I J A htransition
  let c := chartAt (ModelProd HB HG) q
  let a := (A.triv i).toOpenPartialHomeomorph.trans c
  have hcm : c ∈ IsManifold.maximalAtlas (I.prod J) n (B × G) :=
    IsManifold.chart_mem_maximalAtlas q
  have ham : a ∈ IsManifold.maximalAtlas (I.prod J) n P :=
    StructureGroupoid.subset_maximalAtlas (G := contDiffGroupoid n (I.prod J))
      (show a ∈ atlas (ModelProd HB HG) P from
        ⟨i, c, chart_mem_atlas (ModelProd HB HG) q, rfl⟩)
  have hcq : q ∈ c.source := mem_chart_source _ _
  have haq : c q ∈ a.target := ⟨c.map_source hcq, by
    change c.symm (c q) ∈ (A.triv i).target
    rw [c.left_inv hcq]
    exact (A.triv i).mem_target.mpr hq⟩
  have hc := contMDiffAt_of_mem_maximalAtlas hcm hcq
  have ha := contMDiffAt_symm_of_mem_maximalAtlas ham haq
  apply (ha.comp q hc).congr_of_eventuallyEq
  filter_upwards [c.open_source.mem_nhds hcq] with y hy
  change (A.triv i).toOpenPartialHomeomorph.symm y =
    (A.triv i).toOpenPartialHomeomorph.symm (c.symm (c y))
  rw [c.left_inv hy]

/-- Every original inverse principal trivialization is smooth on its actual base/group target for the direct geometric atlas. -/
theorem contMDiffOn_symm (i : ι) :
    letI := chartedSpace HB HG A
    ContMDiffOn (I.prod J) (I.prod J) n (A.triv i).toOpenPartialHomeomorph.symm
      (A.triv i).target := by
  let := chartedSpace HB HG A
  intro q hq
  exact (contMDiffAt_symm I J A htransition i q ((A.triv i).mem_target.mp hq)).contMDiffWithinAt

/-- The actual direct principal atlas supplies genuine smooth-atlas data for the original geometric total space, after smoothness of both original chart directions has been proved. -/
theorem smoothAtlas :
    letI := chartedSpace HB HG A
    GeometricPrincipalSmoothAtlas.Data I J (I.prod J) A n := by
  let := chartedSpace HB HG A
  exact
    { smooth_triv := contMDiffOn_triv I J A htransition
      smooth_symm := contMDiffOn_symm I J A htransition }

end Smooth
end FoliationQM.GeometricPrincipalManifold
