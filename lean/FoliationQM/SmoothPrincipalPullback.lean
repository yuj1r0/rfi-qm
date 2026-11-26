module
public import FoliationQM.SmoothPullbackChartedSpace

/-!
# Smooth compatibility of the principal fiber-product charts

For the frame-bundle construction in v13 `prop:takabayasi`, each change of
pullback trivializations keeps the new base coordinate and reads the group
coordinate from the original smooth chart change. This makes the actual
fiber product a manifold of the same differentiability order and makes
its geometric principal charts smooth in both directions.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Bundle StructureGroupoid
open scoped Manifold Topology
namespace FoliationQM.SmoothPrincipalPullback
open GeometricPrincipalPullback SmoothPullbackChartedSpace

variable {EX EB EG ET HX HB HG HT X B G T ι : Type*}
  [NormedAddCommGroup EX] [NormedSpace ℝ EX] [TopologicalSpace HX]
  [NormedAddCommGroup EB] [NormedSpace ℝ EB] [TopologicalSpace HB]
  [NormedAddCommGroup EG] [NormedSpace ℝ EG] [TopologicalSpace HG]
  [NormedAddCommGroup ET] [NormedSpace ℝ ET] [TopologicalSpace HT]
  [TopologicalSpace X] [ChartedSpace HX X] [TopologicalSpace B] [ChartedSpace HB B]
  [TopologicalSpace G] [ChartedSpace HG G] [Group G] [TopologicalSpace T] [ChartedSpace HT T]
  {IX : ModelWithCorners ℝ EX HX} {IB : ModelWithCorners ℝ EB HB}
  {J : ModelWithCorners ℝ EG HG} {K : ModelWithCorners ℝ ET HT} {n : WithTop ℕ∞}
  {proj : T → B} {A : GeometricPrincipalAtlas.Data (G := G) proj ι}
  (f : C(X, B)) (hf : ContMDiff IX IB n f) (S : GeometricPrincipalSmoothAtlas.Data IB J K A n)

include hf S

/-- The joint product-coordinate change is smooth on its true source by composition
with the original smooth principal maps in both directions at the image base point. -/
theorem contMDiffOn_change (i j : ι) : ContMDiffOn (IX.prod J) (IX.prod J) n
    ((trivialization f A i).toOpenPartialHomeomorph.symm.trans (trivialization f A j).toOpenPartialHomeomorph)
    ((trivialization f A i).toOpenPartialHomeomorph.symm.trans (trivialization f A j).toOpenPartialHomeomorph).source := by
  rw [change_source]
  have hpair : ContMDiff (IX.prod J) (IB.prod J) n (fun z : X × G => (f z.1, z.2)) :=
    (hf.comp contMDiff_fst).prodMk contMDiff_snd
  have hlocal : ContMDiffOn (IX.prod J) (IX.prod J) n
      (fun z : X × G => (z.1, (A.triv j ((A.triv i).toOpenPartialHomeomorph.symm (f z.1, z.2))).2))
      ((f ⁻¹' ((A.triv i).baseSet ∩ (A.triv j).baseSet)) ×ˢ univ) := by
    intro z hz
    have hb := (A.triv i).proj_symm_apply' (x := z.2) hz.1.1
    have hinv := (S.contMDiffAt_symm i (f z.1, z.2) hz.1.1).comp z hpair.contMDiffAt
    have ht := (S.contMDiffAt_triv j _ (hb.symm ▸ hz.1.2)).comp z hinv
    exact (contMDiff_fst.contMDiffAt.prodMk ht.snd).contMDiffWithinAt
  exact hlocal.congr (fun z hz => change_apply f A i j z hz.1.1 hz.1.2)

variable [IsManifold IX n X] [IsManifold J n G]

/-- The actual fiber product, with its charted subtype topology and base/group product model,
is a manifold to the joint order of the base map and the original principal charts. -/
theorem isManifold_total :
    letI := chartedSpace HX HG f A
    IsManifold (IX.prod J) n (Total f proj) := by
  let := chartedSpace HX HG f A
  refine { compatible := ?_ }
  rintro e e' ⟨i, c, hc, rfl⟩ ⟨j, d, hd, rfl⟩
  have h := symm_trans_trans_mem_contDiffGroupoid_of_contMDiffOn
    (StructureGroupoid.subset_maximalAtlas (G := contDiffGroupoid n (IX.prod J)) hc)
    (StructureGroupoid.subset_maximalAtlas (G := contDiffGroupoid n (IX.prod J)) hd)
    (contMDiffOn_change f hf S i j) (contMDiffOn_change f hf S j i)
  change (((trivialization f A i).toOpenPartialHomeomorph.trans c).symm.trans
    ((trivialization f A j).toOpenPartialHomeomorph.trans d)) ∈ contDiffGroupoid n (IX.prod J)
  simpa only [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
    OpenPartialHomeomorph.symm_symm, OpenPartialHomeomorph.trans_assoc] using h

/-- The geometric pullback trivialization is smooth on its actual source in the constructed atlas. -/
theorem contMDiffOn_triv (i : ι) :
    letI := chartedSpace HX HG f A
    ContMDiffOn (IX.prod J) (IX.prod J) n (trivialization f A i) (trivialization f A i).source := by
  let := chartedSpace HX HG f A
  let := isManifold_total f hf S
  intro p hp
  let v := trivialization f A i
  let c := chartAt (ModelProd HX HG) (v p)
  let a := v.toOpenPartialHomeomorph.trans c
  have hc : c ∈ IsManifold.maximalAtlas (IX.prod J) n (X × G) := IsManifold.chart_mem_maximalAtlas (v p)
  have ha : a ∈ IsManifold.maximalAtlas (IX.prod J) n (Total f proj) :=
    StructureGroupoid.subset_maximalAtlas (G := contDiffGroupoid n (IX.prod J))
      (show a ∈ _root_.atlas (ModelProd HX HG) (Total f proj) from
        ⟨i, c, chart_mem_atlas _ (v p), rfl⟩)
  have hvp : v p ∈ c.source := mem_chart_source _ _
  have hap : p ∈ a.source := ⟨hp, hvp⟩
  have hback := contMDiffAt_symm_of_mem_maximalAtlas hc (c.map_source hvp)
  have hforward := contMDiffAt_of_mem_maximalAtlas ha hap
  apply ContMDiffAt.contMDiffWithinAt
  apply (hback.comp p hforward).congr_of_eventuallyEq
  filter_upwards [a.open_source.mem_nhds hap] with q hq
  exact (c.left_inv hq.2).symm

/-- The inverse geometric pullback trivialization is smooth on its actual target. -/
theorem contMDiffOn_symm (i : ι) :
    letI := chartedSpace HX HG f A
    ContMDiffOn (IX.prod J) (IX.prod J) n (trivialization f A i).toOpenPartialHomeomorph.symm
      (trivialization f A i).target := by
  let := chartedSpace HX HG f A
  let := isManifold_total f hf S
  intro q hq
  let v := trivialization f A i
  let c := chartAt (ModelProd HX HG) q
  let a := v.toOpenPartialHomeomorph.trans c
  have hc : c ∈ IsManifold.maximalAtlas (IX.prod J) n (X × G) := IsManifold.chart_mem_maximalAtlas q
  have ha : a ∈ IsManifold.maximalAtlas (IX.prod J) n (Total f proj) :=
    StructureGroupoid.subset_maximalAtlas (G := contDiffGroupoid n (IX.prod J))
      (show a ∈ _root_.atlas (ModelProd HX HG) (Total f proj) from
        ⟨i, c, chart_mem_atlas _ q, rfl⟩)
  have hcq : q ∈ c.source := mem_chart_source _ _
  have haq : c q ∈ a.target := ⟨c.map_source hcq, by
    change c.symm (c q) ∈ v.target
    rw [c.left_inv hcq]
    exact hq⟩
  have hforward := contMDiffAt_of_mem_maximalAtlas hc hcq
  have hback := contMDiffAt_symm_of_mem_maximalAtlas ha haq
  apply ContMDiffAt.contMDiffWithinAt
  apply (hback.comp q hforward).congr_of_eventuallyEq
  filter_upwards [c.open_source.mem_nhds hcq] with y hy
  change v.toOpenPartialHomeomorph.symm y = v.toOpenPartialHomeomorph.symm (c.symm (c y))
  rw [c.left_inv hy]

/-- Both chart directions supply a smooth principal atlas on the actual fiber product. -/
theorem smoothAtlas :
    letI := chartedSpace HX HG f A
    GeometricPrincipalSmoothAtlas.Data IX J (IX.prod J) (GeometricPrincipalPullback.atlas f A) n := by
  let := chartedSpace HX HG f A
  exact ⟨contMDiffOn_triv f hf S, contMDiffOn_symm f hf S⟩

end FoliationQM.SmoothPrincipalPullback
