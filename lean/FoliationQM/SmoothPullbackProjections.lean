module
public import FoliationQM.GeometricPrincipalPullback

/-!
# The smooth maps out of a principal fiber product

For the frame-bundle component of v13 `prop:takabayasi`, reconstruct
the map to the original total space in an actual chart. Its two chart
coordinates are the smooth image of the new base point and the original
group coordinate. This proves smoothness for any smooth principal
structure on the pulled charts, including the constructed product model.
-/

@[expose] public section
noncomputable section
open scoped Manifold Topology
namespace FoliationQM.SmoothPullbackProjections
open GeometricPrincipalPullback

variable {EX EB EG ET EZ HX HB HG HT HZ X B G T ι : Type*}
  [NormedAddCommGroup EX] [NormedSpace ℝ EX] [TopologicalSpace HX]
  [NormedAddCommGroup EB] [NormedSpace ℝ EB] [TopologicalSpace HB]
  [NormedAddCommGroup EG] [NormedSpace ℝ EG] [TopologicalSpace HG]
  [NormedAddCommGroup ET] [NormedSpace ℝ ET] [TopologicalSpace HT]
  [NormedAddCommGroup EZ] [NormedSpace ℝ EZ] [TopologicalSpace HZ]
  [TopologicalSpace X] [ChartedSpace HX X] [TopologicalSpace B] [ChartedSpace HB B]
  [TopologicalSpace G] [ChartedSpace HG G] [Group G] [TopologicalSpace T] [ChartedSpace HT T]
  {IX : ModelWithCorners ℝ EX HX} {IB : ModelWithCorners ℝ EB HB} {J : ModelWithCorners ℝ EG HG}
  {K : ModelWithCorners ℝ ET HT} {L : ModelWithCorners ℝ EZ HZ} {n : WithTop ℕ∞}
  {proj : T → B} {A : GeometricPrincipalAtlas.Data (G := G) proj ι}
  (f : C(X, B)) (hf : ContMDiff IX IB n f)
  (S : GeometricPrincipalSmoothAtlas.Data IB J K A n) [ChartedSpace HZ (Total f proj)]
  (M : GeometricPrincipalSmoothAtlas.Data IX J L (atlas f A) n)

include M in
/-- The first projection is smooth in the smooth principal structure on the fiber product. -/
theorem contMDiff_projection : ContMDiff L IX n (projection f proj) := M.contMDiff_proj

include M S hf in
/-- The projection to the original principal space is smooth, by chartwise reconstruction. -/
theorem contMDiff_toOriginal : ContMDiff L K n (toOriginal f proj) := by
  intro p
  obtain ⟨i, hi⟩ := (atlas f A).covers (projection f proj p)
  have hx := (contMDiff_projection f M).contMDiffAt (x := p)
  have hbase := hf.contMDiffAt.comp p hx
  have hgroup := (M.contMDiffAt_triv i p hi).snd
  have hlocal := (S.contMDiffAt_symm i (f (projection f proj p), ((atlas f A).triv i p).2) hi).comp p
    (hbase.prodMk hgroup)
  apply hlocal.congr_of_eventuallyEq
  filter_upwards [hx.continuousAt.preimage_mem_nhds (((atlas f A).triv i).open_baseSet.mem_nhds hi)] with q hq
  change toOriginal f proj q =
    (A.triv i).toOpenPartialHomeomorph.symm (f (projection f proj q), (A.triv i (toOriginal f proj q)).2)
  rw [commutes f q]
  exact ((A.triv i).symm_apply_mk_proj ((A.triv i).mem_source.mpr ((commutes f q) ▸ hq))).symm

end FoliationQM.SmoothPullbackProjections
