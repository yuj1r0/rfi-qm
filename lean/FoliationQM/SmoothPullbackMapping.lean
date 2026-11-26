module
public import FoliationQM.SmoothPullbackProjections

/-!
# Smooth maps into the geometric principal fiber product

For the frame-bundle component of v13 `prop:takabayasi`, two maps to the
new base and the original principal space determine a unique map to their
fiber product when their projections agree. In actual pulled principal
charts this lift is smooth whenever both components are smooth. The two
projections give the converse when the base map is smooth.
-/

@[expose] public section
noncomputable section
open scoped Manifold Topology
namespace FoliationQM.SmoothPullbackMapping
open GeometricPrincipalPullback

section Mapping
variable {X B T Z : Type*} [TopologicalSpace X] [TopologicalSpace B] {proj : T → B}
  (f : C(X, B))

/-- The map to the actual fiber product given by a pair of compatible component maps. -/
def lift (b : Z → X) (t : Z → T) (comm : ∀ z, f (b z) = proj (t z)) (z : Z) : Total f proj :=
  ⟨(b z, t z), comm z⟩

/-- The lift has the prescribed component in the new base. -/
theorem projection_lift (b : Z → X) (t : Z → T) (comm : ∀ z, f (b z) = proj (t z)) (z : Z) :
    projection f proj (lift f b t comm z) = b z := rfl

/-- The lift has the prescribed component in the original total space. -/
theorem toOriginal_lift (b : Z → X) (t : Z → T) (comm : ∀ z, f (b z) = proj (t z)) (z : Z) :
    toOriginal f proj (lift f b t comm z) = t z := rfl

/-- Reconstructing a map from its two projections recovers the map itself. -/
theorem lift_eta (F : Z → Total f proj) : lift f (fun z => projection f proj (F z))
    (fun z => toOriginal f proj (F z)) (fun z => commutes f (F z)) = F := rfl

/-- Any map to the fiber product with these pointwise components equals the constructed lift. -/
theorem lift_unique (b : Z → X) (t : Z → T) (comm : ∀ z, f (b z) = proj (t z))
    (F : Z → Total f proj) (hb : ∀ z, projection f proj (F z) = b z)
    (ht : ∀ z, toOriginal f proj (F z) = t z) : F = lift f b t comm :=
  funext (fun z => Subtype.ext (Prod.ext (hb z) (ht z)))
end Mapping

section Smooth
variable {EX EB EG ET EY EZ HX HB HG HT HY HZ X B G T Z ι : Type*}
  [NormedAddCommGroup EX] [NormedSpace ℝ EX] [TopologicalSpace HX]
  [NormedAddCommGroup EB] [NormedSpace ℝ EB] [TopologicalSpace HB]
  [NormedAddCommGroup EG] [NormedSpace ℝ EG] [TopologicalSpace HG]
  [NormedAddCommGroup ET] [NormedSpace ℝ ET] [TopologicalSpace HT]
  [NormedAddCommGroup EY] [NormedSpace ℝ EY] [TopologicalSpace HY]
  [NormedAddCommGroup EZ] [NormedSpace ℝ EZ] [TopologicalSpace HZ]
  [TopologicalSpace X] [ChartedSpace HX X] [TopologicalSpace B] [ChartedSpace HB B]
  [TopologicalSpace G] [ChartedSpace HG G] [Group G] [TopologicalSpace T] [ChartedSpace HT T]
  [TopologicalSpace Z] [ChartedSpace HZ Z]
  {IX : ModelWithCorners ℝ EX HX} {IB : ModelWithCorners ℝ EB HB} {J : ModelWithCorners ℝ EG HG}
  {K : ModelWithCorners ℝ ET HT} {L : ModelWithCorners ℝ EY HY} {IZ : ModelWithCorners ℝ EZ HZ}
  {n : WithTop ℕ∞} {proj : T → B} {A : GeometricPrincipalAtlas.Data (G := G) proj ι}
  (f : C(X, B)) (hf : ContMDiff IX IB n f)
  (S : GeometricPrincipalSmoothAtlas.Data IB J K A n) [ChartedSpace HY (Total f proj)]
  (M : GeometricPrincipalSmoothAtlas.Data IX J L (atlas f A) n)

include S M

/-- A pair smooth within a set gives a smooth lift there. In a containing
principal chart, the coordinates are the base map and the original chart's group component. -/
theorem contMDiffWithinAt_lift (b : Z → X) (t : Z → T) (comm : ∀ z, f (b z) = proj (t z))
    {s : Set Z} {z : Z} (hb : ContMDiffWithinAt IZ IX n b s z) (ht : ContMDiffWithinAt IZ K n t s z) :
    ContMDiffWithinAt IZ L n (lift f b t comm) s z := by
  obtain ⟨i, hi⟩ := A.covers (proj (t z))
  let v := (atlas f A).triv i
  have hx : b z ∈ v.baseSet := by
    change f (b z) ∈ (A.triv i).baseSet
    rwa [comm z]
  have hgroup := ((S.contMDiffAt_triv i (t z) hi).comp_contMDiffWithinAt z ht).snd
  have hinv := (M.contMDiffAt_symm i (b z, (A.triv i (t z)).2) hx).comp_contMDiffWithinAt z (hb.prodMk hgroup)
  have heq : ∀ y, b y ∈ v.baseSet → lift f b t comm y =
      v.toOpenPartialHomeomorph.symm (b y, (A.triv i (t y)).2) := fun y hy =>
    (v.toOpenPartialHomeomorph.left_inv (show lift f b t comm y ∈ v.source from v.mem_source.mpr hy)).symm
  apply hinv.congr_of_eventuallyEq
  · filter_upwards [hb.continuousWithinAt (v.open_baseSet.mem_nhds hx)] with y hy
    exact heq y hy
  · exact heq z hx

/-- Two globally smooth compatible components give a globally smooth map to the fiber product. -/
theorem contMDiff_lift (b : Z → X) (t : Z → T) (comm : ∀ z, f (b z) = proj (t z))
    (hb : ContMDiff IZ IX n b) (ht : ContMDiff IZ K n t) : ContMDiff IZ L n (lift f b t comm) :=
  fun z => contMDiffWithinAt_univ.mp (contMDiffWithinAt_lift f S M b t comm
    (hb.contMDiffAt (x := z)).contMDiffWithinAt ht.contMDiffAt.contMDiffWithinAt)

include hf in
/-- For a smooth base map, smoothness of a map germ into the pulled principal space
is equivalent to smoothness of its two actual component germs. -/
theorem contMDiffWithinAt_iff (F : Z → Total f proj) {s : Set Z} {z : Z} :
    ContMDiffWithinAt IZ L n F s z ↔
      ContMDiffWithinAt IZ IX n (fun w => projection f proj (F w)) s z ∧
      ContMDiffWithinAt IZ K n (fun w => toOriginal f proj (F w)) s z := by
  constructor
  · intro hF
    exact ⟨(SmoothPullbackProjections.contMDiff_projection f M).contMDiffAt.comp_contMDiffWithinAt z hF,
      (SmoothPullbackProjections.contMDiff_toOriginal f hf S M).contMDiffAt.comp_contMDiffWithinAt z hF⟩
  · rintro ⟨hb, ht⟩
    exact contMDiffWithinAt_lift f S M _ _ (fun w => commutes f (F w)) hb ht

include hf in
/-- For a smooth base map, a map to the actual pullback is smooth exactly when both projections are smooth. -/
theorem contMDiff_iff (F : Z → Total f proj) : ContMDiff IZ L n F ↔
    ContMDiff IZ IX n (fun z => projection f proj (F z)) ∧
      ContMDiff IZ K n (fun z => toOriginal f proj (F z)) := by
  constructor
  · intro hF
    exact ⟨(SmoothPullbackProjections.contMDiff_projection f M).comp hF,
      (SmoothPullbackProjections.contMDiff_toOriginal f hf S M).comp hF⟩
  · rintro ⟨hb, ht⟩
    exact contMDiff_lift f S M _ _ (fun z => commutes f (F z)) hb ht

end Smooth
end FoliationQM.SmoothPullbackMapping
