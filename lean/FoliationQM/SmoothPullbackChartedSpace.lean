module
public import FoliationQM.GeometricPrincipalPullback
public import FoliationQM.GeometricPrincipalManifold

/-!
# Product charts on the geometric principal pullback

For the frame-bundle construction in v13 `prop:takabayasi`, compose the
principal trivializations on the fiber product with the actual charts of the
new base times the group. On a true overlap the base coordinate stays fixed,
and the group coordinate changes by the original chart change over its image.
-/

@[expose] public section
noncomputable section
open Bundle Set
open scoped Manifold
namespace FoliationQM.SmoothPullbackChartedSpace
open GeometricPrincipalPullback

variable {X B T G ι : Type*} [TopologicalSpace X] [TopologicalSpace B]
  [TopologicalSpace T] [TopologicalSpace G] [Group G] {proj : T → B}

section Charts
variable (HX HG : Type*) [TopologicalSpace HX] [TopologicalSpace HG]
  [ChartedSpace HX X] [ChartedSpace HG G]
  (f : C(X, B)) (A : GeometricPrincipalAtlas.Data (G := G) proj ι)

/-- The charted space on the actual fiber product, using its subspace topology. -/
abbrev chartedSpace : ChartedSpace (ModelProd HX HG) (Total f proj) :=
  GeometricPrincipalManifold.chartedSpace HX HG (GeometricPrincipalPullback.atlas f A)

/-- Every chart consists of an actual pullback trivialization followed by a product chart. -/
theorem mem_atlas_iff (e : OpenPartialHomeomorph (Total f proj) (ModelProd HX HG)) :
    letI := chartedSpace HX HG f A
    e ∈ _root_.atlas (ModelProd HX HG) (Total f proj) ↔
      ∃ i, ∃ c ∈ _root_.atlas (ModelProd HX HG) (X × G),
        e = (trivialization f A i).toOpenPartialHomeomorph.trans c := Iff.rfl

/-- The distinguished chart at a pullback point uses a containing original chart at its image. -/
theorem chartAt_eq (p : Total f proj) :
    letI := chartedSpace HX HG f A
    let i := (A.covers (f (projection f proj p))).choose
    chartAt (ModelProd HX HG) p = (trivialization f A i).toOpenPartialHomeomorph.trans
      (chartAt (ModelProd HX HG) (projection f proj p, (A.triv i (toOriginal f proj p)).2)) := rfl

end Charts

variable (f : C(X, B)) (A : GeometricPrincipalAtlas.Data (G := G) proj ι)

/-- The exact source of each change of trivializations is the preimage overlap times the group. -/
theorem change_source (i j : ι) :
    ((trivialization f A i).toOpenPartialHomeomorph.symm.trans
      (trivialization f A j).toOpenPartialHomeomorph).source =
      (f ⁻¹' ((A.triv i).baseSet ∩ (A.triv j).baseSet)) ×ˢ (univ : Set G) :=
  GeometricPrincipalManifold.trivTransition_source (GeometricPrincipalPullback.atlas f A) i j

/-- On this overlap the original transition multiplies the old group coordinate on the left. -/
theorem change_action (i j : ι) (z : X × G)
    (hi : f z.1 ∈ (A.triv i).baseSet) (hj : f z.1 ∈ (A.triv j).baseSet) :
    trivialization f A j ((trivialization f A i).toOpenPartialHomeomorph.symm z) =
      (z.1, A.transition i j (f z.1) * z.2) := by
  have h := GeometricPrincipalManifold.trivTransition_apply
    (GeometricPrincipalPullback.atlas f A) i j z hi hj
  rw [transition_eq f A i j z.1 hi hj] at h
  exact h

/-- The changed group coordinate is the second component of the original change between charts. -/
theorem change_apply (i j : ι) (z : X × G)
    (hi : f z.1 ∈ (A.triv i).baseSet) (hj : f z.1 ∈ (A.triv j).baseSet) :
    trivialization f A j ((trivialization f A i).toOpenPartialHomeomorph.symm z) =
      (z.1, (A.triv j ((A.triv i).toOpenPartialHomeomorph.symm (f z.1, z.2))).2) := by
  rw [change_action f A i j z hi hj,
    GeometricPrincipalManifold.trivTransition_apply A i j (f z.1, z.2) hi hj]

section Smooth
variable {EX EB EG ET HX HB HG HT : Type*}
  [NormedAddCommGroup EX] [NormedSpace ℝ EX] [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  [NormedAddCommGroup EG] [NormedSpace ℝ EG] [NormedAddCommGroup ET] [NormedSpace ℝ ET]
  [TopologicalSpace HX] [TopologicalSpace HB] [TopologicalSpace HG] [TopologicalSpace HT]
  [ChartedSpace HX X] [ChartedSpace HB B] [ChartedSpace HG G] [ChartedSpace HT T]
  {IX : ModelWithCorners ℝ EX HX} {IB : ModelWithCorners ℝ EB HB}
  {J : ModelWithCorners ℝ EG HG} {K : ModelWithCorners ℝ ET HT} {n : WithTop ℕ∞}

/-- The geometric pullback transitions inherit the original smoothness order on each true overlap. -/
theorem contMDiffOn_transition (hf : ContMDiff IX IB n f)
    (S : GeometricPrincipalSmoothAtlas.Data IB J K A n) (i j : ι) :
    ContMDiffOn IX J n ((GeometricPrincipalPullback.atlas f A).transition i j)
      (f ⁻¹' ((A.triv i).baseSet ∩ (A.triv j).baseSet)) := by
  apply ((S.contMDiffOn_transition i j).comp hf.contMDiffOn (fun _ hx => hx)).congr
  intro x hx
  exact transition_eq f A i j x hx.1 hx.2

end Smooth
end FoliationQM.SmoothPullbackChartedSpace
