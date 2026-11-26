module

public import FoliationQM.CurvedAtlasDescent
public import FoliationQM.CurvedChartTestTransport

/-!
# Compact chart tests as actual global fields

A coordinate test with compact support inside one chart target extends by
zero to the manifold. Its support remains compactly contained in that
chart. Consequently the global field has the atlas regularity needed for
the curved action variation, including at the boundary of its chart.
-/

@[expose] public section
noncomputable section
open scoped Topology
namespace FoliationQM.CurvedAtlasTests

open Set Filter LorentzMatrixGroup CurvedMetricChartMeasure CurvedAtlasDescent

variable {X : Type*} [TopologicalSpace X] {F : Type*} [NormedAddCommGroup F]

/-- A coordinate test extended by zero outside the source of its chart. -/
def extend (A : MetricAtlas X) (i : ℕ) (η : Covector → F) : X → F :=
  (A.chart i).source.indicator (η ∘ A.chart i)

/-- On its chart source the extension is the coordinate test. -/
theorem extend_apply (A : MetricAtlas X) (i : ℕ) (η : Covector → F)
    {x : X} (hx : x ∈ (A.chart i).source) : extend A i η x = η (A.chart i x) :=
  indicator_of_mem hx _

/-- Outside its chart source the extension is zero. -/
theorem extend_zero (A : MetricAtlas X) (i : ℕ) (η : Covector → F)
    {x : X} (hx : x ∉ (A.chart i).source) : extend A i η x = 0 :=
  indicator_of_notMem hx _

/-- The original coordinate representative agrees with the test throughout a neighborhood of any target point. -/
theorem repr_extend_germ (A : MetricAtlas X) (i : ℕ) (η : Covector → F)
    {y : Covector} (hy : y ∈ (A.chart i).target) : repr A i (extend A i η) =ᶠ[𝓝 y] η := by
  filter_upwards [(A.chart i).open_target.mem_nhds hy] with z hz
  simp only [CurvedAtlasDescent.repr, Function.comp_apply, extend_apply A i η ((A.chart i).map_target hz),
    (A.chart i).right_inv hz]

variable [T2Space X] {η : Covector → F}

/-- The extension's topological support lies in the inverse chart image of the original compact support. -/
theorem extend_tsupport_image (A : MetricAtlas X) (i : ℕ) (hc : HasCompactSupport η)
    (hs : tsupport η ⊆ (A.chart i).target) :
    tsupport (extend A i η) ⊆ (A.chart i).symm '' tsupport η := by
  apply closure_minimal _ (hc.image_of_continuousOn ((A.chart i).symm.continuousOn.mono hs)).isClosed
  intro x hx
  by_cases hxs : x ∈ (A.chart i).source
  · refine ⟨A.chart i x, subset_closure ?_, (A.chart i).left_inv hxs⟩
    simpa only [Function.mem_support, extend_apply A i η hxs] using hx
  · exact (hx (extend_zero A i η hxs)).elim

/-- The support of the global test stays inside its original chart, including its chart boundary. -/
theorem extend_tsupport_subset (A : MetricAtlas X) (i : ℕ) (hc : HasCompactSupport η)
    (hs : tsupport η ⊆ (A.chart i).target) : tsupport (extend A i η) ⊆ (A.chart i).source := by
  rintro x hx
  obtain ⟨y, hy, rfl⟩ := extend_tsupport_image A i hc hs hx
  exact (A.chart i).map_target (hs hy)

/-- Zero extension preserves compact support on the manifold. -/
theorem extend_compact (A : MetricAtlas X) (i : ℕ) (hc : HasCompactSupport η)
    (hs : tsupport η ⊆ (A.chart i).target) : HasCompactSupport (extend A i η) :=
  (hc.image_of_continuousOn ((A.chart i).symm.continuousOn.mono hs)).of_isClosed_subset
    (isClosed_tsupport _) (extend_tsupport_image A i hc hs)

/-- At every point outside the chart source the global extension is zero on a neighborhood. -/
theorem extend_zero_germ (A : MetricAtlas X) (i : ℕ) (hc : HasCompactSupport η)
    (hs : tsupport η ⊆ (A.chart i).target) {x : X} (hx : x ∉ (A.chart i).source) :
    extend A i η =ᶠ[𝓝 x] fun _ => 0 :=
  notMem_tsupport_iff_eventuallyEq.mp (fun h => hx (extend_tsupport_subset A i hc hs h))

/-- A compact C² coordinate test has C² representatives in every smooth metric chart. -/
theorem regular_extend [NormedSpace ℝ F] (A : MetricAtlas X) (hA : SmoothLorentz A) (i : ℕ)
    (hη : ContDiff ℝ 2 η) (hc : HasCompactSupport η) (hs : tsupport η ⊆ (A.chart i).target) :
    Regular A 2 (extend A i η) := by
  intro j y hy
  let x := (A.chart j).symm y
  have hxj : x ∈ (A.chart j).source := (A.chart j).map_target hy
  have hcont : ContinuousAt (A.chart j).symm y :=
    (A.chart j).symm.continuousOn.continuousAt ((A.chart j).open_target.mem_nhds hy)
  by_cases hxi : x ∈ (A.chart i).source
  · have htrans := hA.transition_smooth j i y ⟨x, ⟨hxj, hxi⟩, (A.chart j).right_inv hy⟩
    apply (hη.contDiffAt.comp y (htrans.of_le (by decide))).congr_of_eventuallyEq
    have hn := hcont.eventually ((A.chart i).open_source.mem_nhds hxi)
    filter_upwards [hn] with z hz
    exact extend_apply A i η hz
  · apply (contDiffAt_const (c := (0 : F))).congr_of_eventuallyEq
    exact (extend_zero_germ A i hc hs hxi).comp_tendsto hcont

end FoliationQM.CurvedAtlasTests
