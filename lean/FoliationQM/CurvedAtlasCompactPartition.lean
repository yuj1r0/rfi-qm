module

public import FoliationQM.CurvedAtlasTests
public import FoliationQM.CurvedChartTestPartition

/-!
# Finite coordinate localization of arbitrary compact atlas tests

The metric charts are assumed to belong to the C² maximal atlas of an
actual smooth manifold. A smooth partition of unity subordinate to their
open source cover then decomposes every compact C² field into finitely
many chart tests. Each coordinate test is extended by zero beyond its
chart target, with compact support and C² regularity proved across the
boundary.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.CurvedAtlasCompactPartition

open Set IsManifold CurvedMetricChartMeasure CurvedAtlasDescent CurvedAtlasTests
open scoped Topology Manifold ContDiff
set_option backward.isDefEq.respectTransparency false

variable {X F : Type*} [TopologicalSpace X] [NormedAddCommGroup F]

/-- A global field represented in one coordinate chart and cut off to zero outside the target. -/
def coordinateTest (A : MetricAtlas X) (i : ℕ) (η : X → F) : Covector → F :=
  (A.chart i).target.indicator (repr A i η)

/-- The coordinate cutoff agrees with the actual chart representative on the chart target. -/
theorem coordinateTest_apply (A : MetricAtlas X) (i : ℕ) (η : X → F) {y : Covector}
    (hy : y ∈ (A.chart i).target) : coordinateTest A i η y = repr A i η y :=
  indicator_of_mem hy _

/-- A compact global support inside the chart maps to a compact set containing the coordinate cutoff support. -/
theorem coordinateTest_tsupport_image (A : MetricAtlas X) (i : ℕ) {η : X → F}
    (hc : HasCompactSupport η) (hs : tsupport η ⊆ (A.chart i).source) :
    tsupport (coordinateTest A i η) ⊆ A.chart i '' tsupport η := by
  apply closure_minimal _ (hc.image_of_continuousOn ((A.chart i).continuousOn.mono hs)).isClosed
  intro y hy
  by_cases ht : y ∈ (A.chart i).target
  · refine ⟨(A.chart i).symm y, subset_closure ?_, (A.chart i).right_inv ht⟩
    change η ((A.chart i).symm y) ≠ 0
    simpa only [Function.mem_support, coordinateTest_apply A i η ht, CurvedAtlasDescent.repr,
      Function.comp_apply] using hy
  · exact (hy (indicator_of_notMem ht _)).elim

/-- The cutoff's closed support is contained in the open coordinate target. -/
theorem coordinateTest_tsupport_subset (A : MetricAtlas X) (i : ℕ) {η : X → F}
    (hc : HasCompactSupport η) (hs : tsupport η ⊆ (A.chart i).source) :
    tsupport (coordinateTest A i η) ⊆ (A.chart i).target := by
  rintro y hy
  obtain ⟨x, hx, rfl⟩ := coordinateTest_tsupport_image A i hc hs hy
  exact (A.chart i).map_source (hs hx)

/-- The coordinate test has compact support in the finite-dimensional coordinate space. -/
theorem coordinateTest_compact (A : MetricAtlas X) (i : ℕ) {η : X → F}
    (hc : HasCompactSupport η) (hs : tsupport η ⊆ (A.chart i).source) :
    HasCompactSupport (coordinateTest A i η) :=
  (hc.image_of_continuousOn ((A.chart i).continuousOn.mono hs)).of_isClosed_subset (isClosed_tsupport _)
    (coordinateTest_tsupport_image A i hc hs)

/-- The coordinate cutoff is identically zero on a neighborhood of every point outside its chart target. -/
theorem coordinateTest_zero_germ (A : MetricAtlas X) (i : ℕ) {η : X → F}
    (hc : HasCompactSupport η) (hs : tsupport η ⊆ (A.chart i).source) {y : Covector}
    (hy : y ∉ (A.chart i).target) : coordinateTest A i η =ᶠ[𝓝 y] fun _ => 0 :=
  notMem_tsupport_iff_eventuallyEq.mp (fun h => hy (coordinateTest_tsupport_subset A i hc hs h))

/-- Local C² coordinate regularity extends across the target boundary because the test vanishes there locally. -/
theorem coordinateTest_contDiff [NormedSpace ℝ F] (A : MetricAtlas X) (i : ℕ) {η : X → F}
    (hη : Regular A 2 η) (hc : HasCompactSupport η) (hs : tsupport η ⊆ (A.chart i).source) :
    ContDiff ℝ 2 (coordinateTest A i η) := by
  apply contDiff_iff_contDiffAt.mpr
  intro y
  by_cases hy : y ∈ (A.chart i).target
  · apply (hη i y hy).congr_of_eventuallyEq
    filter_upwards [(A.chart i).open_target.mem_nhds hy] with z hz
    exact coordinateTest_apply A i η hz
  · exact (contDiffAt_const (c := (0 : F))).congr_of_eventuallyEq
      (coordinateTest_zero_germ A i hc hs hy)

/-- Extending the coordinate cutoff back to the manifold recovers the original chart-supported global field. -/
theorem extend_coordinateTest (A : MetricAtlas X) (i : ℕ) {η : X → F}
    (hs : tsupport η ⊆ (A.chart i).source) : extend A i (coordinateTest A i η) = η := by
  funext x
  by_cases hx : x ∈ (A.chart i).source
  · rw [extend_apply A i _ hx, coordinateTest_apply A i η ((A.chart i).map_source hx), repr_chart A i η hx]
  · rw [extend_zero A i _ hx, image_eq_zero_of_notMem_tsupport (fun h => hx (hs h))]

section Manifold

variable [ChartedSpace Covector X]
variable [NormedSpace ℝ F]

/-- Metric-chart regularity is equivalent to manifold C² regularity when the metric charts belong to the C² maximal atlas. -/
theorem regular_iff_contMDiff (A : MetricAtlas X)
    (hcharts : ∀ i, A.chart i ∈ maximalAtlas 𝓘(ℝ, Covector) 2 X) (η : X → F) :
    Regular A 2 η ↔ ContMDiff 𝓘(ℝ, Covector) 𝓘(ℝ, F) 2 η := by
  constructor
  · intro hη x
    obtain ⟨i, hi⟩ := exists_chart A x
    have hf := (hη i (A.chart i x) ((A.chart i).map_source hi)).contMDiffAt.comp x
      (contMDiffAt_of_mem_maximalAtlas (hcharts i) hi)
    apply hf.congr_of_eventuallyEq
    filter_upwards [(A.chart i).open_source.mem_nhds hi] with y hy
    exact (repr_chart A i η hy).symm
  · intro hη i y hy
    exact (hη.contMDiffAt.comp y (contMDiffAt_symm_of_mem_maximalAtlas (hcharts i) hy)).contDiffAt

variable [IsManifold 𝓘(ℝ, Covector) ∞ X] [T2Space X] [SecondCountableTopology X]

/-- Every compact C² test is a finite sum of actual zero-extended coordinate tests, with regularity and compact support supplied for each piece. -/
theorem exists_coordinate_decomposition (A : MetricAtlas X)
    (hcharts : ∀ i, A.chart i ∈ maximalAtlas 𝓘(ℝ, Covector) 2 X) {η : X → F}
    (hη : Regular A 2 η) (hc : HasCompactSupport η) :
    ∃ (s : Finset ℕ) (θ : ℕ → Covector → F),
      (∀ i, ContDiff ℝ 2 (θ i) ∧ HasCompactSupport (θ i) ∧ tsupport (θ i) ⊆ (A.chart i).target ∧
        Regular A 2 (extend A i (θ i)) ∧ tsupport (extend A i (θ i)) ⊆ tsupport η) ∧
      η = ∑ i ∈ s, extend A i (θ i) := by
  let test : CurvedChartTestPartition.testSpace 𝓘(ℝ, Covector) X F 2 :=
    ⟨η, (regular_iff_contMDiff A hcharts η).mp hη, hc⟩
  obtain ⟨χ, hχ, _⟩ := CurvedChartTestPartition.exists_partition (I := 𝓘(ℝ, Covector)) (F := F) (n := 2)
    (fun i => (A.chart i).source) (fun i => (A.chart i).open_source) (by rw [A.cover])
  let part (i : ℕ) := CurvedChartTestPartition.piece χ test i
  have hpart (i) : Regular A 2 (part i).val :=
    (regular_iff_contMDiff A hcharts _).mpr (part i).property.1
  have hsource (i) : tsupport (part i).val ⊆ (A.chart i).source :=
    CurvedChartTestPartition.piece_tsupport χ test hχ i
  have he (i) : extend A i (coordinateTest A i (part i).val) = (part i).val :=
    extend_coordinateTest A i (hsource i)
  refine ⟨CurvedChartTestPartition.indices χ test, fun i => coordinateTest A i (part i).val, ?_, ?_⟩
  · intro i
    refine ⟨coordinateTest_contDiff A i (hpart i) (part i).property.2 (hsource i),
      coordinateTest_compact A i (part i).property.2 (hsource i),
      coordinateTest_tsupport_subset A i (part i).property.2 (hsource i), ?_, ?_⟩
    · rw [he i]
      exact hpart i
    · rw [he i]
      exact tsupport_smul_subset_right (fun x => χ i x) η
  · have H := congrArg (fun t : CurvedChartTestPartition.testSpace 𝓘(ℝ, Covector) X F 2 => t.val)
      (CurvedChartTestPartition.sum_pieces χ test)
    change (CurvedChartTestPartition.testSpace 𝓘(ℝ, Covector) X F 2).subtype
      (∑ i ∈ CurvedChartTestPartition.indices χ test, CurvedChartTestPartition.piece χ test i) = η at H
    rw [map_sum] at H
    rw [H.symm]
    apply Finset.sum_congr rfl
    intro i _
    exact (he i).symm

end Manifold
end FoliationQM.CurvedAtlasCompactPartition
