module

public import FoliationQM.CurvedAtlasMeasure
public import FoliationQM.RNCCoordinateVolumeChange
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Measure.Comap

/-!
# Metric volume carried from an actual coordinate chart

Coordinate Lebesgue measure weighted by the metric determinant is pulled
back through the chart on its source. Its value on a measurable region is
the coordinate integral on the image. The Jacobian theorem then identifies
these measures on overlaps where the two metric arrays are related by pullback.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.CurvedMetricChartMeasure

open MeasureTheory Set LorentzMatrixGroup RNCCoordinateVolumeChange RNCVolumeDensity
variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
abbrev Chart (X : Type*) [TopologicalSpace X] := OpenPartialHomeomorph X Covector

/-- The Borel measurable embedding of the chart's actual open source into coordinate space. -/
theorem embedding (e : Chart X) : MeasurableEmbedding (fun x : e.source => e x) :=
  (MeasurableEmbedding.subtype_coe e.open_target.measurableSet).comp
    e.toHomeomorphSourceTarget.toMeasurableEquiv.measurableEmbedding

/-- Metric-weighted coordinate Lebesgue measure. -/
def coordinate (g : Covector → Mat4) : Measure Covector :=
  volume.withDensity (fun y => ENNReal.ofReal (volumeFactor (g y)))

/-- Chart measure supported on the source, using the actual chart map on that source. -/
def chartMeasure (e : Chart X) (g : Covector → Mat4) : Measure X :=
  ((coordinate g).comap (fun x : e.source => e x)).map Subtype.val

/-- A region inside the chart has volume equal to the measure of its coordinate image. -/
theorem chartMeasure_apply (e : Chart X) (g : Covector → Mat4) {s : Set X} (hs : MeasurableSet s)
    (hsub : s ⊆ e.source) : chartMeasure e g s = coordinate g (e '' s) := by
  rw [chartMeasure, Measure.map_apply measurable_subtype_coe hs,
    (embedding e).comap_apply]
  congr 1
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x.val, hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x, hsub hx⟩, hx, rfl⟩

/-- Chart images of measurable subsets of the source are measurable in coordinate space. -/
theorem measurable_image (e : Chart X) {s : Set X} (hs : MeasurableSet s) (hsub : s ⊆ e.source) :
    MeasurableSet (e '' s) := by
  have he : (fun x : e.source => e x) '' (Subtype.val ⁻¹' s) = e '' s := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨z.val, hz, rfl⟩
    · rintro ⟨z, hz, rfl⟩
      exact ⟨⟨z, hsub hz⟩, hz, rfl⟩
  rw [← he]
  exact (embedding e).measurableSet_image.2 (measurable_subtype_coe hs)

/-- Metric-volume measures of two charts agree on their overlap by the ordinary Jacobian theorem. -/
theorem overlap (a b : Chart X) (g k : Covector → Mat4) (D : Covector → Covector →L[ℝ] Covector)
    (hD : ∀ y ∈ a '' (a.source ∩ b.source), HasFDerivAt (b ∘ a.symm) (D y) y)
    (hmetric : ∀ y ∈ a '' (a.source ∩ b.source), g y = pullMetric k (b ∘ a.symm) D y) :
    (chartMeasure a g).restrict (a.source ∩ b.source) = (chartMeasure b k).restrict (a.source ∩ b.source) := by
  ext s hs
  let t := s ∩ (a.source ∩ b.source)
  have ht : MeasurableSet t := hs.inter (a.open_source.measurableSet.inter b.open_source.measurableSet)
  have ha : t ⊆ a.source := fun _ hx => hx.2.1
  have hb : t ⊆ b.source := fun _ hx => hx.2.2
  have hi : InjOn (b ∘ a.symm) (a '' t) := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨z, hz, rfl⟩ he
    simp only [Function.comp_apply, a.left_inv (ha hx), a.left_inv (ha hz)] at he
    rw [b.injOn (hb hx) (hb hz) he]
  have him : (b ∘ a.symm) '' (a '' t) = b '' t := by
    rw [image_image]
    exact image_congr (fun x hx => congrArg b (a.left_inv (ha hx)))
  have sub : a '' t ⊆ a '' (a.source ∩ b.source) := image_mono inter_subset_right
  have he := lintegral_pullMetric (measurable_image a ht ha)
    (fun y hy => (hD y (sub hy)).hasFDerivWithinAt) hi k (fun _ => 1)
  simp only [mul_one, him] at he
  rw [Measure.restrict_apply hs, Measure.restrict_apply hs]
  change chartMeasure a g t = chartMeasure b k t
  rw [chartMeasure_apply a g ht ha, chartMeasure_apply b k ht hb, coordinate, coordinate,
    withDensity_apply _ (measurable_image a ht ha), withDensity_apply _ (measurable_image b ht hb), he]
  exact lintegral_congr_ae <| (ae_restrict_mem (measurable_image a ht ha)).mono fun y hy =>
    congrArg (fun m => ENNReal.ofReal (volumeFactor m)) (hmetric y (sub hy))

/-- A countable cover by actual manifold charts, with coordinate metric arrays related by their transition Jacobians. -/
structure MetricAtlas (X : Type*) [TopologicalSpace X] where
  chart : ℕ → Chart X
  metric : ℕ → Covector → Mat4
  cover : ⋃ i, (chart i).source = univ
  transitionDeriv : ℕ → ℕ → Covector → Covector →L[ℝ] Covector
  hasDeriv : ∀ i j y, y ∈ chart i '' ((chart i).source ∩ (chart j).source) →
    HasFDerivAt (chart j ∘ (chart i).symm) (transitionDeriv i j y) y
  metric_pullback : ∀ i j y, y ∈ chart i '' ((chart i).source ∩ (chart j).source) →
    metric i y = pullMetric (metric j) (chart j ∘ (chart i).symm) (transitionDeriv i j) y

/-- The metric volume of a countable coordinate atlas uses explicitly disjointized chart sources. -/
def MetricAtlas.measure (A : MetricAtlas X) : Measure X :=
  CurvedAtlasMeasure.assemble (fun i => (A.chart i).source) (fun i => chartMeasure (A.chart i) (A.metric i))

/-- The constructed global metric volume agrees with the coordinate determinant measure on each chart, without assuming a global measure. -/
theorem MetricAtlas.measure_restrict (A : MetricAtlas X) (j : ℕ) :
    A.measure.restrict (A.chart j).source =
      (chartMeasure (A.chart j) (A.metric j)).restrict (A.chart j).source :=
  CurvedAtlasMeasure.restrict_chart _ (fun i => (A.chart i).open_source.measurableSet) A.cover _
    (fun i k => overlap _ _ _ _ _ (A.hasDeriv i k) (A.metric_pullback i k)) j

/-- The global volume is uniquely determined by the metric determinants on the chart images. -/
theorem MetricAtlas.measure_unique (A : MetricAtlas X) {ν : Measure X}
    (hν : ∀ j, ν.restrict (A.chart j).source =
      (chartMeasure (A.chart j) (A.metric j)).restrict (A.chart j).source) : ν = A.measure :=
  CurvedAtlasMeasure.unique _ (fun i => (A.chart i).open_source.measurableSet) A.cover
    (fun i => (hν i).trans (A.measure_restrict i).symm)

/-- Integrals over a chart source under the global metric measure use that chart's own determinant measure. -/
theorem MetricAtlas.integral_chart {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : MetricAtlas X) (j : ℕ) (f : X → E) :
    (∫ x in (A.chart j).source, f x ∂A.measure) =
      ∫ x in (A.chart j).source, f x ∂(chartMeasure (A.chart j) (A.metric j)) := by
  rw [A.measure_restrict]

/-- For an integrable global scalar the disjointized chart integrals sum to its metric-volume integral, with each term evaluated against its own determinant measure. -/
theorem MetricAtlas.hasSum_chart_integrals {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : MetricAtlas X) {f : X → E} (hf : Integrable f A.measure) :
    HasSum (fun i => ∫ x in disjointed (fun j => (A.chart j).source) i, f x
      ∂(chartMeasure (A.chart i) (A.metric i))) (∫ x, f x ∂A.measure) := by
  let U := fun i => (A.chart i).source
  have hm (i) : MeasurableSet (U i) := (A.chart i).open_source.measurableSet
  have hc : ⋃ i, disjointed U i = univ := iUnion_disjointed.trans A.cover
  have he (i : ℕ) : A.measure.restrict (disjointed U i) =
      (chartMeasure (A.chart i) (A.metric i)).restrict (disjointed U i) :=
    Measure.restrict_congr_mono (disjointed_subset U i) (A.measure_restrict i)
  have hh := hasSum_integral_iUnion (MeasurableSet.disjointed hm) (disjoint_disjointed U) hf.integrableOn
  simp only [hc, Measure.restrict_univ, he] at hh
  exact hh

/-- Metric volume is atlas-independent when transition pullbacks are compatible across both atlases. -/
theorem MetricAtlas.measure_independent (A B : MetricAtlas X)
    (D : ℕ → ℕ → Covector → Covector →L[ℝ] Covector)
    (hD : ∀ i j y, y ∈ A.chart i '' ((A.chart i).source ∩ (B.chart j).source) →
      HasFDerivAt (B.chart j ∘ (A.chart i).symm) (D i j y) y)
    (hmetric : ∀ i j y, y ∈ A.chart i '' ((A.chart i).source ∩ (B.chart j).source) →
      A.metric i y = pullMetric (B.metric j) (B.chart j ∘ (A.chart i).symm) (D i j) y) :
    A.measure = B.measure :=
  CurvedAtlasMeasure.independent (fun i => (A.chart i).open_source.measurableSet)
    (fun j => (B.chart j).open_source.measurableSet) A.cover B.cover
    (fun i j => overlap _ _ _ _ _ (A.hasDeriv i j) (A.metric_pullback i j))
    (fun i j => overlap _ _ _ _ _ (B.hasDeriv i j) (B.metric_pullback i j))
    (fun i j => overlap _ _ _ _ _ (hD i j) (hmetric i j))

end FoliationQM.CurvedMetricChartMeasure
