module

public import FoliationQM.CurvedMetricChartMeasure
public import FoliationQM.CurvedWeakEquation

/-!
# Coordinate formulas for integration against the constructed metric measure

The global measure restricts to a chart measure. The actual chart map sends
that restriction to weighted Lebesgue measure on its target. This gives
the coordinate integral for any scalar or vector-valued field and permits
passing chartwise action and variation identities to the global measure.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.CurvedChartIntegration

open MeasureTheory Set CurvedMetricChartMeasure RNCVolumeDensity LorentzMatrixGroup
variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]

/-- A chart's source restriction pushes forward to its coordinate metric measure on the target. -/
theorem map_chart (e : Chart X) (g : Covector → Mat4) :
    (chartMeasure e g).map e = (coordinate g).restrict e.target := by
  let μ := (coordinate g).comap (fun x : e.source => e x)
  have hmap : AEMeasurable e (μ.map Subtype.val) := by
    apply ((MeasurableEmbedding.subtype_coe e.open_source.measurableSet).aemeasurable_map_iff).mpr
    exact (embedding e).measurable.aemeasurable
  rw [chartMeasure, AEMeasurable.map_map_of_aemeasurable hmap measurable_subtype_coe.aemeasurable]
  change μ.map (fun x : e.source => e x) = _
  rw [show μ = (coordinate g).comap (fun x : e.source => e x) from rfl, (embedding e).map_comap]
  congr 1
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact e.map_source x.property
  · intro hy
    exact ⟨⟨e.symm y, e.map_target hy⟩, e.right_inv hy⟩

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Integration under a chart measure equals integration of the coordinate representative against its determinant measure. -/
theorem integral_chartMeasure (e : Chart X) (g : Covector → Mat4) (f : X → E) :
    (∫ x, f x ∂chartMeasure e g) = ∫ y in e.target, f (e.symm y) ∂coordinate g := by
  have he := (embedding e).integral_map (μ := (coordinate g).comap (fun x : e.source => e x))
    (fun y => f (e.symm y))
  rw [(embedding e).map_comap] at he
  have hr : Set.range (fun x : e.source => e x) = e.target := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact e.map_source x.property
    · intro hy
      exact ⟨⟨e.symm y, e.map_target hy⟩, e.right_inv hy⟩
  rw [hr] at he
  rw [chartMeasure, (MeasurableEmbedding.subtype_coe e.open_source.measurableSet).integral_map]
  simpa only [e.left_inv, Subtype.property] using he.symm

/-- The actual global metric integral on a chart source has the usual coordinate volume factor. -/
theorem integral_chart (A : MetricAtlas X) (i : ℕ) (f : X → E)
    (hg : ContinuousOn (A.metric i) (A.chart i).target) :
    (∫ x in (A.chart i).source, f x ∂A.measure) =
      ∫ y in (A.chart i).target, volumeFactor (A.metric i y) • f ((A.chart i).symm y) := by
  rw [A.measure_restrict]
  have hsource : (chartMeasure (A.chart i) (A.metric i)).restrict (A.chart i).source =
      chartMeasure (A.chart i) (A.metric i) := by
    apply Measure.restrict_eq_self_of_ae_mem
    rw [chartMeasure, (MeasurableEmbedding.subtype_coe (A.chart i).open_source.measurableSet).ae_map_iff]
    exact Filter.Eventually.of_forall fun x => x.property
  rw [hsource, integral_chartMeasure, coordinate]
  have hm : AEMeasurable (fun y => ENNReal.ofReal (volumeFactor (A.metric i y)))
      (volume.restrict (A.chart i).target) :=
    (ENNReal.continuous_ofReal.comp_continuousOn
      (CurvedWeakEquation.volumeFactor_continuous.comp_continuousOn hg)).aemeasurable
        (A.chart i).open_target.measurableSet
  rw [setIntegral_withDensity_eq_setIntegral_toReal_smul₀ hm
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top) _ (A.chart i).open_target.measurableSet]
  simp only [volumeFactor, ENNReal.toReal_ofReal (Real.sqrt_nonneg _)]

omit [NormedSpace ℝ E] in
/-- Integrability under a chart measure is equivalent to integrability of its actual coordinate representative. -/
theorem integrable_chartMeasure (e : Chart X) (g : Covector → Mat4) (f : X → E) :
    Integrable f (chartMeasure e g) ↔ IntegrableOn (fun y => f (e.symm y)) e.target (coordinate g) := by
  have he := (embedding e).integrable_map_iff
    (μ := (coordinate g).comap (fun x : e.source => e x)) (g := fun y => f (e.symm y))
  rw [(embedding e).map_comap] at he
  have hr : Set.range (fun x : e.source => e x) = e.target := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact e.map_source x.property
    · intro hy
      exact ⟨⟨e.symm y, e.map_target hy⟩, e.right_inv hy⟩
  rw [hr] at he
  rw [chartMeasure, (MeasurableEmbedding.subtype_coe e.open_source.measurableSet).integrable_map_iff]
  have heq : (fun y => f (e.symm y)) ∘ (fun x : e.source => e x) = f ∘ Subtype.val := by
    funext x
    simp only [Function.comp_apply, e.left_inv x.property]
  rw [heq] at he
  exact he.symm

/-- Global integrability on a chart source is exactly coordinate integrability with the determinant volume factor. -/
theorem integrable_chart (A : MetricAtlas X) (i : ℕ) (f : X → E)
    (hg : ContinuousOn (A.metric i) (A.chart i).target) :
    IntegrableOn f (A.chart i).source A.measure ↔
      IntegrableOn (fun y => volumeFactor (A.metric i y) • f ((A.chart i).symm y)) (A.chart i).target := by
  rw [IntegrableOn, A.measure_restrict]
  have hsource : (chartMeasure (A.chart i) (A.metric i)).restrict (A.chart i).source =
      chartMeasure (A.chart i) (A.metric i) := by
    apply Measure.restrict_eq_self_of_ae_mem
    rw [chartMeasure, (MeasurableEmbedding.subtype_coe (A.chart i).open_source.measurableSet).ae_map_iff]
    exact Filter.Eventually.of_forall fun x => x.property
  rw [hsource, integrable_chartMeasure, IntegrableOn, coordinate,
    restrict_withDensity (A.chart i).open_target.measurableSet]
  have hm : AEMeasurable (fun y => ENNReal.ofReal (volumeFactor (A.metric i y)))
      (volume.restrict (A.chart i).target) :=
    (ENNReal.continuous_ofReal.comp_continuousOn
      (CurvedWeakEquation.volumeFactor_continuous.comp_continuousOn hg)).aemeasurable
        (A.chart i).open_target.measurableSet
  rw [integrable_withDensity_iff_integrable_smul₀' hm
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp only [volumeFactor, ENNReal.toReal_ofReal (Real.sqrt_nonneg _)]
  rfl

end FoliationQM.CurvedChartIntegration
