module

public import FoliationQM.WassersteinMappedCoupling
public import FoliationQM.WassersteinDirac
public import FoliationQM.UniformTransportConcentration

/-!
# Actual transport comparison under metric realizations

For a Dirac target, an actual almost-everywhere distance comparison
suffices and requires no joint distance measurability assumption. Every real-valued estimate retains a certificate
that the corresponding extended transport cost is finite.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.WassersteinMetricTransfer

open MeasureTheory Set Filter WassersteinCoupling WassersteinDirac
  UniformTransportConcentration
open scoped ENNReal NNReal Topology

section Metric

variable {E F : Type*} [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
  [MetricSpace F] [MeasurableSpace F] [BorelSpace F]
  {f : E → F} {L : ℝ≥0}

/-- Actual almost-everywhere distance domination transfers the extended Dirac transport cost. -/
theorem eW1_map_dirac_le_of_ae (μ : Measure E) [IsProbabilityMeasure μ] {y : E}
    (hf : AEMeasurable f μ)
    (hdom : ∀ᵐ x ∂μ, edist (f x) (f y) ≤ (L : ℝ≥0∞) * edist x y) :
    eW1 (μ.map f) (Measure.dirac (f y)) ≤ (L : ℝ≥0∞) * eW1 μ (Measure.dirac y) := by
  rw [eW1_dirac, eW1_dirac,
    lintegral_map' measurable_edist_left.aemeasurable hf]
  exact (lintegral_mono_ae hdom).trans_eq
    (lintegral_const_mul' _ _ ENNReal.coe_ne_top)

/-- Regional comparison proves target finiteness before exposing its real transport bound. -/
theorem eW1_map_dirac_finite_and_toReal_le_of_ae
    (μ : Measure E) [IsProbabilityMeasure μ] {y : E}
    (hf : AEMeasurable f μ)
    (hdom : ∀ᵐ x ∂μ, edist (f x) (f y) ≤ (L : ℝ≥0∞) * edist x y)
    (hfinite : eW1 μ (Measure.dirac y) ≠ ∞) :
    eW1 (μ.map f) (Measure.dirac (f y)) ≠ ∞ ∧
      (eW1 (μ.map f) (Measure.dirac (f y))).toReal ≤
        (L : ℝ) * (eW1 μ (Measure.dirac y)).toReal := by
  have hle := eW1_map_dirac_le_of_ae μ hf hdom
  have hright : (L : ℝ≥0∞) * eW1 μ (Measure.dirac y) ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.coe_ne_top hfinite
  refine ⟨ne_top_of_le_ne_top hright hle, ?_⟩
  simpa only [ENNReal.toReal_mul, ENNReal.coe_toReal] using ENNReal.toReal_mono hright hle

/-- A carrying region and its actual two-point distance comparison imply the Dirac cost bound. -/
theorem eW1_map_dirac_le_on (μ : Measure E) [IsProbabilityMeasure μ] {y : E} {S : Set E}
    (hcarry : ∀ᵐ x ∂μ, x ∈ S) (hy : y ∈ S) (hf : AEMeasurable f μ)
    (hregion : ∀ x ∈ S, ∀ z ∈ S,
      edist (f x) (f z) ≤ (L : ℝ≥0∞) * edist x z) :
    eW1 (μ.map f) (Measure.dirac (f y)) ≤ (L : ℝ≥0∞) * eW1 μ (Measure.dirac y) :=
  eW1_map_dirac_le_of_ae μ hf (hcarry.mono fun x hx => hregion x hx y hy)

/-- A carrying-region comparison retains both target finiteness and its quantitative real bound. -/
theorem eW1_map_dirac_finite_and_toReal_le_on
    (μ : Measure E) [IsProbabilityMeasure μ] {y : E} {S : Set E}
    (hcarry : ∀ᵐ x ∂μ, x ∈ S) (hy : y ∈ S) (hf : AEMeasurable f μ)
    (hregion : ∀ x ∈ S, ∀ z ∈ S,
      edist (f x) (f z) ≤ (L : ℝ≥0∞) * edist x z)
    (hfinite : eW1 μ (Measure.dirac y) ≠ ∞) :
    eW1 (μ.map f) (Measure.dirac (f y)) ≠ ∞ ∧
      (eW1 (μ.map f) (Measure.dirac (f y))).toReal ≤
        (L : ℝ) * (eW1 μ (Measure.dirac y)).toReal :=
  eW1_map_dirac_finite_and_toReal_le_of_ae μ hf
    (hcarry.mono fun x hx => hregion x hx y hy) hfinite

section Family

variable {ι : Type*} {ν : ι → ℝ → Measure E} [∀ i t, IsProbabilityMeasure (ν i t)]
  {f : ℝ → E → F} {Y : ℝ → E} {B : ι → ℝ} {T : ℝ}

/-- One uniform distance factor transfers eventual finite concentration along the explicit family filter. -/
theorem family_concentration_of_eventual_bound (l : Filter ι) (hT : 0 ≤ T)
    (hSource : ∀ᶠ i in l, ∀ t ∈ Icc 0 T,
      eW1 (ν i t) (Measure.dirac (Y t)) ≠ ∞ ∧
      (eW1 (ν i t) (Measure.dirac (Y t))).toReal ≤ B i)
    (hMaps : ∀ᶠ i in l, ∀ t ∈ Icc 0 T,
      AEMeasurable (f t) (ν i t) ∧
      ∀ᵐ x ∂ν i t, edist (f t x) (f t (Y t)) ≤ (L : ℝ≥0∞) * edist x (Y t))
    (hB : Tendsto B l (𝓝 0)) :
    (∀ᶠ i in l, ∀ t ∈ Icc 0 T,
      eW1 ((ν i t).map (f t)) (Measure.dirac (f t (Y t))) ≠ ∞) ∧
      TendstoUniformlyOn
        (fun i t => (eW1 ((ν i t).map (f t)) (Measure.dirac (f t (Y t)))).toReal)
        (fun _ => 0) l (Icc 0 T) ∧
      Tendsto (fun i => timeSup
        (fun t => (eW1 ((ν i t).map (f t)) (Measure.dirac (f t (Y t)))).toReal) T)
        l (𝓝 0) := by
  apply uniform_concentration_of_bound
    (ν := fun i t => (ν i t).map (f t)) (Y := fun t => f t (Y t))
    (B := fun i => (L : ℝ) * B i) l hT
  · filter_upwards [hSource, hMaps] with i hi hmi
    intro t ht
    have h := eW1_map_dirac_finite_and_toReal_le_of_ae (ν i t)
      (hmi t ht).1 (hmi t ht).2 (hi t ht).1
    exact ⟨h.1, h.2.trans (mul_le_mul_of_nonneg_left (hi t ht).2 L.coe_nonneg)⟩
  · simpa only [mul_zero] using hB.const_mul (L : ℝ)

end Family
end Metric
end FoliationQM.WassersteinMetricTransfer
