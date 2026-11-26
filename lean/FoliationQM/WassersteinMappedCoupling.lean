module

public import FoliationQM.WassersteinCoupling
public import Mathlib.Topology.MetricSpace.Lipschitz

/-!
# Actual coupling pushforwards and finite Lipschitz transport comparison

The two marginals are proved for the actual product map. Probability
couplings make the source infimum inhabited, including a zero Lipschitz
constant. Real conversion follows a separate finite-cost certificate.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.WassersteinMetricTransfer

open MeasureTheory WassersteinCoupling
open scoped ENNReal NNReal

variable {E F : Type*} [MeasurableSpace E] [MeasurableSpace F]
  {μ ν : Measure E}

/-- Mapping both coordinates gives an actual coupling of the mapped marginals. -/
def mapCoupling (π : Coupling μ ν) (f : E → F) (hf : Measurable f) :
    Coupling (μ.map f) (ν.map f) where
  measure := π.measure.map (fun z => (f z.1, f z.2))
  fst_marginal := by
    have hm : Measurable (fun z : E × E => (f z.1, f z.2)) := by fun_prop
    rw [Measure.map_map measurable_fst hm]
    have h := congrArg (fun ρ : Measure E => ρ.map f) π.fst_marginal
    rw [Measure.map_map hf measurable_fst] at h
    simpa only [Function.comp_def] using h
  snd_marginal := by
    have hm : Measurable (fun z : E × E => (f z.1, f z.2)) := by fun_prop
    rw [Measure.map_map measurable_snd hm]
    have h := congrArg (fun ρ : Measure E => ρ.map f) π.snd_marginal
    rw [Measure.map_map hf measurable_snd] at h
    simpa only [Function.comp_def] using h

section Metric

variable [MetricSpace E] [MetricSpace F] [BorelSpace E] [BorelSpace F]
  [SecondCountableTopology F] {f : E → F} {L : ℝ≥0}

/-- The actual mapped coupling has at most the finite Lipschitz multiple of the original cost. -/
theorem cost_mapCoupling_le (π : Coupling μ ν) (hf : LipschitzWith L f) :
    cost (mapCoupling π f hf.continuous.measurable) ≤ (L : ℝ≥0∞) * cost π := by
  change (∫⁻ z : F × F, edist z.1 z.2
    ∂π.measure.map (fun z => (f z.1, f z.2))) ≤ _
  have hfM : Measurable f := hf.continuous.measurable
  have hm : Measurable (fun z : E × E => (f z.1, f z.2)) := by fun_prop
  rw [lintegral_map measurable_edist hm]
  calc
    (∫⁻ z : E × E, edist (f z.1) (f z.2) ∂π.measure) ≤
        ∫⁻ z : E × E, (L : ℝ≥0∞) * edist z.1 z.2 ∂π.measure :=
      lintegral_mono fun z => hf.edist_le_mul z.1 z.2
    _ = (L : ℝ≥0∞) * cost π :=
      lintegral_const_mul' _ _ ENNReal.coe_ne_top

/-- The genuine coupling infimum contracts under a Lipschitz map, including a zero constant. -/
theorem eW1_map_le (μ ν : Measure E) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (hf : LipschitzWith L f) :
    eW1 (μ.map f) (ν.map f) ≤ (L : ℝ≥0∞) * eW1 μ ν := by
  have : Nonempty (Coupling μ ν) := Coupling.nonempty μ ν
  change eW1 (μ.map f) (ν.map f) ≤ (L : ℝ≥0∞) * ⨅ π : Coupling μ ν, cost π
  rw [ENNReal.mul_iInf (by simp)]
  apply le_iInf
  intro π
  exact (eW1_le_cost (mapCoupling π f hf.continuous.measurable)).trans
    (cost_mapCoupling_le π hf)

/-- Finite source cost gives finite target cost before the real Lipschitz comparison is taken. -/
theorem eW1_map_finite_and_toReal_le (μ ν : Measure E) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (hf : LipschitzWith L f) (hfinite : eW1 μ ν ≠ ∞) :
    eW1 (μ.map f) (ν.map f) ≠ ∞ ∧
    (eW1 (μ.map f) (ν.map f)).toReal ≤ (L : ℝ) * (eW1 μ ν).toReal := by
  have h := eW1_map_le μ ν hf
  have hbound : (L : ℝ≥0∞) * eW1 μ ν ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.coe_ne_top hfinite
  refine ⟨ne_top_of_le_ne_top hbound h, ?_⟩
  simpa only [ENNReal.toReal_mul, ENNReal.coe_toReal] using ENNReal.toReal_mono hbound h

end Metric
end FoliationQM.WassersteinMetricTransfer
