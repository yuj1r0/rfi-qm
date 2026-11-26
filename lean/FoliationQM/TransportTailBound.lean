module

public import FoliationQM.WassersteinDirac
public import FoliationQM.WassersteinFiniteMoment

/-!
# Tail probabilities from genuine first moments

Markov's inequality bounds the actual probability outside a positive-radius
ball. The transport adapter first derives distance integrability from finite
extended Dirac cost, before identifying its real value with the moment.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.TransportTailBound

open MeasureTheory Filter WassersteinCoupling
open scoped ENNReal

variable {E : Type*} [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
  {ν : Measure E} [IsProbabilityMeasure ν] {y : E} {r : ℝ}

omit [BorelSpace E] in
/-- An integrable distance moment bounds the actual strict tail at every positive radius. -/
theorem tail_real_le_moment (hr : 0 < r)
    (hdist : Integrable (fun x => dist x y) ν) :
    ν.real {x | r < dist x y} ≤ (∫ x, dist x y ∂ν) / r := by
  have hm := mul_meas_ge_le_integral_of_nonneg
    (Eventually.of_forall fun x : E => dist_nonneg (x := x) (y := y)) hdist r
  have hs : ν.real {x | r < dist x y} ≤ ν.real {x | r ≤ dist x y} :=
    measureReal_mono (by
      intro x hx
      change r < dist x y at hx
      change r ≤ dist x y
      exact hx.le)
  apply (le_div_iff₀ hr).2
  simpa only [mul_comm] using (mul_le_mul_of_nonneg_left hs hr.le).trans hm

/-- Finite genuine Dirac transport cost bounds the strict tail after proving actual distance integrability. -/
theorem tail_real_le_cost (hr : 0 < r)
    (hfinite : eW1 ν (Measure.dirac y) ≠ ∞) :
    ν.real {x | r < dist x y} ≤ (eW1 ν (Measure.dirac y)).toReal / r := by
  have hm : WassersteinFiniteMoment.moment ν y < ∞ := by
    rw [WassersteinFiniteMoment.moment, ← WassersteinDirac.eW1_dirac]
    exact lt_top_iff_ne_top.mpr hfinite
  have hd := (WassersteinFiniteMoment.moment_lt_top_iff_integrable_dist ν y).mp hm
  rw [WassersteinDirac.eW1_dirac_toReal hd]
  exact tail_real_le_moment hr hd

end FoliationQM.TransportTailBound
