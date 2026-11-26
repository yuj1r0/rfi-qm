module

public import FoliationQM.ActualHeisenbergDefect
public import FoliationQM.WaveMomentumQuadraticForm
public import FoliationQM.SobolevCramerRao

/-!
# Actual wave Heisenberg bound, defect and equality equation

Sources: v13 eq:heisenberg and thm:uncertainty, component kinds C and D.
The actual logarithmic score pairing and quantum quadratic-form decomposition
are derived from the same continuous locally AC wave and true derivative.
Genuine wave, derivative and position L² data give positive position variance,
the literal square-root bound and its sharp weighted equality criterion.
Actual nodal reconstruction then gives a whole-line AE complex differential
equation on saturation. No global positive amplitude or phase is assumed.
Gaussian rigidity and the source phase interpretation remain separate bridges.
-/

@[expose] public section
noncomputable section

namespace FoliationQM.WaveHeisenberg
open MeasureTheory Filter WaveScoreAlgebra WaveDensityMeasure
open WaveMomentumQuadraticForm CenteredL2Variance SobolevCramerRao

variable {u v : ℝ → ℂ}

private theorem log_pairing (hc : Continuous u)
    (hAC : ∀ a b, AbsolutelyContinuousOnInterval u a b)
    (hd : ∀ᵐ x ∂volume, HasDerivAt u (v x) x)
    (hu : MemLp u 2 volume) (hv : MemLp v 2 volume)
    (hxu : MemLp (fun x : ℝ => (x : ℂ) * u x) 2 volume)
    (hnorm : (∫ x, density (u x)) = 1) :
    (∫ x, centered (densityMeasure u) (fun y : ℝ => y) x *
      logDensityDerivative u x ∂densityMeasure u) = -1 := by
  simpa only [centered, logDensityDerivative, hnorm] using
    WaveScoreIntegrationByParts.integral_shifted_log_derivative hc hAC hd hu hv hxu
      (mean (densityMeasure u) (fun x : ℝ => x))

/-- The derived actual logarithmic-score pairing forces positive position variance. -/
theorem variance_pos (hc : Continuous u)
    (hAC : ∀ a b, AbsolutelyContinuousOnInterval u a b)
    (hd : ∀ᵐ x ∂volume, HasDerivAt u (v x) x)
    (hu : MemLp u 2 volume) (hv : MemLp v 2 volume)
    (hxu : MemLp (fun x : ℝ => (x : ℂ) * u x) 2 volume)
    (hnorm : (∫ x, density (u x)) = 1) :
    0 < variance (densityMeasure u) (fun x : ℝ => x) := by
  let : IsProbabilityMeasure (densityMeasure u) := isProbabilityMeasure hu hnorm
  exact ScoreCramerRao.variance_pos (memLp_position hc hxu)
    (memLp_log_derivative hc hd hv) (log_pairing hc hAC hd hu hv hxu hnorm)

/-- The actual uncertainty gap is the sum of the bulk-variance gap and the
genuine logarithmic-score residual, with the exact nonnegative coefficients. -/
theorem defect_eq (hc : Continuous u)
    (hAC : ∀ a b, AbsolutelyContinuousOnInterval u a b)
    (hd : ∀ᵐ x ∂volume, HasDerivAt u (v x) x)
    (hu : MemLp u 2 volume) (hv : MemLp v 2 volume)
    (hxu : MemLp (fun x : ℝ => (x : ℂ) * u x) 2 volume)
    (hnorm : (∫ x, density (u x)) = 1) (hbar : ℝ) :
    variance (densityMeasure u) (fun x : ℝ => x) * momentumVariance hbar u v -
        hbar ^ 2 / 4 =
      variance (densityMeasure u) (fun x : ℝ => x) *
        variance (densityMeasure u) (fun x => bulk hbar (u x) (v x)) +
      (hbar ^ 2 / 4) * variance (densityMeasure u) (fun x : ℝ => x) *
        (∫ x, ScoreCramerRao.scoreResidual (densityMeasure u)
          (fun y : ℝ => y) (logDensityDerivative u) x ^ 2 ∂densityMeasure u) := by
  let : IsProbabilityMeasure (densityMeasure u) := isProbabilityMeasure hu hnorm
  exact ActualHeisenbergDefect.defect_eq (memLp_position hc hxu)
    (memLp_log_derivative hc hd hv) (log_pairing hc hAC hd hu hv hxu hnorm)
    hbar (momentumVariance hbar u v)
    (variance_decomposition hc hAC hd hu hv hnorm hbar)

/-- The actual finite position and momentum quadratic variances satisfy the
squared Heisenberg lower bound. -/
theorem squared_bound (hc : Continuous u)
    (hAC : ∀ a b, AbsolutelyContinuousOnInterval u a b)
    (hd : ∀ᵐ x ∂volume, HasDerivAt u (v x) x)
    (hu : MemLp u 2 volume) (hv : MemLp v 2 volume)
    (hxu : MemLp (fun x : ℝ => (x : ℂ) * u x) 2 volume)
    (hnorm : (∫ x, density (u x)) = 1) (hbar : ℝ) :
    hbar ^ 2 / 4 ≤
      variance (densityMeasure u) (fun x : ℝ => x) * momentumVariance hbar u v := by
  let : IsProbabilityMeasure (densityMeasure u) := isProbabilityMeasure hu hnorm
  exact ActualHeisenbergDefect.squared_bound (memLp_position hc hxu)
    (memLp_log_derivative hc hd hv) (log_pairing hc hAC hd hu hv hxu hnorm)
    hbar (momentumVariance hbar u v)
    (variance_decomposition hc hAC hd hu hv hnorm hbar)

/-- The literal nonnegative square-root standard deviations satisfy the
source Heisenberg inequality for positive hbar. -/
theorem sqrt_bound (hc : Continuous u)
    (hAC : ∀ a b, AbsolutelyContinuousOnInterval u a b)
    (hd : ∀ᵐ x ∂volume, HasDerivAt u (v x) x)
    (hu : MemLp u 2 volume) (hv : MemLp v 2 volume)
    (hxu : MemLp (fun x : ℝ => (x : ℂ) * u x) 2 volume)
    (hnorm : (∫ x, density (u x)) = 1) (hbar : ℝ) (hhbar : 0 < hbar) :
    hbar / 2 ≤ Real.sqrt (variance (densityMeasure u) (fun x : ℝ => x)) *
      Real.sqrt (momentumVariance hbar u v) := by
  let : IsProbabilityMeasure (densityMeasure u) := isProbabilityMeasure hu hnorm
  exact ActualHeisenbergDefect.sqrt_bound (memLp_position hc hxu)
    (memLp_log_derivative hc hd hv) (log_pairing hc hAC hd hu hv hxu hnorm)
    hbar (momentumVariance hbar u v)
    (variance_decomposition hc hAC hd hu hv hnorm hbar) hhbar

/-- Saturation is equivalent to actual constant bulk momentum at its genuine
mean and the affine logarithmic score, both for the actual density measure. -/
theorem equality_iff (hc : Continuous u)
    (hAC : ∀ a b, AbsolutelyContinuousOnInterval u a b)
    (hd : ∀ᵐ x ∂volume, HasDerivAt u (v x) x)
    (hu : MemLp u 2 volume) (hv : MemLp v 2 volume)
    (hxu : MemLp (fun x : ℝ => (x : ℂ) * u x) 2 volume)
    (hnorm : (∫ x, density (u x)) = 1) (hbar : ℝ) (hhbar : 0 < hbar) :
    Real.sqrt (variance (densityMeasure u) (fun x : ℝ => x)) *
        Real.sqrt (momentumVariance hbar u v) = hbar / 2 ↔
      (∀ᵐ x ∂densityMeasure u, bulk hbar (u x) (v x) = meanMomentum hbar u v) ∧
      (∀ᵐ x ∂densityMeasure u, logDensityDerivative u x =
        -(x - mean (densityMeasure u) (fun y : ℝ => y)) /
          variance (densityMeasure u) (fun y : ℝ => y)) := by
  let : IsProbabilityMeasure (densityMeasure u) := isProbabilityMeasure hu hnorm
  have hm : meanMomentum hbar u v =
      mean (densityMeasure u) (fun x => bulk hbar (u x) (v x)) := by
    simpa only [meanMomentum, Complex.ofReal_re] using
      congrArg Complex.re (quantumExpectation_eq_bulk_mean hc hAC hd hu hv hbar)
  rw [hm]
  simpa only [centered, logDensityDerivative] using
    ActualHeisenbergDefect.equality_iff (memLp_position hc hxu) (memLp_bulk hc hv hbar)
      (memLp_log_derivative hc hd hv) (log_pairing hc hAC hd hu hv hxu hnorm)
      hbar (momentumVariance hbar u v)
      (variance_decomposition hc hAC hd hu hv hnorm hbar) hhbar

/-- Saturation derives the actual whole-line AE affine complex wave equation,
using the true nodal derivative theorem rather than assuming global positivity. -/
theorem equality_ode (hc : Continuous u)
    (hAC : ∀ a b, AbsolutelyContinuousOnInterval u a b)
    (hd : ∀ᵐ x ∂volume, HasDerivAt u (v x) x)
    (hu : MemLp u 2 volume) (hv : MemLp v 2 volume)
    (hxu : MemLp (fun x : ℝ => (x : ℂ) * u x) 2 volume)
    (hnorm : (∫ x, density (u x)) = 1) (hbar : ℝ) (hhbar : 0 < hbar)
    (heq : Real.sqrt (variance (densityMeasure u) (fun x : ℝ => x)) *
      Real.sqrt (momentumVariance hbar u v) = hbar / 2) :
    ∀ᵐ x ∂volume, v x =
      (((-((x - mean (densityMeasure u) (fun y : ℝ => y)) /
          (2 * variance (densityMeasure u) (fun y : ℝ => y))) : ℝ) : ℂ) +
        Complex.I * ((meanMomentum hbar u v / hbar : ℝ) : ℂ)) * u x := by
  obtain ⟨hb, hs⟩ := (equality_iff hc hAC hd hu hv hxu hnorm hbar hhbar).mp heq
  have hscore : ∀ᵐ x ∂densityMeasure u, score (u x) (v x) =
      -(x - mean (densityMeasure u) (fun y : ℝ => y)) /
        variance (densityMeasure u) (fun y : ℝ => y) := by
    filter_upwards [hs, ae_log_derivative_eq_score hc hd] with x hx he
    exact he.symm.trans hx
  have hb' := (ae_iff_positive hc
    (fun x => bulk hbar (u x) (v x) = meanMomentum hbar u v)).mp hb
  have hs' := (ae_iff_positive hc (fun x => score (u x) (v x) =
    -(x - mean (densityMeasure u) (fun y : ℝ => y)) /
      variance (densityMeasure u) (fun y : ℝ => y))).mp hscore
  have hV := variance_pos hc hAC hd hu hv hxu hnorm
  filter_upwards [hb', hs', SobolevDensity.ae_derivative_reconstruction hd] with x hbx hsx hr
  by_cases hz : u x = 0
  · simpa only [hz, mul_zero] using hr
  · have hpos := (density_pos_iff (u x)).mpr hz
    have hbulk : hbar * phaseRate (u x) (v x) = meanMomentum hbar u v := hbx hpos
    have hp : phaseRate (u x) (v x) = meanMomentum hbar u v / hbar := by
      apply (eq_div_iff hhbar.ne').mpr
      simpa only [mul_comm] using hbulk
    have hsx' := hsx hpos
    have hhalf :
        (-(x - mean (densityMeasure u) (fun y : ℝ => y)) /
          variance (densityMeasure u) (fun y : ℝ => y)) / 2 =
        -((x - mean (densityMeasure u) (fun y : ℝ => y)) /
          (2 * variance (densityMeasure u) (fun y : ℝ => y))) := by
      field_simp [hV.ne']
    rw [hr, hsx', hp, hhalf]

end FoliationQM.WaveHeisenberg
