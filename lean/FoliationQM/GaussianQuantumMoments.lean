module

public import FoliationQM.GaussianWaveRigidity
public import FoliationQM.WaveMomentumQuadraticForm

/-!
# Exact quantum moments of the actual Gaussian wave

Sources: v13 thm:uncertainty and eq:heisenberg, component kinds C and D.
The literal normalized Gaussian wave has exact current and momentum
quadratic-form moments. Genuine L² wave and derivative bounds justify the
integral identities, and its actual Gaussian density measure supplies the
position and Fisher moments. The variance parameter is positive; the action
scale and quadratic-form center may be any real numbers. Physical momentum
is hbar times the phase frequency. The original-Lp realization is separate.
-/

@[expose] public section
noncomputable section

namespace FoliationQM.GaussianQuantumMoments
open MeasureTheory ProbabilityTheory Filter GaussianPlanePhaseWave
open WaveScoreAlgebra WaveDensityMeasure WaveMomentumQuadraticForm
open scoped NNReal

private theorem densityMeasure_wave (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0)
    (k theta : ℝ) : densityMeasure (wave m v k theta) = gaussianReal m v := by
  rw [densityMeasure, gaussianReal_of_var_ne_zero m hv, gaussianPDF_def]
  apply congrArg (Measure.withDensity volume)
  funext x
  exact congrArg ENNReal.ofReal (norm_sq m hv k theta x)

private theorem fisher_wave (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) (k theta : ℝ) :
    (∫ x, (deriv (fun y => Real.log (density (wave m v k theta y))) x) ^ 2
      ∂densityMeasure (wave m v k theta)) = 1 / (v : ℝ) := by
  have hlog : (fun y => Real.log (density (wave m v k theta y))) =
      fun y => Real.log (gaussianPDFReal m v y) := by
    funext y
    exact congrArg Real.log (norm_sq m hv k theta y)
  rw [hlog, densityMeasure_wave m hv k theta]
  simp_rw [GaussianDensityScore.deriv_log_density m hv]
  exact GaussianScoreMoments.integral_score_sq m hv

/-- The actual derivative quotient gives physical bulk momentum hbar times frequency. -/
theorem bulk_wave (hbar m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) (k theta x : ℝ) :
    bulk hbar (wave m v k theta x) (deriv (wave m v k theta) x) = hbar * k := by
  rw [bulk, phaseRate_eq_im_div, deriv_wave m hv k theta x,
    mul_div_cancel_right₀ _ (GaussianWaveRigidity.wave_ne_zero m hv k theta x)]
  simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re,
    Complex.I_im, Complex.ofReal_re, zero_mul, one_mul, zero_add]

/-- The genuine finite complex current integral is the real physical momentum mean. -/
theorem quantumExpectation_wave (hbar m : ℝ) {v : ℝ≥0} (hv : v ≠ 0)
    (k theta : ℝ) :
    quantumExpectation hbar (wave m v k theta) (deriv (wave m v k theta)) =
      ((hbar * k : ℝ) : ℂ) := by
  have hAC (a b : ℝ) : AbsolutelyContinuousOnInterval (wave m v k theta) a b :=
    (GaussianWaveRigidity.contDiff_wave m hv k theta).contDiffOn.absolutelyContinuousOnInterval
  have hd : ∀ᵐ x ∂volume,
      HasDerivAt (wave m v k theta) (deriv (wave m v k theta) x) x :=
    Eventually.of_forall fun x => (differentiable_wave m hv k theta x).hasDerivAt
  let : IsProbabilityMeasure (densityMeasure (wave m v k theta)) :=
    isProbabilityMeasure (memLp_wave m hv k theta) (integral_norm_sq m hv k theta)
  rw [quantumExpectation_eq_bulk_mean (continuous_wave m hv k theta) hAC hd
    (memLp_wave m hv k theta) (memLp_deriv_wave m hv k theta) hbar]
  simp_rw [bulk_wave hbar m hv k theta]
  rw [CenteredL2Variance.mean_const]

/-- The actual real momentum center equals hbar times the phase frequency. -/
theorem meanMomentum_wave (hbar m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) (k theta : ℝ) :
    meanMomentum hbar (wave m v k theta) (deriv (wave m v k theta)) = hbar * k := by
  simpa only [meanMomentum, Complex.ofReal_re] using
    congrArg Complex.re (quantumExpectation_wave hbar m hv k theta)

/-- Every real-centered genuine momentum quadratic form has its exact Gaussian value. -/
theorem quadraticMoment_wave (hbar p m : ℝ) {v : ℝ≥0} (hv : v ≠ 0)
    (k theta : ℝ) :
    quadraticMoment hbar p (wave m v k theta) (deriv (wave m v k theta)) =
      (hbar * k - p) ^ 2 + hbar ^ 2 / (4 * (v : ℝ)) := by
  have hd : ∀ᵐ x ∂volume,
      HasDerivAt (wave m v k theta) (deriv (wave m v k theta) x) x :=
    Eventually.of_forall fun x => (differentiable_wave m hv k theta x).hasDerivAt
  let : IsProbabilityMeasure (densityMeasure (wave m v k theta)) :=
    isProbabilityMeasure (memLp_wave m hv k theta) (integral_norm_sq m hv k theta)
  rw [quadraticMoment_eq (continuous_wave m hv k theta) hd
    (memLp_wave m hv k theta) (memLp_deriv_wave m hv k theta)
    (integral_norm_sq m hv k theta) hbar p, fisher_wave m hv k theta]
  simp_rw [bulk_wave hbar m hv k theta]
  change CenteredL2Variance.mean (densityMeasure (wave m v k theta))
    (fun _ : ℝ => (hbar * k - p) ^ 2) + _ = _
  rw [CenteredL2Variance.mean_const]
  ring

/-- Centering the genuine quantum quadratic form at its actual mean gives hbar²/(4v). -/
theorem momentumVariance_wave (hbar m : ℝ) {v : ℝ≥0} (hv : v ≠ 0)
    (k theta : ℝ) :
    momentumVariance hbar (wave m v k theta) (deriv (wave m v k theta)) =
      hbar ^ 2 / (4 * (v : ℝ)) := by
  rw [momentumVariance, meanMomentum_wave hbar m hv k theta,
    quadraticMoment_wave hbar (hbar * k) m hv k theta]
  simp

/-- The actual density-weighted position mean is the Gaussian mean parameter. -/
theorem position_mean_wave (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) (k theta : ℝ) :
    CenteredL2Variance.mean (densityMeasure (wave m v k theta)) (fun x : ℝ => x) = m := by
  rw [densityMeasure_wave m hv k theta, GaussianScoreMoments.mean_position]

/-- The actual centered position moment is the positive Gaussian variance parameter. -/
theorem position_variance_wave (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) (k theta : ℝ) :
    CenteredL2Variance.variance (densityMeasure (wave m v k theta)) (fun x : ℝ => x) =
      (v : ℝ) := by
  rw [densityMeasure_wave m hv k theta, GaussianScoreMoments.variance_position]

end FoliationQM.GaussianQuantumMoments
