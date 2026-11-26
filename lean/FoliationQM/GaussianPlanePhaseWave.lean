module

public import FoliationQM.GaussianScoreMoments
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.Complex.RealDeriv

/-!
# Actual normalized Gaussian plane-phase waves

Sources: v13 thm:uncertainty and eq:p_var_decomp, component kinds C and D.
The literal square root of the Gaussian density has a linear complex phase.
Its pointwise derivative, normalization, and genuine square integrability of
the wave, position times the wave, and derivative are proved below. These are
analytic witnesses; no identification with a distributional Sobolev space or
universal momentum-variance theorem is asserted. Physical momentum is hbar
times the phase frequency k. Positive variance excludes the Dirac branch.
-/

@[expose] public section
noncomputable section

namespace FoliationQM.GaussianPlanePhaseWave
open MeasureTheory ProbabilityTheory GaussianDensityScore
open scoped NNReal

/-- The literal Gaussian amplitude with a real affine phase. -/
def wave (m : ℝ) (v : ℝ≥0) (k theta : ℝ) (x : ℝ) : ℂ :=
  (Real.sqrt (gaussianPDFReal m v x) : ℂ) *
    Complex.exp (Complex.I * ((k * x + theta : ℝ) : ℂ))

/-- The actual complex norm square is exactly the Gaussian density. -/
theorem norm_sq (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) (k theta x : ℝ) :
    ‖wave m v k theta x‖ ^ 2 = gaussianPDFReal m v x := by
  simp only [wave, norm_mul, Complex.norm_exp_I_mul_ofReal, mul_one,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  exact Real.sq_sqrt (gaussianPDFReal_pos m v x hv).le

/-- Differentiating the defined wave gives its score and phase-frequency coefficient. -/
theorem hasDerivAt_wave (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) (k theta x : ℝ) :
    HasDerivAt (wave m v k theta)
      ((((score m v x / 2 : ℝ) : ℂ) + Complex.I * (k : ℂ)) *
        wave m v k theta x) x := by
  have hp := gaussianPDFReal_pos m v x hv
  have hs := Real.sqrt_pos.mpr hp
  have hsquare := Real.sq_sqrt hp.le
  have hamp : score m v x * gaussianPDFReal m v x /
      (2 * Real.sqrt (gaussianPDFReal m v x)) =
        score m v x / 2 * Real.sqrt (gaussianPDFReal m v x) := by
    calc
      _ = score m v x * Real.sqrt (gaussianPDFReal m v x) ^ 2 /
          (2 * Real.sqrt (gaussianPDFReal m v x)) := by rw [hsquare]
      _ = _ := by field_simp [hs.ne']
  have ha : HasDerivAt (fun y => Real.sqrt (gaussianPDFReal m v y))
      (score m v x / 2 * Real.sqrt (gaussianPDFReal m v x)) x := by
    simpa only [hamp] using (hasDerivAt_density m hv x).sqrt hp.ne'
  have hphase := ((((hasDerivAt_id x).const_mul k).add_const theta).ofReal_comp.const_mul
    Complex.I).cexp
  convert ha.ofReal_comp.mul hphase using 1
  · rfl
  · simp [wave]
    ring

/-- The actual derivative operator agrees with the proved pointwise formula. -/
theorem deriv_wave (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) (k theta x : ℝ) :
    deriv (wave m v k theta) x =
      ((((score m v x / 2 : ℝ) : ℂ) + Complex.I * (k : ℂ)) *
        wave m v k theta x) :=
  (hasDerivAt_wave m hv k theta x).deriv

/-- The Gaussian plane-phase wave is differentiable everywhere. -/
theorem differentiable_wave (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) (k theta : ℝ) :
    Differentiable ℝ (wave m v k theta) :=
  fun x => (hasDerivAt_wave m hv k theta x).differentiableAt

/-- The literal wave is continuous, hence supplies genuine measurability. -/
theorem continuous_wave (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) (k theta : ℝ) :
    Continuous (wave m v k theta) :=
  (differentiable_wave m hv k theta).continuous

/-- Its true norm-square integral is one. -/
theorem integral_norm_sq (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) (k theta : ℝ) :
    (∫ x, ‖wave m v k theta x‖ ^ 2) = 1 := by
  simp_rw [norm_sq m hv k theta]
  exact integral_gaussianPDFReal_eq_one m hv

/-- The normalized wave belongs to the actual complex L² space. -/
theorem memLp_wave (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) (k theta : ℝ) :
    MemLp (wave m v k theta) 2 volume := by
  apply (memLp_two_iff_integrable_sq_norm
    (continuous_wave m hv k theta).aestronglyMeasurable).mpr
  simpa only [norm_sq m hv k theta] using integrable_gaussianPDFReal m v

/-- Multiplication by the position coordinate still gives a genuine complex L² function. -/
theorem memLp_position_mul_wave (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) (k theta : ℝ) :
    MemLp (fun x : ℝ => (x : ℂ) * wave m v k theta x) 2 volume := by
  have hc : Continuous (fun x : ℝ => (x : ℂ) * wave m v k theta x) :=
    Complex.continuous_ofReal.mul (continuous_wave m hv k theta)
  apply (memLp_two_iff_integrable_sq_norm hc.aestronglyMeasurable).mpr
  simpa only [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs,
    norm_sq m hv k theta, mul_comm] using
    GaussianScoreMoments.integrable_weighted_position_sq m hv

/-- The derivative's true norm square separates amplitude and phase contributions. -/
theorem norm_sq_deriv (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) (k theta x : ℝ) :
    ‖deriv (wave m v k theta) x‖ ^ 2 =
      (score m v x ^ 2 / 4 + k ^ 2) * gaussianPDFReal m v x := by
  rw [deriv_wave m hv k theta x, norm_mul, mul_pow, norm_sq m hv k theta x]
  congr 1
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.ofReal_re,
    Complex.mul_re, Complex.I_re, Complex.ofReal_im, Complex.I_im, zero_mul, mul_zero,
    sub_zero, add_zero, Complex.add_im, Complex.mul_im, one_mul, zero_add]
  ring

private theorem integrable_derivative_density (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) (k : ℝ) :
    Integrable (fun x => (score m v x ^ 2 / 4 + k ^ 2) * gaussianPDFReal m v x) := by
  have h := ((GaussianScoreMoments.integrable_weighted_score_sq m hv).div_const 4).add
    ((integrable_gaussianPDFReal m v).mul_const (k ^ 2))
  convert h using 1
  funext x
  simp only [Pi.add_apply]
  ring

/-- The actual derivative is itself a genuine square-integrable complex function. -/
theorem memLp_deriv_wave (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) (k theta : ℝ) :
    MemLp (deriv (wave m v k theta)) 2 volume := by
  have he : deriv (wave m v k theta) = fun x =>
      ((((score m v x / 2 : ℝ) : ℂ) + Complex.I * (k : ℂ)) *
        wave m v k theta x) := funext (deriv_wave m hv k theta)
  have hc : Continuous (deriv (wave m v k theta)) := by
    rw [he]
    exact ((Complex.continuous_ofReal.comp ((contDiff_score m v).continuous.div_const 2)).add
      continuous_const).mul (continuous_wave m hv k theta)
  apply (memLp_two_iff_integrable_sq_norm hc.aestronglyMeasurable).mpr
  simpa only [norm_sq_deriv m hv k theta] using integrable_derivative_density m hv k

/-- Its actual integrated derivative energy is the Gaussian amplitude term plus phase frequency squared. -/
theorem integral_norm_sq_deriv (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) (k theta : ℝ) :
    (∫ x, ‖deriv (wave m v k theta) x‖ ^ 2) = 1 / (4 * (v : ℝ)) + k ^ 2 := by
  have he : (fun x => ‖deriv (wave m v k theta) x‖ ^ 2) =
      fun x => (gaussianPDFReal m v x * score m v x ^ 2) / 4 +
        gaussianPDFReal m v x * k ^ 2 := by
    funext x
    rw [norm_sq_deriv m hv k theta x]
    ring
  rw [he, integral_add
    ((GaussianScoreMoments.integrable_weighted_score_sq m hv).div_const 4)
    ((integrable_gaussianPDFReal m v).mul_const (k ^ 2)), integral_div,
    integral_mul_const, GaussianScoreMoments.integral_weighted_score_sq m hv,
    integral_gaussianPDFReal_eq_one m hv]
  ring

end FoliationQM.GaussianPlanePhaseWave
