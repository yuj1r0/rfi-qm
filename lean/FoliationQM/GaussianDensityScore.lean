module

public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Tactic.FieldSimp

/-!
# The actual score of a positive-variance Gaussian density

Sources: v13 eq:cramer_rao and thm:uncertainty, component kinds C and D.
The density and probability measure are Mathlib's actual Gaussian objects.
The log-score is derived by differentiation; positivity excludes the zero-
variance Dirac measure from the density interpretation. The weighted integral
bridge below supplies genuine integrability, not only a totalized equality.
This is a Gaussian analytic witness, not the universal Sobolev theorem.
-/

@[expose] public section
noncomputable section

namespace FoliationQM.GaussianDensityScore
open MeasureTheory ProbabilityTheory
open scoped NNReal ContDiff

/-- The affine score that will be identified with the actual logarithmic derivative. -/
def score (m : ℝ) (v : ℝ≥0) (x : ℝ) : ℝ := -(x - m) / (v : ℝ)

/-- The Gaussian density is smooth as a function of its position argument. -/
theorem contDiff_density (m : ℝ) (v : ℝ≥0) :
    ContDiff ℝ ∞ (gaussianPDFReal m v) := by
  unfold gaussianPDFReal
  fun_prop

/-- The actual affine score is smooth in position. -/
theorem contDiff_score (m : ℝ) (v : ℝ≥0) : ContDiff ℝ ∞ (score m v) := by
  unfold score
  fun_prop

/-- Differentiating the literal normalized Gaussian gives score times density. -/
theorem hasDerivAt_density (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) (x : ℝ) :
    HasDerivAt (gaussianPDFReal m v)
      (score m v x * gaussianPDFReal m v x) x := by
  have hvR : (v : ℝ) ≠ 0 := NNReal.coe_ne_zero.mpr hv
  have h := (((((hasDerivAt_id x).sub_const m).pow 2).neg).div_const
    (2 * (v : ℝ))).exp.const_mul (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹
  simp only [Pi.neg_apply, Pi.pow_apply, id_eq, Nat.reduceSub, pow_one,
    Nat.cast_ofNat, mul_one] at h
  convert h using 1
  · rfl
  · simp only [score, gaussianPDFReal]
    field_simp [hvR]

/-- The true density derivative is the affine score multiplied by the density. -/
theorem deriv_density (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) (x : ℝ) :
    deriv (gaussianPDFReal m v) x = score m v x * gaussianPDFReal m v x :=
  (hasDerivAt_density m hv x).deriv

/-- Positive variance gives a genuine logarithmic density derivative at every point. -/
theorem hasDerivAt_log_density (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) (x : ℝ) :
    HasDerivAt (fun y => Real.log (gaussianPDFReal m v y)) (score m v x) x := by
  have hp := (gaussianPDFReal_pos m v x hv).ne'
  simpa only [mul_div_cancel_right₀ _ hp] using (hasDerivAt_density m hv x).log hp

/-- The defined affine score equals the actual derivative of the log density. -/
theorem deriv_log_density (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) (x : ℝ) :
    deriv (fun y => Real.log (gaussianPDFReal m v y)) x = score m v x :=
  (hasDerivAt_log_density m hv x).deriv

/-- Density division in the score is justified by the actual positive Gaussian density. -/
theorem score_eq_deriv_div (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) (x : ℝ) :
    score m v x = deriv (gaussianPDFReal m v) x / gaussianPDFReal m v x := by
  rw [deriv_density m hv x, mul_div_cancel_right₀ _ (gaussianPDFReal_pos m v x hv).ne']

/-- Genuine Gaussian-measure integrability is equivalent to integrability of the density-weighted function. -/
theorem integrable_weighted_iff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) {f : ℝ → E} :
    Integrable f (gaussianReal m v) ↔
      Integrable (fun x => gaussianPDFReal m v x • f x) volume := by
  rw [gaussianReal_of_var_ne_zero m hv]
  have h := integrable_withDensity_iff_integrable_smul' (μ := volume) (g := f)
    (measurable_gaussianPDF m v) (ae_of_all _ fun _ => gaussianPDF_lt_top)
  simpa only [toReal_gaussianPDF] using h

end FoliationQM.GaussianDensityScore
