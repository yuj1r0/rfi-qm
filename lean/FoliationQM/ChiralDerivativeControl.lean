module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Analysis.Calculus.ContDiff.Operations
/-!
# Small chiral angle amplitudes do not control their derivatives

Source qualification: the prose small-chiral-angle limit following v13
`eq:sl2c_fisher_metric_main` must specify derivative control when removing
the chiral quadratic term of `eq:spinor_quadratic_exact`. The actual family
beta_eps(x)=eps*sin(x/eps) is smooth as a function of x for each fixed eps.
For every positive amplitude threshold it supplies a positive eps with a
global pointwise amplitude bound, yet the actual derivative at zero is one.

The fixed-density, fixed-hbar correction below is the source chiral term
for one positive-sign derivative direction. It is a genuine derivative
square and remains nonzero under these arbitrarily small amplitude bounds.
This qualifies an amplitude-only interpretation of the limit prose. It
does not contradict a limit that explicitly controls first derivatives,
claim a field equation or physical solution family, or change a reference.
-/

@[expose] public section
noncomputable section
open scoped ContDiff
namespace FoliationQM.ChiralDerivativeControl

/-- The actual real small-amplitude oscillatory angle family, with amplitude eps and wavelength proportional to eps. -/
def angle (eps x : ℝ) : ℝ := eps*Real.sin (x/eps)

/-- For every fixed parameter the actual angle field is smooth to any differentiability order. -/
theorem contDiff_angle (eps : ℝ) (n : WithTop ℕ∞) : ContDiff ℝ n (angle eps) := by
  simpa only [angle, id_eq] using!
    (contDiff_const.mul (((contDiff_id : ContDiff ℝ n (fun x : ℝ => x)).div_const eps).sin))

/-- A nonnegative parameter bounds the actual angle amplitude uniformly at every real point. -/
theorem angle_abs_le (eps : ℝ) (heps : 0 ≤ eps) (x : ℝ) : |angle eps x| ≤ eps := by
  rw [angle, abs_mul, abs_of_nonneg heps]
  exact (mul_le_mul_of_nonneg_left (Real.abs_sin_le_one (x/eps)) heps).trans_eq (mul_one eps)

/-- Every member of the actual angle family vanishes at the origin. -/
theorem angle_zero (eps : ℝ) : angle eps 0 = 0 := by simp [angle]

/-- The genuine real derivative of the nonzero-parameter angle field is the unscaled cosine. -/
theorem hasDerivAt_angle (eps : ℝ) (heps : eps ≠ 0) (x : ℝ) :
    HasDerivAt (angle eps) (Real.cos (x/eps)) x := by
  have hd := ((hasDerivAt_id x).div_const eps).sin.const_mul eps
  convert hd using 1
  · rfl
  · simp only [id_eq]
    field_simp

/-- Every nonzero-parameter angle field has the genuine derivative one at the origin. -/
theorem hasDerivAt_angle_zero (eps : ℝ) (heps : eps ≠ 0) : HasDerivAt (angle eps) 1 0 := by
  simpa using hasDerivAt_angle eps heps 0

/-- The actual derivative operator evaluates to one at the origin for every nonzero parameter. -/
theorem deriv_angle_zero (eps : ℝ) (heps : eps ≠ 0) : deriv (angle eps) 0 = 1 :=
  (hasDerivAt_angle_zero eps heps).deriv

/-- The actual Frechet derivative at the origin is the identity continuous-linear map. -/
theorem hasFDerivAt_angle_zero (eps : ℝ) (heps : eps ≠ 0) :
    HasFDerivAt (angle eps) (ContinuousLinearMap.id ℝ ℝ) 0 := by
  apply hasFDerivAt_iff_hasDerivAt.mpr
  exact hasDerivAt_angle_zero eps heps

/-- The genuine Frechet derivative at the origin preserves every real tangent direction. -/
theorem fderiv_angle_zero_apply (eps : ℝ) (heps : eps ≠ 0) (v : ℝ) :
    fderiv ℝ (angle eps) 0 v = v := by
  rw [(hasFDerivAt_angle_zero eps heps).fderiv]
  rfl

/-- The actual derivative square stays exactly one despite the small angle amplitudes. -/
theorem derivative_square_at_zero (eps : ℝ) (heps : eps ≠ 0) :
    (deriv (angle eps) 0)^2 = 1 := by rw [deriv_angle_zero eps heps]; norm_num

/-- Every positive global amplitude threshold admits a smooth positive-parameter angle field with actual derivative one at the origin. -/
theorem arbitrarily_small_angle_fixed_derivative (delta : ℝ) (hdelta : 0 < delta) :
    ∃ eps : ℝ, 0 < eps ∧ ContDiff ℝ ∞ (angle eps) ∧
      (∀ x : ℝ, |angle eps x| ≤ delta) ∧ angle eps 0 = 0 ∧ deriv (angle eps) 0 = 1 := by
  refine ⟨delta, hdelta, contDiff_angle delta ∞, ?_, angle_zero delta,
    deriv_angle_zero delta hdelta.ne'⟩
  exact angle_abs_le delta hdelta.le

/-- The source one-direction chiral quadratic correction retains its fixed coefficient for every nonzero parameter. -/
theorem chiral_quadratic_at_zero (rho hbar eps : ℝ) (heps : eps ≠ 0) :
    -(rho*hbar^2/4)*(deriv (angle eps) 0)^2 = -(rho*hbar^2/4) := by
  rw [derivative_square_at_zero eps heps, mul_one]

/-- At fixed positive density and action scale the actual chiral derivative-square correction is nonzero. -/
theorem chiral_quadratic_nonzero (rho hbar eps : ℝ)
    (hrho : 0 < rho) (hhbar : 0 < hbar) (heps : eps ≠ 0) :
    -(rho*hbar^2/4)*(deriv (angle eps) 0)^2 ≠ 0 := by
  rw [chiral_quadratic_at_zero rho hbar eps heps]
  have hpos : 0 < rho*hbar^2/4 := by positivity
  exact neg_ne_zero.mpr hpos.ne'

/-- Arbitrarily small uniform smooth angle amplitudes leave the same nonzero actual chiral derivative-square term at fixed positive density and action scale. -/
theorem arbitrarily_small_angle_nonzero_chiral_term (rho hbar delta : ℝ)
    (hrho : 0 < rho) (hhbar : 0 < hbar) (hdelta : 0 < delta) :
    ∃ eps : ℝ, 0 < eps ∧ ContDiff ℝ ∞ (angle eps) ∧
      (∀ x : ℝ, |angle eps x| ≤ delta) ∧
      -(rho*hbar^2/4)*(deriv (angle eps) 0)^2 = -(rho*hbar^2/4) ∧
      -(rho*hbar^2/4)*(deriv (angle eps) 0)^2 ≠ 0 := by
  exact ⟨delta, hdelta, contDiff_angle delta ∞, angle_abs_le delta hdelta.le,
    chiral_quadratic_at_zero rho hbar delta hdelta.ne',
    chiral_quadratic_nonzero rho hbar delta hrho hhbar hdelta.ne'⟩

end FoliationQM.ChiralDerivativeControl
