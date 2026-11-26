module

public import FoliationQM.GaussianPlanePhaseWave
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

/-!
# Gaussian rigidity for the actual almost-everywhere saturation equation

Sources: v13 thm:uncertainty and eq:heisenberg, kinds C and D.
An actual locally absolutely continuous complex function satisfying the
Gaussian first-order equation is a constant multiple of the literal normalized
Gaussian wave. Normalization reduces that constant to a global phase. The
equation is an explicit input here; the source application derives it from
equality in the actual uncertainty bound. No nonvanishing of the unknown
function, global phase lift, or derivative of an arbitrary Lp representative
is assumed.
-/

@[expose] public section
noncomputable section

namespace FoliationQM.GaussianWaveRigidity
open MeasureTheory ProbabilityTheory GaussianDensityScore GaussianPlanePhaseWave
open scoped NNReal

/-- Positive Gaussian variance makes the actual reference wave nonzero everywhere. -/
theorem wave_ne_zero (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) (k theta x : ℝ) :
    wave m v k theta x ≠ 0 := by
  have hp : 0 < ‖wave m v k theta x‖ ^ 2 := by
    rw [norm_sq m hv k theta x]
    exact gaussianPDFReal_pos m v x hv
  intro hz
  simp only [hz, norm_zero, zero_pow (by decide : 2 ≠ 0), lt_self_iff_false] at hp

/-- The proved derivative formula is continuous, giving a genuine C¹ reference wave. -/
theorem contDiff_wave (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) (k theta : ℝ) :
    ContDiff ℝ 1 (wave m v k theta) := by
  apply contDiff_one_iff_deriv.mpr
  refine ⟨differentiable_wave m hv k theta, ?_⟩
  have he : deriv (wave m v k theta) = fun x =>
      ((((score m v x / 2 : ℝ) : ℂ) + Complex.I * (k : ℂ)) *
        wave m v k theta x) := funext (deriv_wave m hv k theta)
  rw [he]
  exact ((Complex.continuous_ofReal.comp ((contDiff_score m v).continuous.div_const 2)).add
    continuous_const).mul (continuous_wave m hv k theta)

/-- The actual AE Gaussian equation and local absolute continuity force one global multiple. -/
theorem eq_const_mul_of_ae_ode {u g : ℝ → ℂ}
    (hAC : ∀ a b, AbsolutelyContinuousOnInterval u a b)
    (hd : ∀ᵐ x, HasDerivAt u (g x) x)
    (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) (k : ℝ)
    (hode : ∀ᵐ x, g x =
      (((-((x - m) / (2 * (v : ℝ))) : ℝ) : ℂ) + Complex.I * (k : ℂ)) * u x) :
    ∃ c : ℂ, ∀ x, u x = c * wave m v k 0 x := by
  have hinv : ContDiff ℝ 1 (fun x => (wave m v k 0 x)⁻¹) :=
    (contDiff_wave m hv k 0).inv (wave_ne_zero m hv k 0)
  have hqAC (a b : ℝ) :
      AbsolutelyContinuousOnInterval (fun x => u x / wave m v k 0 x) a b := by
    simpa only [Pi.smul_apply, smul_eq_mul, div_eq_mul_inv] using!
      (hAC a b).smul hinv.contDiffOn.absolutelyContinuousOnInterval
  have hzero : ∀ᵐ x, HasDerivAt (fun y => u y / wave m v k 0 y) 0 x := by
    filter_upwards [hd, hode] with x hx he
    have hc : score m v x / 2 = -((x - m) / (2 * (v : ℝ))) := by
      simp only [score, div_eq_mul_inv, mul_inv_rev]
      ring
    have hw := hasDerivAt_wave m hv k 0 x
    rw [hc] at hw
    have hnum : g x * wave m v k 0 x - u x *
        ((((-((x - m) / (2 * (v : ℝ))) : ℝ) : ℂ) + Complex.I * (k : ℂ)) *
          wave m v k 0 x) = 0 := by
      rw [he]
      ring
    simpa only [hnum, zero_div] using hx.fun_div hw (wave_ne_zero m hv k 0 x)
  refine ⟨u 0 / wave m v k 0 0, fun x => ?_⟩
  obtain ⟨c, hc⟩ := (hqAC 0 x).const_of_ae_hasDerivAt_zero
    (hzero.mono fun _ h _ => h)
  have he : u x / wave m v k 0 x = u 0 / wave m v k 0 0 :=
    (hc x Set.right_mem_uIcc).trans (hc 0 Set.left_mem_uIcc).symm
  exact (div_eq_iff (wave_ne_zero m hv k 0 x)).mp he

/-- True normalization turns the global multiple into the phase of the literal Gaussian wave. -/
theorem eq_wave_of_ae_ode {u g : ℝ → ℂ}
    (hAC : ∀ a b, AbsolutelyContinuousOnInterval u a b)
    (hd : ∀ᵐ x, HasDerivAt u (g x) x)
    (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) (k : ℝ)
    (hode : ∀ᵐ x, g x =
      (((-((x - m) / (2 * (v : ℝ))) : ℝ) : ℂ) + Complex.I * (k : ℂ)) * u x)
    (hnorm : (∫ x, ‖u x‖ ^ 2) = 1) :
    ∃ theta : ℝ, ∀ x, u x = wave m v k theta x := by
  obtain ⟨c, hc⟩ := eq_const_mul_of_ae_ode hAC hd m hv k hode
  have hcsq : ‖c‖ ^ 2 = 1 := by
    simp_rw [hc, norm_mul, mul_pow] at hnorm
    rwa [integral_const_mul, integral_norm_sq m hv k 0, mul_one] at hnorm
  have hcnorm : ‖c‖ = 1 := by
    nlinarith [norm_nonneg c]
  have hphase : Complex.exp (Complex.I * (Complex.arg c : ℂ)) = c := by
    simpa only [hcnorm, Complex.ofReal_one, one_mul, mul_one, mul_comm] using!
      Complex.norm_mul_exp_arg_mul_I c
  refine ⟨Complex.arg c, fun x => ?_⟩
  rw [hc]
  simp only [wave, add_zero, Complex.ofReal_add, mul_add, Complex.exp_add, hphase]
  ring

end FoliationQM.GaussianWaveRigidity
