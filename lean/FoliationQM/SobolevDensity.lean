module

public import FoliationQM.WaveScoreAlgebra
public import FoliationQM.AENodalDerivative
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.LpSeminorm.Monotonicity
public import Mathlib.MeasureTheory.Function.AbsolutelyContinuous

/-!
# Actual density calculus for locally absolutely continuous complex waves

Sources: v13 thm:uncertainty, eq:cramer_rao and eq:p_var_decomp,
component kinds C and D. Genuine square integrability of the wave, its
derivative and the separately supplied position observable gives genuine
integrability of the density and position-density derivatives. The actual
local absolute continuity and derivative events are supplied by the proved
H¹ representative construction. Classical statements concern that actual
representative, not arbitrary changes to an Lp function on a null set.

The almost-everywhere nodal theorem extends complex derivative reconstruction
to the whole line. Boundary limits and whole-line integration by parts remain
separate consequences to be derived from these analytic inputs.
-/

@[expose] public section
noncomputable section

namespace FoliationQM.SobolevDensity
open MeasureTheory Filter WaveScoreAlgebra
open scoped ComplexConjugate

variable {u v : ℝ → ℂ} {a b : ℝ}

/-- The actual norm-square density has a genuine finite integral. -/
theorem integrable_density (hu : MemLp u 2 volume) :
    Integrable (fun x => density (u x)) volume := by
  simpa only [density] using hu.norm.integrable_sq

/-- The actual density derivative is integrable by the complex L² product. -/
theorem integrable_densityDerivative (hu : MemLp u 2 volume)
    (hv : MemLp v 2 volume) :
    Integrable (fun x => densityDerivative (u x) (v x)) volume := by
  have h : Integrable (fun x => conj (u x) * v x) volume :=
    (hu.star.integrable_mul hv).congr (Eventually.of_forall fun _ => rfl)
  simpa only [densityDerivative, RCLike.re_eq_complex_re] using h.re.const_mul 2

/-- The separate position L² premise gives an integrable first density moment. -/
theorem integrable_position_density (hu : MemLp u 2 volume)
    (hxu : MemLp (fun x : ℝ => (x : ℂ) * u x) 2 volume) :
    Integrable (fun x => x * density (u x)) volume := by
  have h : Integrable (fun x : ℝ => conj (u x) * ((x : ℂ) * u x)) volume :=
    (hu.star.integrable_mul hxu).congr (Eventually.of_forall fun _ => rfl)
  apply h.re.congr
  exact Eventually.of_forall fun x => by
    simp only [RCLike.re_eq_complex_re, density, Complex.sq_norm, Complex.normSq_apply, Complex.mul_re,
      Complex.mul_im, Complex.conj_re, Complex.conj_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero]
    ring

/-- Pairing position times the wave with its derivative gives the needed L¹ term. -/
theorem integrable_position_densityDerivative
    (hxu : MemLp (fun x : ℝ => (x : ℂ) * u x) 2 volume)
    (hv : MemLp v 2 volume) :
    Integrable (fun x => x * densityDerivative (u x) (v x)) volume := by
  have h : Integrable (fun x : ℝ => conj ((x : ℂ) * u x) * v x) volume :=
    (hxu.star.integrable_mul hv).congr (Eventually.of_forall fun _ => rfl)
  apply (h.re.const_mul 2).congr
  exact Eventually.of_forall fun x => by
    simp only [RCLike.re_eq_complex_re, densityDerivative, Complex.mul_re, Complex.mul_im, Complex.conj_re,
      Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    ring

/-- Squaring the actual absolutely continuous norm gives local density regularity. -/
theorem absolutelyContinuousOnInterval_density
    (hu : AbsolutelyContinuousOnInterval u a b) :
    AbsolutelyContinuousOnInterval (fun x => density (u x)) a b := by
  have hn : AbsolutelyContinuousOnInterval (fun x => ‖u x‖) a b :=
    lipschitzWith_one_norm.comp_absolutelyContinuousOnInterval hu
  simpa only [density, pow_two] using hn.fun_mul hn

/-- Multiplication by the actual coordinate preserves local absolute continuity. -/
theorem absolutelyContinuousOnInterval_position_density
    (hu : AbsolutelyContinuousOnInterval u a b) :
    AbsolutelyContinuousOnInterval (fun x => x * density (u x)) a b := by
  have hi : AbsolutelyContinuousOnInterval (fun x : ℝ => x) a b :=
    (contDiff_id : ContDiff ℝ 1 (fun x : ℝ => x)).contDiffOn.absolutelyContinuousOnInterval
  exact hi.fun_mul (absolutelyContinuousOnInterval_density hu)

/-- Actual almost-everywhere wave derivatives give actual density derivatives. -/
theorem ae_hasDerivAt_density (hd : ∀ᵐ x ∂volume, HasDerivAt u (v x) x) :
    ∀ᵐ x ∂volume, HasDerivAt (fun y => density (u y))
      (densityDerivative (u x) (v x)) x := by
  filter_upwards [hd] with x hx
  exact WaveScoreAlgebra.hasDerivAt_density hx

/-- The product rule supplies the actual position-density derivative. -/
theorem ae_hasDerivAt_position_density (hd : ∀ᵐ x ∂volume, HasDerivAt u (v x) x) :
    ∀ᵐ x ∂volume, HasDerivAt (fun y => y * density (u y))
      (density (u x) + x * densityDerivative (u x) (v x)) x := by
  filter_upwards [ae_hasDerivAt_density hd] with x hx
  simpa only [one_mul, id_eq] using (hasDerivAt_id x).fun_mul hx

/-- Both summands of the actual position-density derivative are genuinely integrable. -/
theorem integrable_position_density_derivative (hu : MemLp u 2 volume)
    (hxu : MemLp (fun x : ℝ => (x : ℂ) * u x) 2 volume)
    (hv : MemLp v 2 volume) :
    Integrable (fun x => density (u x) + x * densityDerivative (u x) (v x)) volume := by
  exact (integrable_density hu).add (integrable_position_densityDerivative hxu hv)

/-- The true nodal derivative theorem extends reconstruction to almost every point. -/
theorem ae_derivative_reconstruction (hd : ∀ᵐ x ∂volume, HasDerivAt u (v x) x) :
    ∀ᵐ x ∂volume, v x =
      ((((score (u x) (v x) / 2 : ℝ) : ℂ) +
        Complex.I * (phaseRate (u x) (v x) : ℂ)) * u x) := by
  have hn := AENodalDerivative.ae_derivative_zero_on_level_set volume (0 : ℂ) hd
  filter_upwards [hn] with x hx
  by_cases hz : u x = 0
  · rw [hx hz, hz, mul_zero]
  · exact WaveScoreAlgebra.derivative_reconstruction (u x) (v x) hz

end FoliationQM.SobolevDensity
