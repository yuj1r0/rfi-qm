module

public import FoliationQM.FisherNormalization
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# The actual translated density KL integrand and its derivatives

Sources: v13 `thm:clock_sideband`, `eq:kl_fisher_expansion`, and the
supplement's normalized spatial KL construction. The definition is an actual
integral of the logarithmic density ratio. Positivity identifies the convenient
logarithmic difference with that ratio. Subsequent domination theorems establish
genuine local integrability and differentiation under this integral.
-/

@[expose] public section
noncomputable section

namespace FoliationQM.TranslatedKL

open MeasureTheory
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The actual logarithm of the positive spatial density. -/
def logDensity (f : E → ℝ) (x : E) : ℝ := Real.log (f x)

/-- The translated KL density, in a form whose value at zero translation is zero. -/
def integrand (f : E → ℝ) (a x : E) : ℝ :=
  f x * (logDensity f x - logDensity f (x + a))

/-- The actual first translation differential of the KL density. -/
def firstIntegrand (f : E → ℝ) (a x : E) : E →L[ℝ] ℝ :=
  (-f x) • fderiv ℝ (logDensity f) (x + a)

/-- The actual second translation differential, valued in continuous bilinear maps. -/
def secondIntegrand (f : E → ℝ) (a x : E) : E →L[ℝ] (E →L[ℝ] ℝ) :=
  (-f x) • fderiv ℝ (fderiv ℝ (logDensity f)) (x + a)

omit [NormedSpace ℝ E] in
/-- Positive densities identify the implemented integrand with the literal log ratio. -/
theorem integrand_eq_log_ratio {f : E → ℝ} (hpos : ∀ x, 0 < f x) (a x : E) :
    integrand f a x = f x * Real.log (f x / f (x + a)) := by
  rw [Real.log_div (hpos x).ne' (hpos (x + a)).ne']
  rfl

omit [NormedSpace ℝ E] in
/-- The zero-translation integrand vanishes pointwise. -/
theorem integrand_zero (f : E → ℝ) (x : E) : integrand f 0 x = 0 := by
  simp [integrand]

/-- Actual C2 regularity and positivity give actual C2 logarithmic density. -/
theorem contDiff_logDensity {f : E → ℝ} (hf : ContDiff ℝ 2 f)
    (hpos : ∀ x, 0 < f x) : ContDiff ℝ 2 (logDensity f) :=
  hf.log (fun x => (hpos x).ne')

/-- The chain rule in the translation variable proves the first KL integrand derivative. -/
theorem hasFDerivAt_integrand {f : E → ℝ} (hf : ContDiff ℝ 2 f)
    (hpos : ∀ x, 0 < f x) (a x : E) :
    HasFDerivAt (fun b => integrand f b x) (firstIntegrand f a x) a := by
  have hl := (contDiff_logDensity hf hpos).differentiable (by norm_num)
  have ht := (hl (x + a)).hasFDerivAt.comp a ((hasFDerivAt_id a).const_add x)
  convert (ht.const_sub (logDensity f x)).const_mul (f x) using 1 <;>
    simp [integrand, firstIntegrand, ContinuousLinearMap.comp_id, smul_neg, neg_smul]

/-- The second translation derivative is derived from the actual derivative map. -/
theorem hasFDerivAt_firstIntegrand {f : E → ℝ} (hf : ContDiff ℝ 2 f)
    (hpos : ∀ x, 0 < f x) (a x : E) :
    HasFDerivAt (fun b => firstIntegrand f b x) (secondIntegrand f a x) a := by
  have hl : ContDiff ℝ 1 (fderiv ℝ (logDensity f)) :=
    (contDiff_logDensity hf hpos).fderiv_right (by norm_num)
  have ht := (hl.differentiable (by norm_num) (x + a)).hasFDerivAt.comp a
    ((hasFDerivAt_id a).const_add x)
  convert ht.const_smul (-f x) using 1 <;>
    simp [firstIntegrand, secondIntegrand, ContinuousLinearMap.comp_id]
  · funext b
    rfl
  · exact neg_smul (f x) (fderiv ℝ (fderiv ℝ (logDensity f)) (x + a))

/-- Each translated KL integrand is continuous in the integration variable. -/
theorem continuous_integrand {f : E → ℝ} (hf : ContDiff ℝ 2 f)
    (hpos : ∀ x, 0 < f x) (a : E) : Continuous (integrand f a) := by
  have hl := (contDiff_logDensity hf hpos).continuous
  exact hf.continuous.mul (hl.sub (hl.comp (continuous_id.add continuous_const)))

/-- The actual first differential field is continuous in the integration variable. -/
theorem continuous_firstIntegrand {f : E → ℝ} (hf : ContDiff ℝ 2 f)
    (hpos : ∀ x, 0 < f x) (a : E) : Continuous (firstIntegrand f a) := by
  exact hf.continuous.neg.smul
    (((contDiff_logDensity hf hpos).continuous_fderiv (by norm_num)).comp
      (continuous_id.add continuous_const))

/-- C2 regularity makes the actual second differential field continuous as well. -/
theorem continuous_secondIntegrand {f : E → ℝ} (hf : ContDiff ℝ 2 f)
    (hpos : ∀ x, 0 < f x) (a : E) : Continuous (secondIntegrand f a) := by
  have hl : ContDiff ℝ 1 (fderiv ℝ (logDensity f)) :=
    (contDiff_logDensity hf hpos).fderiv_right (by norm_num)
  exact hf.continuous.neg.smul
    ((hl.continuous_fderiv (by norm_num)).comp (continuous_id.add continuous_const))

variable [MeasurableSpace E]

/-- The actual translated spatial KL functional; its genuine local integrability
is proved from common integrable derivative envelopes in the analytic bridge. -/
def value (f : E → ℝ) (μ : Measure E) (a : E) : ℝ := ∫ x, integrand f a x ∂μ

omit [NormedSpace ℝ E] in
/-- The actual KL functional agrees with the source's literal log-ratio integral. -/
theorem value_eq_log_ratio {f : E → ℝ} (hpos : ∀ x, 0 < f x) (μ : Measure E) (a : E) :
    value f μ a = ∫ x, f x * Real.log (f x / f (x + a)) ∂μ := by
  simp only [value, integrand_eq_log_ratio hpos]

omit [NormedSpace ℝ E] in
/-- The actual zero-translation KL integral is zero. -/
theorem value_zero (f : E → ℝ) (μ : Measure E) : value f μ 0 = 0 := by
  simp only [value, integrand_zero, integral_zero]

omit [NormedSpace ℝ E] in
/-- The zero-translation KL density is genuinely integrable without an entropy assumption. -/
theorem integrable_zero (f : E → ℝ) (μ : Measure E) : Integrable (integrand f 0) μ := by
  have he : integrand f 0 = (0 : E → ℝ) := funext (integrand_zero f)
  rw [he]
  exact MeasureTheory.integrable_zero E ℝ μ

end FoliationQM.TranslatedKL
