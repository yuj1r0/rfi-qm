module

public import FoliationQM.TranslatedKL
public import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Actual higher translation derivatives of the KL density

Sources: v13 `thm:clock_sideband`, `eq:kl_fisher_expansion`, and the
supplement's fourth-order finite-shift refinement. The derivatives below are
actual iterated Frechet derivatives. Their first two evaluations agree with
the already established KL differential fields. Higher regularity and common
integrable envelopes remain explicit density assumptions; no Taylor remainder
or derivative of an integral is included in these definitions.
-/

@[expose] public section
noncomputable section

namespace FoliationQM.IteratedLogDerivatives

open MeasureTheory TranslatedKL
open scoped BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

-- Use the same standard nested operator norms as the earlier KL modules.
local instance dualNormedGroup : NormedAddCommGroup (E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance bilinearNormedGroup : NormedAddCommGroup (E →L[ℝ] (E →L[ℝ] ℝ)) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance dualNormedSpace : NormedSpace ℝ (E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

local instance bilinearNormedSpace : NormedSpace ℝ (E →L[ℝ] (E →L[ℝ] ℝ)) :=
  ContinuousLinearMap.toNormedSpace

/-- The actual weighted order-n log derivative in the translation variable. -/
def weightedLogDerivative (f : E → ℝ) (n : ℕ) (a x : E) : E [×n]→L[ℝ] ℝ :=
  (-f x) • iteratedFDeriv ℝ n (logDensity f) (x + a)

/-- Positive Cn density gives the same actual Cn regularity for its logarithm. -/
theorem contDiff_logDensity_order {n : ℕ} {f : E → ℝ}
    (hf : ContDiff ℝ n f) (hpos : ∀ x, 0 < f x) :
    ContDiff ℝ n (logDensity f) :=
  hf.log (fun x => (hpos x).ne')

/-- Translation and the fixed density weight preserve actual Cn regularity. -/
theorem contDiff_integrand_order {n : ℕ} {f : E → ℝ}
    (hf : ContDiff ℝ n f) (hpos : ∀ x, 0 < f x) (x : E) :
    ContDiff ℝ n (fun a => integrand f a x) := by
  have hs : ContDiff ℝ n (fun b => logDensity f (x + b)) :=
    (contDiff_logDensity_order hf hpos).comp (contDiff_const.add contDiff_id)
  exact (contDiff_const.sub hs).const_smul (f x)

/-- All positive-order iterated translation derivatives of the actual KL
density have the negative weighted log-derivative sign. -/
theorem iteratedFDeriv_integrand {n : ℕ} (hn : n ≠ 0) {f : E → ℝ}
    (hf : ContDiff ℝ n f) (hpos : ∀ x, 0 < f x) (a x : E) :
    iteratedFDeriv ℝ n (fun b => integrand f b x) a =
      weightedLogDerivative f n a x := by
  have hs : ContDiff ℝ n (fun b => logDensity f (x + b)) :=
    (contDiff_logDensity_order hf hpos).comp (contDiff_const.add contDiff_id)
  change iteratedFDeriv ℝ n
    ((f x) • ((fun _ : E => logDensity f x) - (fun b => logDensity f (x + b)))) a = _
  have hsub : ContDiff ℝ n
      ((fun _ : E => logDensity f x) - (fun b => logDensity f (x + b))) :=
    contDiff_const.sub hs
  rw [iteratedFDeriv_const_smul_apply (a := f x) hsub.contDiffAt,
    iteratedFDeriv_sub_apply (f := fun _ : E => logDensity f x)
      contDiff_const.contDiffAt hs.contDiffAt,
    iteratedFDeriv_const_of_ne hn, Pi.zero_apply, zero_sub,
    iteratedFDeriv_comp_add_left]
  exact smul_neg (f x) (iteratedFDeriv ℝ n (logDensity f) (x + a)) |>.trans
    (neg_smul (f x) (iteratedFDeriv ℝ n (logDensity f) (x + a))).symm

/-- Evaluation of the weighted derivative is literal multiplication by
the negative unshifted density. -/
theorem weightedLogDerivative_apply (f : E → ℝ) (n : ℕ) (a x : E) (v : Fin n → E) :
    weightedLogDerivative f n a x v =
      -f x * iteratedFDeriv ℝ n (logDensity f) (x + a) v := rfl

/-- The order-one multilinear derivative is the previously proved actual
first KL translation differential. -/
theorem weightedLogDerivative_one_apply (f : E → ℝ) (a x v : E) :
    weightedLogDerivative f 1 a x (fun _ => v) = firstIntegrand f a x v := by
  simp [weightedLogDerivative, firstIntegrand]

/-- The order-two multilinear derivative is the previously proved actual
nested Frechet differential, including its order of arguments. -/
theorem weightedLogDerivative_two_apply (f : E → ℝ) (a x : E) (v : Fin 2 → E) :
    weightedLogDerivative f 2 a x v = secondIntegrand f a x (v 0) (v 1) := by
  simp [weightedLogDerivative, secondIntegrand, iteratedFDeriv_two_apply]

/-- Repeated-vector evaluation of the order-two derivative matches the
actual Hessian field used in the Fisher identification. -/
theorem weightedLogDerivative_two_diagonal (f : E → ℝ) (a x v : E) :
    weightedLogDerivative f 2 a x (fun _ => v) = secondIntegrand f a x v v :=
  weightedLogDerivative_two_apply f a x (fun _ => v)

/-- The weighted operator norm retains precisely the absolute density factor. -/
theorem norm_weightedLogDerivative (f : E → ℝ) (n : ℕ) (a x : E) :
    ‖weightedLogDerivative f n a x‖ =
      |f x| * ‖iteratedFDeriv ℝ n (logDensity f) (x + a)‖ := by
  simp [weightedLogDerivative, norm_smul, Real.norm_eq_abs]

/-- The order-one norm agrees with the operator envelope used in the KL
differentiation module. -/
theorem norm_weightedLogDerivative_one (f : E → ℝ) (a x : E) :
    ‖weightedLogDerivative f 1 a x‖ = ‖firstIntegrand f a x‖ := by
  simp [norm_weightedLogDerivative, firstIntegrand, norm_smul, Real.norm_eq_abs]

/-- The order-two norm agrees with the nested operator envelope used in the
KL differentiation module. -/
theorem norm_weightedLogDerivative_two (f : E → ℝ) (a x : E) :
    ‖weightedLogDerivative f 2 a x‖ = ‖secondIntegrand f a x‖ := by
  rw [norm_weightedLogDerivative]
  have he : ‖iteratedFDeriv ℝ 2 (logDensity f) (x + a)‖ =
      ‖fderiv ℝ (fderiv ℝ (logDensity f)) (x + a)‖ := by
    rw [← norm_iteratedFDeriv_fderiv (n := 1), norm_iteratedFDeriv_one]
  rw [he]
  rw [secondIntegrand]
  simpa only [Real.norm_eq_abs, abs_neg] using
    (norm_smul (-f x) (fderiv ℝ (fderiv ℝ (logDensity f)) (x + a))).symm

/-- Actual multilinearity bounds repeated-vector evaluation by the nth
power of the vector norm. -/
theorem norm_weightedLogDerivative_diagonal_le (f : E → ℝ) (n : ℕ) (a x v : E) :
    ‖weightedLogDerivative f n a x (fun _ => v)‖ ≤
      ‖weightedLogDerivative f n a x‖ * ‖v‖ ^ n := by
  simpa using (weightedLogDerivative f n a x).le_opNorm (fun _ => v)

/-- A concrete operator envelope gives the corresponding diagonal bound
without any assumed Taylor estimate. -/
theorem norm_weightedLogDerivative_diagonal_le_of_bound (f : E → ℝ) (n : ℕ)
    (a x v : E) {B : ℝ} (hB : ‖weightedLogDerivative f n a x‖ ≤ B) :
    ‖weightedLogDerivative f n a x (fun _ => v)‖ ≤ B * ‖v‖ ^ n :=
  (norm_weightedLogDerivative_diagonal_le f n a x v).trans
    (mul_le_mul_of_nonneg_right hB (by positivity))

/-- Actual Cn density regularity gives continuity of each weighted order-n
derivative in the spatial integration variable. -/
theorem continuous_weightedLogDerivative {n : ℕ} {f : E → ℝ}
    (hf : ContDiff ℝ n f) (hpos : ∀ x, 0 < f x) (a : E) :
    Continuous (weightedLogDerivative f n a) := by
  exact hf.continuous.neg.smul
    (((contDiff_logDensity_order hf hpos).continuous_iteratedFDeriv').comp
      (continuous_id.add continuous_const))

/-- Actual Cn density regularity also gives continuity of the weighted
derivative in the translation parameter. -/
theorem continuous_weightedLogDerivative_translation {n : ℕ} {f : E → ℝ}
    (hf : ContDiff ℝ n f) (hpos : ∀ x, 0 < f x) (x : E) :
    Continuous (fun a => weightedLogDerivative f n a x) := by
  exact (continuous_const (y := -f x)).smul
    (((contDiff_logDensity_order hf hpos).continuous_iteratedFDeriv').comp
      (continuous_const.add continuous_id))

variable [MeasurableSpace E]

/-- Evaluating a genuinely integrable multilinear derivative field preserves
integrability; the integral is not being assigned a default value. -/
theorem integrable_weightedLogDerivative_apply {f : E → ℝ} {n : ℕ}
    {a : E} {μ : Measure E} (hint : Integrable (weightedLogDerivative f n a) μ)
    (v : Fin n → E) : Integrable (fun x => weightedLogDerivative f n a x v) μ :=
  (ContinuousMultilinearMap.apply ℝ (fun _ : Fin n => E) ℝ v).integrable_comp hint

/-- Evaluation commutes with the genuine integral of the weighted actual
multilinear derivative field. -/
theorem integral_weightedLogDerivative_apply {f : E → ℝ} {n : ℕ}
    {a : E} {μ : Measure E} (hint : Integrable (weightedLogDerivative f n a) μ)
    (v : Fin n → E) :
    (∫ x, weightedLogDerivative f n a x ∂μ) v =
      ∫ x, weightedLogDerivative f n a x v ∂μ :=
  ContinuousMultilinearMap.integral_apply hint v

variable [BorelSpace E] [SecondCountableTopology E]

/-- Cn regularity and a genuine integrable weighted operator envelope prove
integrability of the actual order-n multilinear derivative field. -/
theorem integrable_weightedLogDerivative {n : ℕ} {f : E → ℝ}
    (hf : ContDiff ℝ n f) (hpos : ∀ x, 0 < f x) {μ : Measure E}
    (a : E) {B : E → ℝ} (hB : Integrable B μ)
    (hbound : ∀ᵐ x ∂μ, ‖weightedLogDerivative f n a x‖ ≤ B x) :
    Integrable (weightedLogDerivative f n a) μ :=
  hB.mono' (continuous_weightedLogDerivative hf hpos a).aestronglyMeasurable hbound

end FoliationQM.IteratedLogDerivatives
