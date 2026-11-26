module

public import FoliationQM.KLPointwiseTaylor
public import FoliationQM.KLFourthDomination
public import FoliationQM.KLHessian

/-!
# Integrating the actual KL cubic Taylor expansion

Sources: v13 `thm:clock_sideband`, `eq:kl_fisher_expansion`, and the
supplement's finite-displacement fourth-order refinement. The actual pointwise
Taylor identity is integrated only after the polynomial and remainder have
been proved genuinely integrable. The resulting remainder constant is the
integral of the supplied fourth-derivative envelope divided by 24. No C4
regularity of KL, derivative interchange through order four, or KL Taylor
remainder is assumed. The first density boundary cancellation removes the
linear term; Fisher identification and physical-probe averaging are separate.
-/

@[expose] public section
noncomputable section

namespace FoliationQM.KLIntegralTaylor

open MeasureTheory Metric TranslatedKL KLDifferentiation IteratedLogDerivatives
open KLFourthDomination KLPointwiseTaylor

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

local instance dualNormedGroup : NormedAddCommGroup (E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance bilinearNormedGroup : NormedAddCommGroup (E →L[ℝ] (E →L[ℝ] ℝ)) :=
  ContinuousLinearMap.toNormedAddCommGroup

/-- The cubic polynomial formed from actual integrals of the density derivatives. -/
def integralPolynomial (f : E → ℝ) (μ : Measure E) (a : E) : ℝ :=
  firstIntegral f μ 0 a + (1 / 2 : ℝ) * secondIntegral f μ 0 a a +
    (1 / 6 : ℝ) * thirdIntegral f μ 0 (fun _ => a)

/-- Every term of the pointwise KL cubic polynomial is genuinely integrable
under the common derivative envelopes. -/
theorem integrable_densityPolynomial {f : E → ℝ} (hf : ContDiff ℝ 4 f)
    (hpos : ∀ x, 0 < f x) {μ : Measure E} {r : ℝ}
    (D : HigherDomination f μ r) (a : E) :
    Integrable (densityPolynomial f a) μ := by
  have hf2 : ContDiff ℝ 2 f := hf.of_le (by norm_num)
  have hz : (0 : E) ∈ ball (0 : E) r := mem_ball_self D.radius_pos
  have h1 := (integrable_first hf2 hpos D.toDomination hz).apply_continuousLinearMap a
  have h2 := ((integrable_second hf2 hpos D.toDomination hz).apply_continuousLinearMap a).apply_continuousLinearMap a
  have h3 : Integrable (fun x => weightedLogDerivative f 3 0 x (fun _ => a)) μ :=
    integrable_third_apply hf hpos D hz (fun _ => a)
  exact (h1.add (h2.const_mul (1 / 2 : ℝ))).add (h3.const_mul (1 / 6 : ℝ))

/-- The actual density remainder is genuinely integrable throughout the
common translation ball. -/
theorem integrable_remainder {f : E → ℝ} (hf : ContDiff ℝ 4 f)
    (hpos : ∀ x, 0 < f x) {μ : Measure E} {r : ℝ}
    (D : HigherDomination f μ r) {a : E} (ha : a ∈ ball (0 : E) r) :
    Integrable (fun x => integrand f a x - densityPolynomial f a x) μ :=
  (integrable_integrand (hf.of_le (by norm_num)) hpos D.toDomination ha).sub
    (integrable_densityPolynomial hf hpos D a)

/-- Integrating the actual pointwise cubic polynomial gives exactly the
first, second and third derivative integrals, with genuine evaluation interchange. -/
theorem integral_densityPolynomial {f : E → ℝ} (hf : ContDiff ℝ 4 f)
    (hpos : ∀ x, 0 < f x) {μ : Measure E} {r : ℝ}
    (D : HigherDomination f μ r) (a : E) :
    (∫ x, densityPolynomial f a x ∂μ) = integralPolynomial f μ a := by
  have hf2 : ContDiff ℝ 2 f := hf.of_le (by norm_num)
  have hz : (0 : E) ∈ ball (0 : E) r := mem_ball_self D.radius_pos
  have hi1 := integrable_first hf2 hpos D.toDomination hz
  have hi2 := integrable_second hf2 hpos D.toDomination hz
  have h1 := hi1.apply_continuousLinearMap a
  have hi2a := hi2.apply_continuousLinearMap a
  have h2 := hi2a.apply_continuousLinearMap a
  have h3 : Integrable (fun x => weightedLogDerivative f 3 0 x (fun _ => a)) μ :=
    integrable_third_apply hf hpos D hz (fun _ => a)
  have h1eq : firstIntegral f μ 0 a = ∫ x, firstIntegrand f 0 x a ∂μ :=
    ContinuousLinearMap.integral_apply hi1 a
  have h2eq : secondIntegral f μ 0 a a = ∫ x, secondIntegrand f 0 x a a ∂μ := by
    change (∫ x, secondIntegrand f 0 x ∂μ) a a = _
    rw [ContinuousLinearMap.integral_apply hi2 a, ContinuousLinearMap.integral_apply hi2a a]
  have h12 : Integrable (fun x => firstIntegrand f 0 x a +
      (1 / 2 : ℝ) * secondIntegrand f 0 x a a) μ := h1.add (h2.const_mul (1 / 2 : ℝ))
  unfold densityPolynomial integralPolynomial
  rw [integral_add h12 (h3.const_mul (1 / 6 : ℝ)),
    integral_add h1 (h2.const_mul (1 / 2 : ℝ)), integral_const_mul, integral_const_mul,
    ← h1eq, ← h2eq, ← thirdIntegral_apply hf hpos D hz (fun _ => a)]

/-- The difference between actual KL and its integrated polynomial is the
actual integral of the genuinely integrable pointwise remainder. -/
theorem value_sub_integralPolynomial_eq_integral {f : E → ℝ} (hf : ContDiff ℝ 4 f)
    (hpos : ∀ x, 0 < f x) {μ : Measure E} {r : ℝ}
    (D : HigherDomination f μ r) {a : E} (ha : a ∈ ball (0 : E) r) :
    value f μ a - integralPolynomial f μ a =
      ∫ x, (integrand f a x - densityPolynomial f a x) ∂μ := by
  rw [integral_sub (integrable_integrand (hf.of_le (by norm_num)) hpos D.toDomination ha)
    (integrable_densityPolynomial hf hpos D a), integral_densityPolynomial hf hpos D a]
  rfl

/-- The genuine integrated KL remainder has a density-dependent fourth-order
bound given by the integral of the actual derivative envelope. -/
theorem norm_value_sub_integralPolynomial_le {f : E → ℝ} (hf : ContDiff ℝ 4 f)
    (hpos : ∀ x, 0 < f x) {μ : Measure E} {r : ℝ}
    (D : HigherDomination f μ r) {a : E} (ha : a ∈ ball (0 : E) r) :
    ‖value f μ a - integralPolynomial f μ a‖ ≤
      ((∫ x, D.fourthBound x ∂μ) / 24) * ‖a‖ ^ 4 := by
  rw [value_sub_integralPolynomial_eq_integral hf hpos D ha]
  have hb : ∀ᵐ x ∂μ, ‖integrand f a x - densityPolynomial f a x‖ ≤
      D.fourthBound x * ‖a‖ ^ 4 / 24 := by
    filter_upwards [D.fourth_le] with x hx
    exact norm_integrand_sub_densityPolynomial_le_of_ball hf hpos D.radius_pos a x ha hx
  have h := norm_integral_le_of_norm_le ((D.fourth_integrable.mul_const (‖a‖ ^ 4)).div_const 24) hb
  rw [integral_div, integral_mul_const] at h
  convert h using 1
  ring

/-- The first density boundary condition removes the entire actual first
KL integral, whose genuine integrability follows from the common envelopes. -/
theorem firstIntegral_zero {f : E → ℝ} (hf : ContDiff ℝ 4 f)
    (hpos : ∀ x, 0 < f x) {μ : Measure E} {r : ℝ}
    (D : HigherDomination f μ r)
    (hboundary : ∀ v, (∫ x, fderiv ℝ f x v ∂μ) = 0) :
    firstIntegral f μ 0 = 0 := by
  rw [← fderiv_value (hf.of_le (by norm_num)) hpos D.toDomination (mem_ball_self D.radius_pos)]
  exact KLHessian.fderiv_value_zero (hf.of_le (by norm_num)) hpos D.toDomination hboundary

/-- After the first boundary cancellation, the integrated cubic polynomial
contains exactly its quadratic and cubic derivative terms. -/
theorem integralPolynomial_eq_quadratic_cubic {f : E → ℝ} (hf : ContDiff ℝ 4 f)
    (hpos : ∀ x, 0 < f x) {μ : Measure E} {r : ℝ}
    (D : HigherDomination f μ r)
    (hboundary : ∀ v, (∫ x, fderiv ℝ f x v ∂μ) = 0) (a : E) :
    integralPolynomial f μ a =
      (1 / 2 : ℝ) * secondIntegral f μ 0 a a +
      (1 / 6 : ℝ) * thirdIntegral f μ 0 (fun _ => a) := by
  simp only [integralPolynomial, firstIntegral_zero hf hpos D hboundary,
    zero_apply, zero_add]

/-- The actual KL functional has the source quadratic-plus-cubic expansion
with a genuine density-dependent fourth-order error throughout the common ball. -/
theorem norm_value_sub_quadratic_cubic_le {f : E → ℝ} (hf : ContDiff ℝ 4 f)
    (hpos : ∀ x, 0 < f x) {μ : Measure E} {r : ℝ}
    (D : HigherDomination f μ r) {a : E} (ha : a ∈ ball (0 : E) r)
    (hboundary : ∀ v, (∫ x, fderiv ℝ f x v ∂μ) = 0) :
    ‖value f μ a - ((1 / 2 : ℝ) * secondIntegral f μ 0 a a +
      (1 / 6 : ℝ) * thirdIntegral f μ 0 (fun _ => a))‖ ≤
      ((∫ x, D.fourthBound x ∂μ) / 24) * ‖a‖ ^ 4 := by
  simpa only [integralPolynomial_eq_quadratic_cubic hf hpos D hboundary] using
    norm_value_sub_integralPolynomial_le hf hpos D ha

/-- The quadratic coefficient in the finite-shift estimate is the actual
KL Hessian already identified by differentiation under the integral. -/
theorem norm_value_sub_actual_hessian_cubic_le {f : E → ℝ} (hf : ContDiff ℝ 4 f)
    (hpos : ∀ x, 0 < f x) {μ : Measure E} {r : ℝ}
    (D : HigherDomination f μ r) {a : E} (ha : a ∈ ball (0 : E) r)
    (hboundary : ∀ v, (∫ x, fderiv ℝ f x v ∂μ) = 0) :
    ‖value f μ a - ((1 / 2 : ℝ) * fderiv ℝ (fderiv ℝ (value f μ)) 0 a a +
      (1 / 6 : ℝ) * thirdIntegral f μ 0 (fun _ => a))‖ ≤
      ((∫ x, D.fourthBound x ∂μ) / 24) * ‖a‖ ^ 4 := by
  rw [fderiv_fderiv_value (hf.of_le (by norm_num)) hpos D.toDomination (mem_ball_self D.radius_pos)]
  exact norm_value_sub_quadratic_cubic_le hf hpos D ha hboundary

end FoliationQM.KLIntegralTaylor
