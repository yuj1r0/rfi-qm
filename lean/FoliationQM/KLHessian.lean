module

public import FoliationQM.KLDifferentiation
public import FoliationQM.LogDensityHessian
public import FoliationQM.SecondOrderFrechet

/-!
# The actual translated KL Hessian and Fisher integral

Sources: v13 `thm:clock_sideband`, `eq:kl_fisher_expansion`, and the
supplement's normalized spatial KL construction. Actual differentiation
under the integral is combined with the source's explicit zero-integral
boundary conditions on density derivatives. Finite Fisher and second-density
derivative integrals justify the subtraction. The resulting actual Hessian
gives a uniform quadratic remainder; no KL Hessian or remainder is assumed.
These analytic identities also hold for unnormalized positive densities.
Probability normalization and clock averaging are separate constructions.
-/

@[expose] public section
noncomputable section

namespace FoliationQM.KLHessian

open MeasureTheory Filter Metric TranslatedKL KLDifferentiation
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
/-- At zero translation, the actual first KL differential is minus the
actual density differential. -/
theorem firstIntegrand_zero_apply {f : E → ℝ} (hf : ContDiff ℝ 2 f)
    (hpos : ∀ x, 0 < f x) (x v : E) :
    firstIntegrand f 0 x v = -(fderiv ℝ f x v) := by
  change -f x * fderiv ℝ (fun y => Real.log (f y)) (x + 0) v = _
  rw [add_zero]
  rw [LogDensityHessian.fderiv_log_apply (hf.differentiable (by norm_num) x)
    (hpos x) v]
  field_simp [(hpos x).ne']

/-- First log-derivative domination also proves genuine integrability of
each actual density derivative at zero translation. -/
theorem integrable_fderiv_apply {f : E → ℝ} (hf : ContDiff ℝ 2 f)
    (hpos : ∀ x, 0 < f x) {μ : Measure E} {r : ℝ} (D : Domination f μ r)
    (v : E) : Integrable (fun x => fderiv ℝ f x v) μ := by
  have h : Integrable (fun x => firstIntegrand f 0 x v) μ :=
    (integrable_first hf hpos D (mem_ball_self D.radius_pos)).apply_continuousLinearMap v
  simp_rw [firstIntegrand_zero_apply hf hpos] at h
  simpa only [Pi.neg_def, neg_neg] using h.neg

/-- The actual KL first derivative vanishes by the source's zero-integral
boundary condition. Its integrand is genuinely integrable by domination. -/
theorem fderiv_value_zero {f : E → ℝ} (hf : ContDiff ℝ 2 f)
    (hpos : ∀ x, 0 < f x) {μ : Measure E} {r : ℝ} (D : Domination f μ r)
    (hboundary : ∀ v, (∫ x, fderiv ℝ f x v ∂μ) = 0) :
    fderiv ℝ (value f μ) 0 = 0 := by
  ext v
  rw [fderiv_value_apply hf hpos D (mem_ball_self D.radius_pos)]
  simp_rw [firstIntegrand_zero_apply hf hpos]
  simp only [integral_neg, hboundary, neg_zero, zero_apply]

/-- The actual translated KL Hessian is the actual Fisher bilinear integral,
after the explicitly integrable density Hessian has zero integral. -/
theorem hessian_eq_fisher {f : E → ℝ} (hf : ContDiff ℝ 2 f)
    (hpos : ∀ x, 0 < f x) {μ : Measure E} {r : ℝ} (D : Domination f μ r)
    (u v : E)
    (hFisher : Integrable (fun x =>
      f x * FisherNormalization.score f x u * FisherNormalization.score f x v) μ)
    (hSecond : Integrable (fun x => fderiv ℝ (fderiv ℝ f) x u v) μ)
    (hboundary : (∫ x, fderiv ℝ (fderiv ℝ f) x u v ∂μ) = 0) :
    fderiv ℝ (fderiv ℝ (value f μ)) 0 u v =
      ∫ x, f x * FisherNormalization.score f x u * FisherNormalization.score f x v ∂μ := by
  rw [fderiv_fderiv_value_apply hf hpos D (mem_ball_self D.radius_pos)]
  have hp : ∀ x, secondIntegrand f 0 x u v =
      f x * FisherNormalization.score f x u * FisherNormalization.score f x v -
        fderiv ℝ (fderiv ℝ f) x u v := by
    intro x
    change -f x * fderiv ℝ (fderiv ℝ (fun y => Real.log (f y))) (x + 0) u v = _
    rw [add_zero]
    exact LogDensityHessian.neg_mul_fderiv_fderiv_log_eq_score_product
      hf.contDiffAt (hpos x) u v
  simp_rw [hp]
  rw [integral_sub hFisher hSecond, hboundary, sub_zero]

/-- Evaluation of the proved second integral gives the same actual Fisher
bilinear form. This form is useful when retaining the differentiation API's H. -/
theorem secondIntegral_eq_fisher {f : E → ℝ} (hf : ContDiff ℝ 2 f)
    (hpos : ∀ x, 0 < f x) {μ : Measure E} {r : ℝ} (D : Domination f μ r)
    (u v : E)
    (hFisher : Integrable (fun x =>
      f x * FisherNormalization.score f x u * FisherNormalization.score f x v) μ)
    (hSecond : Integrable (fun x => fderiv ℝ (fderiv ℝ f) x u v) μ)
    (hboundary : (∫ x, fderiv ℝ (fderiv ℝ f) x u v ∂μ) = 0) :
    secondIntegral f μ 0 u v =
      ∫ x, f x * FisherNormalization.score f x u * FisherNormalization.score f x v ∂μ := by
  rw [← fderiv_fderiv_value hf hpos D (mem_ball_self D.radius_pos)]
  exact hessian_eq_fisher hf hpos D u v hFisher hSecond hboundary

/-- Finite supplied directions identify the actual Hessian entries with
the existing genuinely integrated Fisher matrix. -/
theorem hessian_eq_fisherMatrix {n : ℕ} {f : E → ℝ} (hf : ContDiff ℝ 2 f)
    (hpos : ∀ x, 0 < f x) {μ : Measure E} {r : ℝ} (D : Domination f μ r)
    (v : Fin n → E) (i j : Fin n)
    (hFisher : Integrable (FisherNormalization.matrixIntegrand f v i j) μ)
    (hSecond : Integrable (fun x => fderiv ℝ (fderiv ℝ f) x (v i) (v j)) μ)
    (hboundary : (∫ x, fderiv ℝ (fderiv ℝ f) x (v i) (v j) ∂μ) = 0) :
    fderiv ℝ (fderiv ℝ (value f μ)) 0 (v i) (v j) =
      FisherNormalization.fisherMatrix f v μ i j :=
  hessian_eq_fisher hf hpos D (v i) (v j) hFisher hSecond hboundary

/-- The actual translated KL functional has a uniform quadratic remainder
with its actual Hessian. The first boundary cancellation is explicit. -/
theorem isLittleO_value_sub_quadratic {f : E → ℝ} (hf : ContDiff ℝ 2 f)
    (hpos : ∀ x, 0 < f x) {μ : Measure E} {r : ℝ} (D : Domination f μ r)
    (hboundary : ∀ v, (∫ x, fderiv ℝ f x v ∂μ) = 0) :
    (fun a => value f μ a -
      (1 / 2 : ℝ) * fderiv ℝ (fderiv ℝ (value f μ)) 0 a a)
      =o[𝓝 (0 : E)] fun a => ‖a‖ ^ 2 := by
  have hd : ∀ᶠ a in 𝓝 (0 : E), DifferentiableAt ℝ (value f μ) a := by
    filter_upwards [ball_mem_nhds (0 : E) D.radius_pos] with a ha
    exact (hasFDerivAt_value hf hpos D ha).differentiableAt
  have hH := hasFDerivAt_fderiv_value hf hpos D (mem_ball_self D.radius_pos)
  rw [← hH.fderiv] at hH
  exact SecondOrderFrechet.isLittleO_sub_quadratic hd hH (TranslatedKL.value_zero f μ)
    (fderiv_value_zero hf hpos D hboundary)

end FoliationQM.KLHessian
