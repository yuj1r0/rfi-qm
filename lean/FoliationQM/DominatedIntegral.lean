module

public import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# Actual parameter integrals with a common derivative bound

An integrable derivative envelope on one parameter ball gives genuine
integrability of every slice from integrability of the zero slice. The mean
value theorem supplies this conclusion before differentiation under the
integral is used. The codomain may itself be a continuous-linear-map space,
so the same results apply to a second differentiation step. No particular
formula for an integral or its derivatives is assumed.
-/

@[expose] public section
noncomputable section

namespace FoliationQM.DominatedIntegral

open MeasureTheory Metric Filter
open scoped Topology

variable {E X G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace X] [NormedAddCommGroup G] [NormedSpace ℝ G]
  {μ : Measure X} {F : E → X → G} {F' : E → X → E →L[ℝ] G}
  {B : X → ℝ} {r : ℝ}

/-- Every derivative slice is genuinely integrable under its common norm
bound and actual strong measurability. -/
theorem integrable_derivative
    (hF'_meas : ∀ a ∈ ball (0 : E) r, AEStronglyMeasurable (F' a) μ)
    (h_bound : ∀ᵐ x ∂μ, ∀ a ∈ ball (0 : E) r, ‖F' a x‖ ≤ B x)
    (hB : Integrable B μ) {a : E} (ha : a ∈ ball (0 : E) r) :
    Integrable (F' a) μ :=
  hB.mono' (hF'_meas a ha) (h_bound.mono fun _ hx => hx a ha)

/-- Integrability at zero and an integrable derivative envelope imply actual
integrability at every parameter in the common ball. -/
theorem integrable_slice (hr : 0 < r)
    (hF_meas : ∀ a ∈ ball (0 : E) r, AEStronglyMeasurable (F a) μ)
    (hF_zero : Integrable (F 0) μ)
    (h_bound : ∀ᵐ x ∂μ, ∀ a ∈ ball (0 : E) r, ‖F' a x‖ ≤ B x)
    (hB : Integrable B μ)
    (h_diff : ∀ᵐ x ∂μ, ∀ a ∈ ball (0 : E) r,
      HasFDerivAt (fun b => F b x) (F' a x) a)
    {a : E} (ha : a ∈ ball (0 : E) r) : Integrable (F a) μ := by
  have hzero : (0 : E) ∈ ball (0 : E) r := mem_ball_self hr
  have hnorm : ∀ᵐ x ∂μ, ‖F 0 x - F a x‖ ≤ B x * ‖a‖ := by
    filter_upwards [h_diff, h_bound] with x hx hbx
    have hm := (convex_ball (0 : E) r).norm_image_sub_le_of_norm_hasFDerivWithin_le
      (fun b hb => (hx b hb).hasFDerivWithinAt) hbx hzero ha
    simpa only [sub_zero, norm_sub_rev] using hm
  exact integrable_of_norm_sub_le (hF_meas a ha) hF_zero (hB.mul_const ‖a‖) hnorm

/-- At every parameter in the common ball, the actual Fréchet derivative
of the integral is the integral of the actual pointwise derivative. -/
theorem hasFDerivAt_integral [CompleteSpace G] (hr : 0 < r)
    (hF_meas : ∀ a ∈ ball (0 : E) r, AEStronglyMeasurable (F a) μ)
    (hF_zero : Integrable (F 0) μ)
    (hF'_meas : ∀ a ∈ ball (0 : E) r, AEStronglyMeasurable (F' a) μ)
    (h_bound : ∀ᵐ x ∂μ, ∀ a ∈ ball (0 : E) r, ‖F' a x‖ ≤ B x)
    (hB : Integrable B μ)
    (h_diff : ∀ᵐ x ∂μ, ∀ a ∈ ball (0 : E) r,
      HasFDerivAt (fun b => F b x) (F' a x) a)
    {a : E} (ha : a ∈ ball (0 : E) r) :
    HasFDerivAt (fun b => ∫ x, F b x ∂μ) (∫ x, F' a x ∂μ) a := by
  have hball : ball (0 : E) r ∈ 𝓝 a := isOpen_ball.mem_nhds ha
  exact hasFDerivAt_integral_of_dominated_of_fderiv_le hball
    (Filter.mem_of_superset hball hF_meas)
    (integrable_slice hr hF_meas hF_zero h_bound hB h_diff ha)
    (hF'_meas a ha) h_bound hB h_diff

end FoliationQM.DominatedIntegral
