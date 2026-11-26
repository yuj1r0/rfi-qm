module

public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.Calculus.FDeriv.CompCLM

/-!
# Uniform second-order approximation from actual Fréchet derivatives

The actual derivative of the first derivative at zero gives a uniform
quadratic remainder. Symmetry of the second derivative follows from local
first differentiability and is not postulated. The proof applies the mean
value theorem to the remainder's actual derivative. This is the analytic
uniformity needed for bounded displacement probes; no integral exchange or
translated KL identity is asserted here.
-/

@[expose] public section
noncomputable section

namespace FoliationQM.SecondOrderFrechet

open Asymptotics Filter Metric
open scoped Topology ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {f : E → ℝ} {H : E →L[ℝ] E →L[ℝ] ℝ}

/-- The actual second derivative is symmetric under local first
differentiability, without a separate continuity or symmetry premise. -/
theorem hessian_symmetric
    (h_diff : ∀ᶠ a in 𝓝 (0 : E), DifferentiableAt ℝ f a)
    (hH : HasFDerivAt (fderiv ℝ f) H 0) (v w : E) : H v w = H w v :=
  second_derivative_symmetric_of_eventually
    (h_diff.mono fun _ ha => ha.hasFDerivAt) hH v w

/-- Half the diagonal of a symmetric continuous bilinear form has the
expected actual derivative. -/
theorem hasFDerivAt_half_diagonal (hH : ∀ v w, H v w = H w v) (a : E) :
    HasFDerivAt (fun b => (1 / 2 : ℝ) * H b b) (H a) a := by
  have hd : HasFDerivAt (fun b => H b b) (H a + H.flip a) a := by
    simpa using H.hasFDerivAt.clm_apply (hasFDerivAt_id a)
  have he : (1 / 2 : ℝ) • (H a + H.flip a) = H a := by
    ext v
    simp only [smul_apply, add_apply,
      ContinuousLinearMap.flip_apply, smul_eq_mul]
    rw [hH v a]
    ring
  simpa only [Pi.smul_def, smul_eq_mul, he] using hd.const_smul (1 / 2 : ℝ)

/-- Actual second differentiability gives a uniform Fréchet little-o
remainder at a zero critical point. No Taylor expansion is a hypothesis. -/
theorem isLittleO_sub_quadratic
    (h_diff : ∀ᶠ a in 𝓝 (0 : E), DifferentiableAt ℝ f a)
    (hH : HasFDerivAt (fderiv ℝ f) H 0)
    (hzero : f 0 = 0) (hfirst : fderiv ℝ f 0 = 0) :
    (fun a => f a - (1 / 2 : ℝ) * H a a) =o[𝓝 (0 : E)] fun a => ‖a‖ ^ 2 := by
  have hsymm := hessian_symmetric h_diff hH
  have ho : (fun a => fderiv ℝ f a - H a) =o[𝓝 (0 : E)] fun a => ‖a‖ := by
    simpa only [zero_add, hfirst, sub_zero] using
      (hasFDerivAt_iff_isLittleO_nhds_zero.mp hH).norm_right
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.mp h_diff
  have hder : ∀ a ∈ ball (0 : E) r,
      HasFDerivWithinAt (fun b => f b - (1 / 2 : ℝ) * H b b)
        (fderiv ℝ f a - H a) (ball (0 : E) r) a := by
    intro a ha
    exact ((hball a ha).hasFDerivAt.sub
      (hasFDerivAt_half_diagonal hsymm a)).hasFDerivWithinAt
  have hsmall : (fun a => fderiv ℝ f a - H a) =o[𝓝[ball (0 : E) r] (0 : E)]
      fun a => ‖a - 0‖ ^ 1 := by
    simpa only [sub_zero, pow_one] using ho.mono nhdsWithin_le_nhds
  have hresult := (convex_ball (0 : E) r).isLittleO_pow_succ
    (mem_ball_self hr) hder hsmall
  rw [nhdsWithin_eq_nhds.mpr (ball_mem_nhds (0 : E) hr)] at hresult
  simpa only [hzero, map_zero, zero_apply, mul_zero, sub_zero] using hresult

/-- Local C2 regularity supplies the genuine derivative hypotheses of the
uniform quadratic approximation. -/
theorem isLittleO_sub_quadratic_of_contDiffAt
    (hf : ContDiffAt ℝ 2 f 0) (hzero : f 0 = 0) (hfirst : fderiv ℝ f 0 = 0) :
    (fun a => f a - (1 / 2 : ℝ) * fderiv ℝ (fderiv ℝ f) 0 a a)
      =o[𝓝 (0 : E)] fun a => ‖a‖ ^ 2 := by
  have hd : ∀ᶠ a in 𝓝 (0 : E), DifferentiableAt ℝ f a :=
    (hf.eventually (by norm_num)).mono fun _ ha => ha.differentiableAt (by norm_num)
  have hsecond : ContDiffAt ℝ 1 (fderiv ℝ f) 0 := hf.fderiv_right (by norm_num)
  exact isLittleO_sub_quadratic hd (hsecond.differentiableAt (by norm_num)).hasFDerivAt
    hzero hfirst

end FoliationQM.SecondOrderFrechet
