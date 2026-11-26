module

public import FoliationQM.FisherNormalization
public import FoliationQM.PolarRegularity
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.Calculus.Deriv.Inv

/-!
# Actual log-density derivatives and the pointwise Fisher identity

Sources: v13 `thm:clock_sideband`, `eq:kl_fisher_expansion`.
The first and second derivatives are actual real Fréchet derivatives.
Local C2 regularity and positivity at the point supply the neighborhood on
which the actual derivative of log density agrees with the quotient rule.
Differentiating that derivative map gives the full continuous-bilinear
Hessian and its directional evaluations. No Hessian jet, KL differentiation
under an integral, boundary cancellation, or Fisher identity is postulated.
-/

@[expose] public section
noncomputable section

namespace FoliationQM.LogDensityHessian

open Filter ContinuousLinearMap
open scoped Topology ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The actual second directional derivative: outer direction u, inner direction v. -/
def secondDirectional (f : E → ℝ) (x u v : E) : ℝ :=
  fderiv ℝ (fun y => fderiv ℝ f y v) x u

/-- The first actual Fréchet derivative of log positive density. -/
theorem hasFDerivAt_log {f : E → ℝ} {x : E}
    (hf : DifferentiableAt ℝ f x) (hpos : 0 < f x) :
    HasFDerivAt (fun y => Real.log (f y)) ((f x)⁻¹ • fderiv ℝ f x) x :=
  hf.hasFDerivAt.log hpos.ne'

/-- The actual derivative map of log density is the scaled density derivative. -/
theorem fderiv_log {f : E → ℝ} {x : E}
    (hf : DifferentiableAt ℝ f x) (hpos : 0 < f x) :
    fderiv ℝ (fun y => Real.log (f y)) x = (f x)⁻¹ • fderiv ℝ f x :=
  (hasFDerivAt_log hf hpos).fderiv

/-- Evaluating the actual log derivative gives the ordinary spatial score. -/
theorem fderiv_log_apply {f : E → ℝ} {x : E}
    (hf : DifferentiableAt ℝ f x) (hpos : 0 < f x) (v : E) :
    fderiv ℝ (fun y => Real.log (f y)) x v = fderiv ℝ f x v / f x :=
  FisherNormalization.score_eq hf hpos v

/-- Positive local C2 density gives actual local C2 log density. -/
theorem contDiffAt_log {f : E → ℝ} {x : E}
    (hf : ContDiffAt ℝ 2 f x) (hpos : 0 < f x) :
    ContDiffAt ℝ 2 (fun y => Real.log (f y)) x := hf.log hpos.ne'

/-- Local C2 regularity makes the actual continuous-linear derivative map differentiable. -/
theorem differentiableAt_fderiv {f : E → ℝ} {x : E} (hf : ContDiffAt ℝ 2 f x) :
    DifferentiableAt ℝ (fderiv ℝ f) x := by
  have hd : ContDiffAt ℝ 1 (fderiv ℝ f) x := hf.fderiv_right (by norm_num)
  exact hd.differentiableAt_one

/-- Continuity and local regularity identify the actual log derivative map
with its quotient expression on a whole neighborhood of the point. -/
theorem fderiv_log_eventuallyEq {f : E → ℝ} {x : E}
    (hf : ContDiffAt ℝ 2 f x) (hpos : 0 < f x) :
    fderiv ℝ (fun y => Real.log (f y)) =ᶠ[𝓝 x]
      (fun y => (f y)⁻¹ • fderiv ℝ f y) := by
  have hp : ∀ᶠ y in 𝓝 x, 0 < f y :=
    hf.continuousAt.preimage_mem_nhds (Ioi_mem_nhds hpos)
  filter_upwards [PolarRegularity.eventually_differentiableAt_of_contDiffAt_two hf, hp]
    with y hy hpy
  exact fderiv_log hy hpy

/-- Differentiating the actual derivative map proves the full Fréchet Hessian
formula, rather than only an algebraic relation between supplied jets. -/
theorem hasFDerivAt_fderiv_log {f : E → ℝ} {x : E}
    (hf : ContDiffAt ℝ 2 f x) (hpos : 0 < f x) :
    HasFDerivAt (fderiv ℝ (fun y => Real.log (f y)))
      ((f x)⁻¹ • fderiv ℝ (fderiv ℝ f) x -
        (f x ^ 2)⁻¹ • (fderiv ℝ f x).smulRight (fderiv ℝ f x)) x := by
  have hi := (hasDerivAt_inv hpos.ne').comp_hasFDerivAt x
    (hf.differentiableAt (by norm_num)).hasFDerivAt
  have hd := hi.smul (differentiableAt_fderiv hf).hasFDerivAt
  have he := fderiv_log_eventuallyEq hf hpos
  convert hd.congr_of_eventuallyEq he using 1
  ext u v
  simp only [sub_apply, add_apply, smul_apply, smulRight_apply, smul_eq_mul, Function.comp_apply]
  ring

/-- The actual nested continuous-linear-map Hessian of log positive density. -/
theorem fderiv_fderiv_log {f : E → ℝ} {x : E}
    (hf : ContDiffAt ℝ 2 f x) (hpos : 0 < f x) :
    fderiv ℝ (fderiv ℝ (fun y => Real.log (f y))) x =
      (f x)⁻¹ • fderiv ℝ (fderiv ℝ f) x -
        (f x ^ 2)⁻¹ • (fderiv ℝ f x).smulRight (fderiv ℝ f x) :=
  (hasFDerivAt_fderiv_log hf hpos).fderiv

/-- Evaluating the full actual Hessian gives the pointwise log-density rule. -/
theorem fderiv_fderiv_log_apply {f : E → ℝ} {x : E}
    (hf : ContDiffAt ℝ 2 f x) (hpos : 0 < f x) (u v : E) :
    fderiv ℝ (fderiv ℝ (fun y => Real.log (f y))) x u v =
      fderiv ℝ (fderiv ℝ f) x u v / f x -
        fderiv ℝ f x u * fderiv ℝ f x v / f x ^ 2 := by
  rw [fderiv_fderiv_log hf hpos]
  simp only [sub_apply, smul_apply, smulRight_apply, smul_eq_mul]
  ring

/-- The derivative of a fixed derivative evaluation agrees with evaluation
of the actual full Fréchet Hessian; the direction order is u then v. -/
theorem secondDirectional_eq_fderiv_fderiv {f : E → ℝ} {x : E}
    (hf : DifferentiableAt ℝ (fderiv ℝ f) x) (u v : E) :
    secondDirectional f x u v = fderiv ℝ (fderiv ℝ f) x u v := by
  unfold secondDirectional
  rw [fderiv_clm_apply hf (differentiableAt_const v)]
  simp

/-- Actual mixed directional derivatives of a positive local C2 log density. -/
theorem secondDirectional_log {f : E → ℝ} {x : E}
    (hf : ContDiffAt ℝ 2 f x) (hpos : 0 < f x) (u v : E) :
    secondDirectional (fun y => Real.log (f y)) x u v =
      secondDirectional f x u v / f x -
        fderiv ℝ f x u * fderiv ℝ f x v / f x ^ 2 := by
  rw [secondDirectional_eq_fderiv_fderiv
      (hasFDerivAt_fderiv_log hf hpos).differentiableAt,
    secondDirectional_eq_fderiv_fderiv (differentiableAt_fderiv hf),
    fderiv_fderiv_log_apply hf hpos]

/-- The actual nested-CLM Hessian satisfies the pointwise identity needed
before integrating the translated KL Hessian. -/
theorem neg_mul_fderiv_fderiv_log {f : E → ℝ} {x : E}
    (hf : ContDiffAt ℝ 2 f x) (hpos : 0 < f x) (u v : E) :
    -(f x) * fderiv ℝ (fderiv ℝ (fun y => Real.log (f y))) x u v =
      fderiv ℝ f x u * fderiv ℝ f x v / f x -
        fderiv ℝ (fderiv ℝ f) x u v := by
  rw [fderiv_fderiv_log_apply hf hpos]
  field_simp
  ring

/-- The same weighted log-Hessian identity for derivatives of actual directional
derivative functions, with positive density and local C2 regularity explicit. -/
theorem neg_mul_secondDirectional_log {f : E → ℝ} {x : E}
    (hf : ContDiffAt ℝ 2 f x) (hpos : 0 < f x) (u v : E) :
    -(f x) * secondDirectional (fun y => Real.log (f y)) x u v =
      fderiv ℝ f x u * fderiv ℝ f x v / f x - secondDirectional f x u v := by
  rw [secondDirectional_log hf hpos]
  field_simp
  ring

/-- Expressing the weighted Hessian through the existing actual spatial score
gives the literal pointwise Fisher integrand minus the density Hessian. -/
theorem neg_mul_fderiv_fderiv_log_eq_score_product {f : E → ℝ} {x : E}
    (hf : ContDiffAt ℝ 2 f x) (hpos : 0 < f x) (u v : E) :
    -(f x) * fderiv ℝ (fderiv ℝ (fun y => Real.log (f y))) x u v =
      f x * FisherNormalization.score f x u * FisherNormalization.score f x v -
        fderiv ℝ (fderiv ℝ f) x u v := by
  rw [neg_mul_fderiv_fderiv_log hf hpos,
    FisherNormalization.score_eq (hf.differentiableAt (by norm_num)) hpos,
    FisherNormalization.score_eq (hf.differentiableAt (by norm_num)) hpos]
  field_simp

/-- Local C2 regularity gives symmetry of the actual directional Hessian. -/
theorem secondDirectional_symm {f : E → ℝ} {x : E}
    (hf : ContDiffAt ℝ 2 f x) (u v : E) :
    secondDirectional f x u v = secondDirectional f x v u := by
  rw [secondDirectional_eq_fderiv_fderiv (differentiableAt_fderiv hf),
    secondDirectional_eq_fderiv_fderiv (differentiableAt_fderiv hf)]
  exact hf.isSymmSndFDerivAt (by norm_num) u v

end FoliationQM.LogDensityHessian
