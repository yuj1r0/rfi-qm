module
public import FoliationQM.DressedVelocity
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
# Integration of a compactly supported flat divergence

For the action variation in v13 `thm:dirac_lift`, a compactly supported
C¹ scalar flux has an integrable directional derivative. Flat
integration by parts with the constant function one shows that its
integral vanishes on the full space and on every set containing the
flux support. This requires no geometric condition on the boundary.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.DiracCompactDivergence
open MeasureTheory Function Set
open scoped Topology

variable {g : Covector → ℝ} (hg : ContDiff ℝ 1 g) (hc : HasCompactSupport g)
include hg hc

/-- The directional derivative is continuous with compact support, hence integrable for flat volume. -/
theorem integrable_deriv (v : Covector) : Integrable (fun x => fderiv ℝ g x v) :=
  ((hg.continuous_fderiv (by norm_num)).clm_apply continuous_const).integrable_of_hasCompactSupport
    (hc.fderiv_apply ℝ v)

/-- Integration by parts against the constant one gives zero total integral of any directional derivative. -/
theorem integral_deriv_zero (v : Covector) : (∫ x, fderiv ℝ g x v) = 0 := by
  have H := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (μ := volume) (f := fun _ : Covector => (1 : ℝ)) (g := g) (v := v)
    (by simp)
    (by simpa using integrable_deriv hg hc v)
    (by simpa using hg.continuous.integrable_of_hasCompactSupport hc)
    (fun _ _ => differentiableAt_const _) (fun x _ => hg.differentiable (by norm_num) x)
  simpa using H

/-- On a set containing the flux support the directional integral still vanishes. -/
theorem setIntegral_deriv_zero {U : Set Covector} (hs : tsupport g ⊆ U) (v : Covector) :
    (∫ x in U, fderiv ℝ g x v) = 0 := by
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
  · exact integral_deriv_zero hg hc v
  · intro x hx
    rw [fderiv_of_notMem_tsupport ℝ (show x ∉ tsupport g from fun h => hx (hs h))]
    rfl

end FoliationQM.DiracCompactDivergence
