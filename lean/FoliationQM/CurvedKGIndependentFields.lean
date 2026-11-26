module

public import FoliationQM.CurvedKGEulerLagrange

/-!
# Independent variation of the conjugated field

The complex bilinear action treats the conjugate and unconjugated fields
as separate arguments. Varying only its conjugated argument gives a tested
complex residual directly. The relative functional is well defined on compact
interior perturbations even if the background action is infinite.
-/

@[expose] public section
noncomputable section
open scoped Matrix.Norms.Operator ContDiff
namespace FoliationQM.CurvedKGIndependentFields

open MeasureTheory LorentzMatrixGroup RNCVolumeDensity CurvedKGFirstVariation CurvedKGTestResidual

/-- The integrated change from varying only the conjugated slot in the sesquilinear Klein–Gordon action. -/
def leftChange (p : MassiveParameters) (g : Covector → Mat4) (χ ψ η : Covector → ℂ)
    (U : Set Covector) (t : ℝ) : ℂ :=
  ∫ x in U, volumeFactor (g x) • (cross p g (perturb χ η t) ψ x - cross p g χ ψ x)

/-- Independent variation of the conjugated slot is exactly linear in the variation parameter. -/
theorem leftChange_eq (p : MassiveParameters) (g : Covector → Mat4)
    {χ η : Covector → ℂ} (ψ : Covector → ℂ) {U : Set Covector} (hU : MeasurableSet U)
    (hχ : ∀ x ∈ U, DifferentiableAt ℝ χ x) (hη : ∀ x ∈ U, DifferentiableAt ℝ η x) (t : ℝ) :
    leftChange p g χ ψ η U t = t • ∫ x in U, volumeFactor (g x) • cross p g η ψ x := by
  rw [← integral_smul]
  apply setIntegral_congr_fun hU
  intro x hx
  change volumeFactor (g x) • (cross p g (perturb χ η t) ψ x - cross p g χ ψ x) = _
  rw [cross_perturb_left p g (hχ x hx) (hη x hx) ψ t, add_sub_cancel_left, smul_comm]

/-- The derivative with respect to the independent conjugated slot is the tested complex Euler–Lagrange residual with its sign. -/
theorem left_derivative (p : MassiveParameters) {g : Covector → Mat4} {χ ψ η : Covector → ℂ}
    {U : Set Covector} (hU : MeasurableSet U) (hχ : ∀ x ∈ U, DifferentiableAt ℝ χ x)
    (hg : ∀ x ∈ U, ContDiffAt ℝ 2 g x) (hd : ∀ x ∈ U, (g x).det < 0)
    (hψ : ∀ x ∈ U, ContDiffAt ℝ 2 ψ x) (hη : ContDiff ℝ 1 η)
    (hc : HasCompactSupport η) (hs : tsupport η ⊆ U) :
    HasDerivAt (leftChange p g χ ψ η U)
      (-(∫ x in U, volumeFactor (g x) • (star (η x) * residual p g ψ x))) 0 := by
  have he := funext (leftChange_eq p g ψ hU hχ (fun _ _ => hη.differentiable_one.differentiableAt))
  rw [he, ← integral_cross_residual p hη hc hs hg hd hψ]
  simpa only [one_smul, id_eq] using!
    (hasDerivAt_id (0 : ℝ)).smul_const (∫ x in U, volumeFactor (g x) • cross p g η ψ x)

/-- Independent compact variation of the conjugated field is stationary exactly when the unconjugated field solves the pointwise curved equation. -/
theorem stationary_left_iff (p : MassiveParameters) {g : Covector → Mat4} {χ ψ : Covector → ℂ}
    {U : Set Covector} (hU : IsOpen U) (hχ : ∀ x ∈ U, DifferentiableAt ℝ χ x)
    (hg : ∀ x ∈ U, ContDiffAt ℝ 2 g x) (hd : ∀ x ∈ U, (g x).det < 0)
    (hψ : ∀ x ∈ U, ContDiffAt ℝ 2 ψ x) :
    (∀ η : Covector → ℂ, ContDiff ℝ ∞ η → HasCompactSupport η → tsupport η ⊆ U →
      HasDerivAt (leftChange p g χ ψ η U) 0 0) ↔ ∀ x ∈ U, kgOperator p g ψ x = 0 := by
  constructor
  · intro hv
    apply (CurvedKGEulerLagrange.operator_iff_tests p hU hg hd hψ).mpr
    intro η hη hc hs
    have he := (left_derivative p hU.measurableSet hχ hg hd hψ (hη.of_le (by simp)) hc hs).unique (hv η hη hc hs)
    have hi := (CurvedWeakEquation.integrable_pair
      (fun x hx => (hg x hx).continuousAt.continuousWithinAt)
      (fun x hx => (residual_continuousAt p (hg x hx) (hd x hx) (hψ x hx)).continuousWithinAt)
      hη.continuous hc hs).integrableOn (s := U)
    have hr := integral_re hi
    calc
      _ = (∫ x in U, volumeFactor (g x) • (star (η x) * residual p g ψ x)).re := by
        simpa only [CurvedWeakEquation.testIntegral, RCLike.re_eq_complex_re, Complex.smul_re, smul_eq_mul] using! hr
      _ = 0 := congrArg Complex.re (neg_eq_zero.mp he)
  · intro hv η hη hc hs
    have hz : (∫ x in U, volumeFactor (g x) • (star (η x) * residual p g ψ x)) = 0 := by
      apply setIntegral_eq_zero_of_forall_eq_zero
      intro x hx
      simp [(residual_zero_iff p g ψ x).mpr (hv x hx)]
    simpa only [hz, neg_zero] using left_derivative p hU.measurableSet hχ hg hd hψ (hη.of_le (by simp)) hc hs

end FoliationQM.CurvedKGIndependentFields
