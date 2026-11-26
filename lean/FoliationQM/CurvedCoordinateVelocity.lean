module

public import FoliationQM.CurvedCovariantDerivative
public import Mathlib.Analysis.Calculus.Deriv.Inv

/-!
# Actual coordinate-time velocity and its derivative

In coordinates with `x⁰ = ct`, rescaling the proper-time velocity by
`c/U⁰` produces the full coordinate-time velocity. The derivative below
comes from the scalar quotient and vector product rules. In particular,
its self-derivative retains the derivative of the zeroth component, which
is required when converting proper acceleration to coordinate dynamics.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.CurvedCoordinateVelocity

open LorentzMatrixGroup CurvedScalarAtlasOverlap CurvedConnectionComponents ContinuousLinearMap
open scoped Topology Matrix.Norms.Operator
set_option backward.isDefEq.respectTransparency false

/-- The full coordinate-time velocity in coordinates whose zeroth coordinate is `ct`. -/
def coordinateVelocity (c : ℝ) (U : Covector → Covector) (x : Covector) : Covector :=
  (c / U x 0) • U x

variable {U : Covector → Covector} {x : Covector}

/-- A nonzero temporal proper-velocity component gives the required constant temporal coordinate velocity `c`. -/
theorem time_component (c : ℝ) (h0 : U x 0 ≠ 0) : coordinateVelocity c U x 0 = c := by
  change (c / U x 0) * U x 0 = c
  exact div_mul_cancel₀ c h0

/-- The three spatial coordinate velocities are the source ratios `c Uⁱ/U⁰`. -/
theorem spatial_components (c : ℝ) (U : Covector → Covector) (x : Covector) (i : Fin 3) :
    coordinateVelocity c U x i.succ = c * U x i.succ / U x 0 := by
  change (c / U x 0) * U x i.succ = _
  ring

/-- The genuine Fréchet derivative of coordinate velocity includes the quotient derivative of its temporal denominator. -/
theorem hasFDerivAt_coordinateVelocity (c : ℝ) (hU : DifferentiableAt ℝ U x)
    (h0 : U x 0 ≠ 0) :
    HasFDerivAt (coordinateVelocity c U)
      ((c / U x 0) • fderiv ℝ U x +
        ((-c / (U x 0) ^ 2) •
          ((proj 0 : Covector →L[ℝ] ℝ).comp (fderiv ℝ U x))).smulRight (U x)) x := by
  have ht : HasFDerivAt (fun y => U y 0)
      ((proj 0 : Covector →L[ℝ] ℝ).comp (fderiv ℝ U x)) x :=
    (proj 0 : Covector →L[ℝ] ℝ).hasFDerivAt.comp x hU.hasFDerivAt
  have hr : HasDerivAt (fun r : ℝ => c / r) (-c / (U x 0) ^ 2) (U x 0) := by
    simpa only [zero_mul, mul_one, zero_sub] using!
      (hasDerivAt_const (U x 0) c).fun_div (hasDerivAt_id (U x 0)) h0
  exact (hr.comp_hasFDerivAt x ht).fun_smul hU.hasFDerivAt

/-- A differentiable proper velocity gives a differentiable coordinate velocity wherever its temporal component is nonzero. -/
theorem differentiableAt_coordinateVelocity (c : ℝ) (hU : DifferentiableAt ℝ U x)
    (h0 : U x 0 ≠ 0) : DifferentiableAt ℝ (coordinateVelocity c U) x :=
  (hasFDerivAt_coordinateVelocity c hU h0).differentiableAt

/-- Coordinate-time rescaling preserves any supplied order of local continuous differentiability on its nonzero temporal domain. -/
theorem contDiffAt_coordinateVelocity (c : ℝ) {n : WithTop ℕ∞} (hU : ContDiffAt ℝ n U x)
    (h0 : U x 0 ≠ 0) : ContDiffAt ℝ n (coordinateVelocity c U) x := by
  have ht := (proj 0 : Covector →L[ℝ] ℝ).contDiff.contDiffAt.comp x hU
  exact (contDiffAt_const.div ht h0).smul hU

/-- Evaluating the actual coordinate-velocity derivative gives both the scaled velocity derivative and the temporal quotient correction. -/
theorem directional_derivative (c : ℝ) (hU : DifferentiableAt ℝ U x)
    (h0 : U x 0 ≠ 0) (v : Covector) :
    fderiv ℝ (coordinateVelocity c U) x v =
      (c / U x 0) • fderiv ℝ U x v -
        (c / (U x 0) ^ 2 * fderiv ℝ U x v 0) • U x := by
  rw [(hasFDerivAt_coordinateVelocity c hU h0).fderiv]
  simp only [add_apply, smul_apply, smulRight_apply, comp_apply, proj_apply,
    smul_eq_mul, neg_div, neg_mul, neg_smul, sub_eq_add_neg]

/-- The actual self-derivative of coordinate velocity is the proper-velocity self-derivative with its exact temporal correction. -/
theorem self_derivative (c : ℝ) (hU : DifferentiableAt ℝ U x) (h0 : U x 0 ≠ 0) :
    fderiv ℝ (coordinateVelocity c U) x (coordinateVelocity c U x) =
      (c / U x 0) ^ 2 • fderiv ℝ U x (U x) -
        (c ^ 2 / (U x 0) ^ 3 * fderiv ℝ U x (U x) 0) • U x := by
  rw [directional_derivative c hU h0]
  ext a
  simp only [coordinateVelocity, map_smul, Pi.smul_apply, Pi.sub_apply, smul_eq_mul,
    div_eq_mul_inv]
  ring

/-- Bilinearity of the actual connection scales its two velocity slots by the square of the coordinate-time factor. -/
theorem connection_rescale (g : Covector → Mat4) (c : ℝ) (U : Covector → Covector) (x : Covector) :
    connection g x (coordinateVelocity c U x) (coordinateVelocity c U x) =
      (c / U x 0) ^ 2 • connection g x (U x) (U x) := by
  simp only [coordinateVelocity, ← connectionBilin_apply, map_smul, smul_apply, smul_smul, pow_two]

end FoliationQM.CurvedCoordinateVelocity
