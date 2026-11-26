module

public import FoliationQM.PolarDifferential
public import FoliationQM.ClockScales

/-! Source eq:master_local_metric in its literal clock-period normalization.
Kind C: actual real Frechet derivatives of differentiable fields on any real
normed vector space. This is the local target-space metric and its pullback;
no global real phase, spacetime isometry, or smooth cone completion is asserted.
-/
@[expose] public section

namespace FoliationQM.MasterEquation

open PolarDifferential

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The source field using its derived physical clock period. -/
noncomputable def clockWave (p : MassiveParameters) (ρ τ : E → ℝ) : E → ℂ :=
  polarField ρ (fun y => -(2 * Real.pi / p.period) * τ y)

/-- Source eq:master_local_metric: both displayed equalities, with actual
field derivatives, on the positive-density domain. All increments are the
values of Frechet derivatives at an arbitrary tangent vector `v`. -/
theorem master_local_metric (p : MassiveParameters) {ρ τ : E → ℝ} {x : E}
    (hρ : DifferentiableAt ℝ ρ x) (hτ : DifferentiableAt ℝ τ x)
    (hpos : 0 < ρ x) (v : E) :
    (‖fderiv ℝ (clockWave p ρ τ) x v‖ ^ 2 =
      (fderiv ℝ ρ x v) ^ 2 / (4 * ρ x) +
        ρ x * (fderiv ℝ (fun y => -(2 * Real.pi / p.period) * τ y) x v) ^ 2) ∧
    (‖fderiv ℝ (clockWave p ρ τ) x v‖ ^ 2 =
      (ρ x / p.ellC ^ 2) *
        (p.c ^ 2 * (fderiv ℝ τ x v) ^ 2 +
          (p.c * p.period / (4 * Real.pi)) ^ 2 *
            (fderiv ℝ (fun y => Real.log (ρ y)) x v) ^ 2)) := by
  constructor
  · exact fderiv_polarField_norm_sq hρ (hτ.const_mul _) hpos v
  · unfold clockWave
    rw [← ClockScales.omega0_eq_two_pi_div_period]
    rw [fderiv_clockField_norm_sq p hρ hτ hpos v, ClockScales.period_metric_factor]
    ring

end FoliationQM.MasterEquation
