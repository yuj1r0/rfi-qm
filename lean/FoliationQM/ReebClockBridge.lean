module

public import FoliationQM.ReebFlow
public import FoliationQM.ClockScales
public import FoliationQM.ActionClockCircle

/-!
# Affine Reeb flow and the stipulated periodic clock readout

Sources: v13 `thm:contact_period` and the clock scales used in
`thm:clock_sideband`. The actual future-shell trajectories are injective.
Periodic proper-clock compactification is an additional circle-valued
readout of the action parameter, not a conclusion that these flat-shell
trajectories close. The signed conversion is the one proved for the actual
Reeb and proper-time curves.
-/

@[expose] public section
noncomputable section

namespace FoliationQM.ReebClockBridge
open ContactReeb ReebFlow

/-- A massive future-shell proper-time trajectory is injective in its actual real parameter. -/
theorem properLine_injective {m c : ℝ} (hm : 0 < m) {z : Ambient}
    (hs : OnShell m c z.2) : Function.Injective (properLine m z) := by
  intro s t h
  have he := congrArg (fun y : Ambient => y.1 0) h
  change z.1 0 + s * properVelocity m z.2 0 = z.1 0 + t * properVelocity m z.2 0 at he
  exact mul_right_cancel₀ (properVelocity_future hm hs).ne' (add_left_cancel he)

/-- The actual massive future-shell Reeb action trajectory is also injective. -/
theorem actionLine_injective {m c : ℝ} (hm : 0 < m) (hc : 0 < c) {z : Ambient}
    (hs : OnShell m c z.2) : Function.Injective (actionLine m c z) := by
  intro s t h
  have he := congrArg (fun y : Ambient => y.1 0) h
  change z.1 0 + s * (reeb m c z.2).1 0 = z.1 0 + t * (reeb m c z.2).1 0 at he
  have hv : (reeb m c z.2).1 0 ≠ 0 := by
    change -z.2 0 / (m ^ 2 * c ^ 2) ≠ 0
    exact div_ne_zero (neg_ne_zero.mpr hs.2.ne')
      (mul_ne_zero (pow_ne_zero _ hm.ne') (pow_ne_zero _ hc.ne'))
  exact mul_right_cancel₀ hv (add_left_cancel he)

/-- The actual proper-time curve returns to a point after a shift only for zero shift. -/
theorem properLine_return_iff {m c : ℝ} (hm : 0 < m) {z : Ambient}
    (hs : OnShell m c z.2) (τ T : ℝ) :
    properLine m z (τ + T) = properLine m z τ ↔ T = 0 := by
  rw [(properLine_injective hm hs).eq_iff]
  exact add_eq_left

/-- The actual action curve returns to a point after a shift only for zero shift. -/
theorem actionLine_return_iff {m c : ℝ} (hm : 0 < m) (hc : 0 < c) {z : Ambient}
    (hs : OnShell m c z.2) (s T : ℝ) :
    actionLine m c z (s + T) = actionLine m c z s ↔ T = 0 := by
  rw [(actionLine_injective hm hc hs).eq_iff]
  exact add_eq_left

/-- The positive derived clock period does not close the underlying affine proper-time trajectory. -/
theorem properLine_period_ne (p : MassiveParameters) {z : Ambient}
    (hs : OnShell p.m p.c z.2) (τ : ℝ) :
    properLine p.m z (τ + p.period) ≠ properLine p.m z τ := by
  rw [ne_eq, properLine_return_iff p.m_pos hs]
  exact (ClockScales.period_pos p).ne'

/-- One derived proper-clock period changes the actual Reeb action parameter by minus the adopted action quantum. -/
theorem proper_period_action_shift (p : MassiveParameters) (τ : ℝ) :
    -p.m * p.c ^ 2 * (τ + p.period) =
      -p.m * p.c ^ 2 * τ - 2 * Real.pi * p.hbar := by
  unfold MassiveParameters.period
  field_simp [p.m_pos.ne', p.c_pos.ne']
  ring

/-- Along the actual proper-time flow the stipulated clock readout repeats after its fundamental period while the trajectory advances. -/
theorem actual_flow_clock_cycle (p : MassiveParameters) {z : Ambient}
    (hs : OnShell p.m p.c z.2) (τ : ℝ) :
    actionLine p.m p.c z (-p.m * p.c ^ 2 * (τ + p.period)) =
        properLine p.m z (τ + p.period) ∧
      properLine p.m z (τ + p.period) ≠ properLine p.m z τ ∧
      ((-p.m * p.c ^ 2 * (τ + p.period) : ℝ) : ActionClockCircle.ActionCircle p) =
        ((-p.m * p.c ^ 2 * τ : ℝ) : ActionClockCircle.ActionCircle p) := by
  refine ⟨actionLine_reparam p.m_pos p.c_pos z _, properLine_period_ne p hs τ, ?_⟩
  simpa only [ActionClockCircle.properToAction_coe] using
    ActionClockCircle.properToAction_periodic p τ

end FoliationQM.ReebClockBridge
