module

public import FoliationQM.ClockScales
public import Mathlib.Topology.Algebra.Order.Field

/-!
# Actual classical limits of the supplied clock scales

Source: v13 `thm:clock_sideband`. These are genuine filter limits at fixed
positive mass and speed, with a fixed finite real Fisher functional. They do
not assert a limit for a varying density or a family of PDE solutions. Real
formulas are extended to zero so that the two-sided limits also supply the
physical positive-parameter limits by restriction.
-/

@[expose] public section
noncomputable section

namespace FoliationQM.ClockScaleLimits
open Filter
open scoped Topology

/-- The reduced Compton radius as a function of the action scale at fixed mass and speed. -/
def radius (m c h : ℝ) : ℝ := h / (m * c)

/-- The proper-clock period as a function of the action scale at fixed mass and speed. -/
def period (m c h : ℝ) : ℝ := 2 * Real.pi * h / (m * c ^ 2)

/-- The fixed-parameter radius agrees with the project's derived physical scale. -/
theorem radius_parameters (p : MassiveParameters) : radius p.m p.c p.hbar = p.ellC := rfl

/-- The fixed-parameter period agrees with the project's derived physical scale. -/
theorem period_parameters (p : MassiveParameters) : period p.m p.c p.hbar = p.period := rfl

/-- The actual reduced radius tends to zero as the action scale tends to zero. -/
theorem radius_tendsto_zero (m c : ℝ) : Tendsto (radius m c) (𝓝 0) (𝓝 0) := by
  unfold radius
  simpa only [zero_div] using!
    (tendsto_id : Tendsto (fun h : ℝ => h) (𝓝 0) (𝓝 0)).div_const (m * c)

/-- The actual proper-clock period tends to zero with the action scale. -/
theorem period_tendsto_zero (m c : ℝ) : Tendsto (period m c) (𝓝 0) (𝓝 0) := by
  unfold period
  simpa only [mul_zero, zero_div] using!
    ((tendsto_id : Tendsto (fun h : ℝ => h) (𝓝 0) (𝓝 0)).const_mul (2 * Real.pi)).div_const
      (m * c ^ 2)

/-- At fixed positive mass and speed, vanishing radius is equivalent to vanishing action scale along any filter. -/
theorem radius_tendsto_zero_iff {A : Type*} {l : Filter A} {h : A → ℝ}
    {m c : ℝ} (hm : 0 < m) (hc : 0 < c) :
    Tendsto (fun x => radius m c (h x)) l (𝓝 0) ↔ Tendsto h l (𝓝 0) := by
  have hmc : m * c ≠ 0 := mul_ne_zero hm.ne' hc.ne'
  constructor
  · intro ht
    have hr := ht.mul_const (m * c)
    simpa [radius, hmc] using hr
  · intro ht
    simpa [radius] using ht.div_const (m * c)

/-- The exact Fisher coefficient hbar squared over four has an actual zero classical limit. -/
theorem fisher_coefficient_tendsto_zero :
    Tendsto (fun h : ℝ => h ^ 2 / 4) (𝓝 0) (𝓝 0) := by
  simpa using ((tendsto_id : Tendsto (fun h : ℝ => h) (𝓝 0) (𝓝 0)).pow 2).div_const 4

/-- The supplied Fisher penalty tends to zero for a fixed finite density functional. -/
theorem fixed_fisher_penalty_tendsto_zero (I : ℝ) :
    Tendsto (fun h : ℝ => (h ^ 2 / 4) * I) (𝓝 0) (𝓝 0) := by
  simpa using fisher_coefficient_tendsto_zero.mul_const I

/-- The corresponding fixed-density nonrelativistic Bohm energy has the same actual zero classical limit. -/
theorem fixed_bohm_energy_tendsto_zero (m I : ℝ) :
    Tendsto (fun h : ℝ => h ^ 2 / (8 * m) * I) (𝓝 0) (𝓝 0) := by
  simpa using (((tendsto_id : Tendsto (fun h : ℝ => h) (𝓝 0) (𝓝 0)).pow 2).div_const
    (8 * m)).mul_const I

end FoliationQM.ClockScaleLimits
