module

public import FoliationQM.Conventions

/-! Exact relationships among the derived massive-clock scales.
Sources: sec:master_equation, eq:master_local_metric, thm:clock_sideband.
Kind A. Positivity comes from the three physical input parameters; the period
and Compton radius are never introduced as independent assumptions.
-/
@[expose] public section

namespace FoliationQM.ClockScales

/-- The derived Compton frequency is positive. -/
theorem omega0_pos (p : MassiveParameters) : 0 < p.omega0 := by
  exact div_pos (mul_pos p.m_pos (sq_pos_of_pos p.c_pos)) p.hbar_pos

/-- The derived clock period is positive. -/
theorem period_pos (p : MassiveParameters) : 0 < p.period := by
  exact div_pos (mul_pos (mul_pos (by norm_num) Real.pi_pos) p.hbar_pos)
    (mul_pos p.m_pos (sq_pos_of_pos p.c_pos))

/-- The reduced Compton radius is positive. -/
theorem ellC_pos (p : MassiveParameters) : 0 < p.ellC := by
  exact div_pos p.hbar_pos (mul_pos p.m_pos p.c_pos)

/-- Source eq:master_local_metric: both supplied phase-frequency expressions agree. -/
theorem omega0_eq_two_pi_div_period (p : MassiveParameters) :
    p.omega0 = 2 * Real.pi / p.period := by
  have hc := ne_of_gt p.c_pos
  have hm := ne_of_gt p.m_pos
  have hh := ne_of_gt p.hbar_pos
  have hpi := ne_of_gt Real.pi_pos
  unfold MassiveParameters.omega0 MassiveParameters.period
  field_simp

/-- Source sec:master_equation: the clock-radius and Compton formulas agree. -/
theorem clock_radius (p : MassiveParameters) :
    p.c * p.period / (2 * Real.pi) = p.ellC := by
  have hc := ne_of_gt p.c_pos
  have hm := ne_of_gt p.m_pos
  have hpi := ne_of_gt Real.pi_pos
  unfold MassiveParameters.period MassiveParameters.ellC
  field_simp

/-- Source eq:master_local_metric: the displayed period coefficient is ellC/2. -/
theorem period_metric_factor (p : MassiveParameters) :
    p.c * p.period / (4 * Real.pi) = p.ellC / 2 := by
  calc
    p.c * p.period / (4 * Real.pi) = (p.c * p.period / (2 * Real.pi)) / 2 := by ring
    _ = p.ellC / 2 := by rw [clock_radius]

/-- Source thm:clock_sideband: period substitution gives the Fisher coefficient.
This proves the scalar substitution; clock averaging and KL analysis are separate. -/
theorem period_fisher_coefficient (p : MassiveParameters) :
    p.m ^ 2 * p.c ^ 4 * p.period ^ 2 / (16 * Real.pi ^ 2) = p.hbar ^ 2 / 4 := by
  have hc := ne_of_gt p.c_pos
  have hm := ne_of_gt p.m_pos
  have hpi := ne_of_gt Real.pi_pos
  unfold MassiveParameters.period
  field_simp
  ring

end FoliationQM.ClockScales
