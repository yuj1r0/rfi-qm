module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-! Shared scalar conventions. Source: sec:master_equation.
All phases here are local real lifts; no global real phase is postulated.
The three positive parameters are inputs, and clock scales are derived.
-/
@[expose] public section

namespace FoliationQM

structure MassiveParameters where
  c : ℝ
  m : ℝ
  hbar : ℝ
  c_pos : 0 < c
  m_pos : 0 < m
  hbar_pos : 0 < hbar

namespace MassiveParameters
noncomputable def omega0 (p : MassiveParameters) : ℝ := p.m * p.c ^ 2 / p.hbar
noncomputable def period (p : MassiveParameters) : ℝ := 2 * Real.pi * p.hbar / (p.m * p.c ^ 2)
noncomputable def ellC (p : MassiveParameters) : ℝ := p.hbar / (p.m * p.c)
end MassiveParameters

/-- The actual unit complex phase, using a local real lift. -/
noncomputable def phase (φ : ℝ) : ℂ := Complex.exp ((φ : ℂ) * Complex.I)

end FoliationQM
