module

public import FoliationQM.Conventions

/-! Pointwise algebra for thm:adm_positivity(iii), eq:dressed_mass_velocity,
eq:clock_vs_proper_oneform, and eq:noether_current. Kind A; components only.
`dS` and `velocityCovector` have lowered indices. With the fixed diagonal
metric, the inverse-metric contraction has the same (+---) coefficients.
No differentiability, PDE, observer geometry, or closedness is asserted.
-/
@[expose] public section

namespace FoliationQM

abbrev Covector := Fin 4 → ℝ

/-- Explicit inverse Minkowski bilinear form; no function-space norm is used. -/
def minkowski (p q : Covector) : ℝ :=
  p 0 * q 0 - p 1 * q 1 - p 2 * q 2 - p 3 * q 3

noncomputable def effectiveMass (c : ℝ) (dS : Covector) : ℝ :=
  Real.sqrt (minkowski dS dS) / c

noncomputable def velocityCovector (c : ℝ) (dS : Covector) : Covector :=
  fun μ => -dS μ / effectiveMass c dS

/-- eq:dressed_mass_velocity, positivity from the actual timelike domain. -/
theorem effectiveMass_pos {c : ℝ} {dS : Covector}
    (hc : 0 < c) (ht : 0 < minkowski dS dS) : 0 < effectiveMass c dS := by
  exact div_pos (Real.sqrt_pos.2 ht) hc

/-- eq:dressed_mass_velocity, squared mass identity without a mass-shell assumption. -/
theorem effectiveMass_sq {c : ℝ} {dS : Covector}
    (_hc : 0 < c) (ht : 0 < minkowski dS dS) :
    effectiveMass c dS ^ 2 = minkowski dS dS / c ^ 2 := by
  simp [effectiveMass, div_pow, Real.sq_sqrt ht.le]

/-- eq:dressed_mass_velocity, actual inverse-Minkowski normalization. -/
theorem velocity_normalized {c : ℝ} {dS : Covector}
    (hc : 0 < c) (ht : 0 < minkowski dS dS) :
    minkowski (velocityCovector c dS) (velocityCovector c dS) = c ^ 2 := by
  have hm : effectiveMass c dS ≠ 0 := ne_of_gt (effectiveMass_pos hc ht)
  have hs := effectiveMass_sq hc ht
  have hc0 : c ≠ 0 := ne_of_gt hc
  have hs' : effectiveMass c dS ^ 2 * c ^ 2 = minkowski dS dS :=
    (eq_div_iff (pow_ne_zero 2 hc0)).1 hs
  unfold minkowski velocityCovector
  field_simp
  dsimp [minkowski] at hs'
  nlinarith [hs']

/-- Future direction is separate from timelikeness. -/
theorem velocity_future {c : ℝ} {dS : Covector}
    (hc : 0 < c) (ht : 0 < minkowski dS dS) (hf : dS 0 < 0) :
    0 < velocityCovector c dS 0 := by
  exact div_pos (neg_pos.2 hf) (effectiveMass_pos hc ht)

/-- eq:clock_vs_proper_oneform, equality of covector components only. -/
theorem clock_dressing (p : MassiveParameters) (dS : Covector)
    (ht : 0 < minkowski dS dS) (μ : Fin 4) :
    -dS μ / (p.m * p.c ^ 2) =
      (effectiveMass p.c dS / p.m) * (velocityCovector p.c dS μ / p.c ^ 2) := by
  have hm := ne_of_gt (effectiveMass_pos p.c_pos ht)
  have hc := ne_of_gt p.c_pos
  have hmass := ne_of_gt p.m_pos
  unfold velocityCovector
  field_simp

/-- eq:noether_current, factorization of the supplied phase-current expression.
This does not prove a Noether theorem or current conservation. -/
theorem current_factorization (p : MassiveParameters) (dS : Covector)
    (ht : 0 < minkowski dS dS) (rho : ℝ) (μ : Fin 4) :
    -(rho / p.m) * dS μ =
      (rho * effectiveMass p.c dS / p.m) * velocityCovector p.c dS μ := by
  have hm := ne_of_gt (effectiveMass_pos p.c_pos ht)
  unfold velocityCovector
  field_simp

/-- A concrete future timelike instance: the rest covector. -/
def restCovector (c m : ℝ) : Covector := fun μ => if μ = 0 then -(m * c) else 0

/-- Nonvacuity for the massive domain, with no imposed PDE. -/
theorem rest_timelike (p : MassiveParameters) :
    0 < minkowski (restCovector p.c p.m) (restCovector p.c p.m) := by
  have hm := p.m_pos
  have hc := p.c_pos
  change 0 < (-(p.m * p.c)) * (-(p.m * p.c)) - 0 * 0 - 0 * 0 - 0 * 0
  nlinarith [mul_pos hm hc]

end FoliationQM
