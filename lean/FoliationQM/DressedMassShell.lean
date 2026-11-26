module

public import FoliationQM.DressedVelocity

/-!
# Effective mass on the timelike Hamilton–Jacobi shell

For v13 `thm:adm_positivity` and `eq:dressed_mass_velocity`, the quantum
correction to the squared covector norm enters the mass through the
reduced Compton length. Timelikeness determines the domain of its
positive square root.
-/

@[expose] public section
namespace FoliationQM.DressedMassShell

private theorem shell_factor (p : MassiveParameters) (q : ℝ) :
    (p.m ^ 2 * p.c ^ 2) * (1 + p.ellC ^ 2 * q) = p.m ^ 2 * p.c ^ 2 + p.hbar ^ 2 * q := by
  unfold MassiveParameters.ellC
  field_simp [p.m_pos.ne', p.c_pos.ne']

/-- On the Hamilton–Jacobi shell, positivity of the dimensionless mass radicand
is equivalent to timelikeness of the original covector. -/
theorem timelike_iff_radicand_pos (p : MassiveParameters) {v : Covector} {q : ℝ}
    (hHJ : minkowski v v = p.m ^ 2 * p.c ^ 2 + p.hbar ^ 2 * q) :
    0 < minkowski v v ↔ 0 < 1 + p.ellC ^ 2 * q := by
  rw [hHJ, ← shell_factor, mul_pos_iff_of_pos_left (mul_pos (sq_pos_of_pos p.m_pos) (sq_pos_of_pos p.c_pos))]

/-- A timelike covector satisfying the Hamilton–Jacobi shell has a strictly positive mass radicand. -/
theorem radicand_pos (p : MassiveParameters) {v : Covector} {q : ℝ} (ht : 0 < minkowski v v)
    (hHJ : minkowski v v = p.m ^ 2 * p.c ^ 2 + p.hbar ^ 2 * q) : 0 < 1 + p.ellC ^ 2 * q :=
  (timelike_iff_radicand_pos p hHJ).mp ht

/-- The actual effective mass equals the bare mass times the positive Compton-scale square root. -/
theorem mass_formula (p : MassiveParameters) {v : Covector} {q : ℝ} (ht : 0 < minkowski v v)
    (hHJ : minkowski v v = p.m ^ 2 * p.c ^ 2 + p.hbar ^ 2 * q) :
    effectiveMass p.c v = p.m * Real.sqrt (1 + p.ellC ^ 2 * q) := by
  have hr := radicand_pos p ht hHJ
  apply (sq_eq_sq₀ (effectiveMass_pos p.c_pos ht).le (mul_nonneg p.m_pos.le (Real.sqrt_nonneg _))).mp
  rw [effectiveMass_sq p.c_pos ht, hHJ, ← shell_factor, mul_pow, Real.sq_sqrt hr.le]
  field_simp [p.c_pos.ne']

/-- On the timelike shell the effective mass equals the bare mass exactly at zero correction. -/
theorem mass_eq_bare_iff (p : MassiveParameters) {v : Covector} {q : ℝ} (ht : 0 < minkowski v v)
    (hHJ : minkowski v v = p.m ^ 2 * p.c ^ 2 + p.hbar ^ 2 * q) :
    effectiveMass p.c v = p.m ↔ q = 0 := by
  constructor
  · intro hm
    have hs := effectiveMass_sq p.c_pos ht
    rw [hm, eq_div_iff (pow_ne_zero 2 p.c_pos.ne')] at hs
    have hq : p.hbar ^ 2 * q = 0 := by linarith
    exact (mul_eq_zero.mp hq).resolve_left (pow_ne_zero 2 p.hbar_pos.ne')
  · intro hq
    simp [mass_formula p ht hHJ, hq]

end FoliationQM.DressedMassShell
