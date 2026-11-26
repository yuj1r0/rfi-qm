module

public import FoliationQM.Conventions
public import Mathlib.Analysis.Complex.Trigonometric

/-!
# Polar tangent metric and cone-parameter algebra

Sources: v13 `eq:master_local_metric`, `eq:lambda_metric`, `eq:cone_angle`,
`lem:uniqueness`, `eq:nonlinear_defect`; supplement
`eq:audit11_master_euclidean`.

These are identities of explicitly supplied tangent components. The complex
exponential, squared complex norm, and real square root are Mathlib operations.
The actual derivative bridge is proved separately in PolarDifferential and
MasterEquation. A metric completion construction is not asserted here. In particular, the numerical cone-angle criterion below is
only an algebraic component of the source's smooth-completion claim.
-/
@[expose] public section

namespace FoliationQM.MasterMetricAndCone

/-- The complex tangent obtained from polar amplitude and phase increments. -/
noncomputable def amplitudeTangent (R Φ dR dΦ : ℝ) : ℂ :=
  phase Φ * ((dR : ℂ) + Complex.I * (R : ℂ) * (dΦ : ℂ))

/-- The density-coordinate tangent on the regular domain `ρ > 0`. -/
noncomputable def polarTangent (ρ Φ dρ dΦ : ℝ) : ℂ :=
  amplitudeTangent (Real.sqrt ρ) Φ (dρ / (2 * Real.sqrt ρ)) dΦ

private theorem normSq_phase (Φ : ℝ) : Complex.normSq (phase Φ) = 1 := by
  simp only [phase, Complex.normSq_apply, Complex.exp_ofReal_mul_I_re,
    Complex.exp_ofReal_mul_I_im]
  nlinarith [Real.sin_sq_add_cos_sq Φ]

/-- Euclidean complex norm squared of the explicit amplitude-phase tangent. -/
theorem amplitudeTangent_normSq (R Φ dR dΦ : ℝ) :
    Complex.normSq (amplitudeTangent R Φ dR dΦ) = dR ^ 2 + R ^ 2 * dΦ ^ 2 := by
  rw [amplitudeTangent, Complex.normSq_mul, normSq_phase, one_mul]
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im]
  ring

/-- The unweighted polar metric, as a pointwise tangent-component identity. -/
theorem polarTangent_normSq (ρ Φ dρ dΦ : ℝ) (hρ : 0 < ρ) :
    Complex.normSq (polarTangent ρ Φ dρ dΦ) = dρ ^ 2 / (4 * ρ) + ρ * dΦ ^ 2 := by
  rw [polarTangent, amplitudeTangent_normSq]
  have hs : (Real.sqrt ρ) ^ 2 = ρ := Real.sq_sqrt hρ.le
  rw [div_pow, mul_pow, hs]
  ring

/-- The same unweighted tangent metric with the supplied clock and log-density
increments substituted. This is not a theorem about derivatives of fields. -/
theorem polarTangent_clock_normSq (p : MassiveParameters) (ρ Φ dρ dτ : ℝ)
    (hρ : 0 < ρ) :
    Complex.normSq (polarTangent ρ Φ dρ (-p.omega0 * dτ)) =
      (ρ / p.ellC ^ 2) *
        (p.c ^ 2 * dτ ^ 2 + (p.ellC ^ 2 / 4) * (dρ / ρ) ^ 2) := by
  rw [polarTangent_normSq ρ Φ dρ (-p.omega0 * dτ) hρ]
  have hc : p.c ≠ 0 := ne_of_gt p.c_pos
  have hm : p.m ≠ 0 := ne_of_gt p.m_pos
  have hh : p.hbar ≠ 0 := ne_of_gt p.hbar_pos
  have hr : ρ ≠ 0 := ne_of_gt hρ
  unfold MassiveParameters.omega0 MassiveParameters.ellC
  field_simp; ring

/-- Algebraic substitution of the source's radial and angular tangent
components. Actual coordinate derivatives are proved in RadialGeometry. -/
theorem radial_angular_metric (hbar coupling ρ dρ dΦ : ℝ)
    (hh : 0 < hbar) (hcoupling : 0 < coupling) (hρ : 0 < ρ) :
    (Real.sqrt coupling / (hbar * Real.sqrt ρ) * dρ) ^ 2 +
      (2 * Real.sqrt coupling / hbar * Real.sqrt ρ) ^ 2 *
        (hbar / (2 * Real.sqrt coupling) * dΦ) ^ 2 =
      coupling / (hbar ^ 2 * ρ) * dρ ^ 2 + ρ * dΦ ^ 2 := by
  have hh0 : hbar ≠ 0 := ne_of_gt hh
  have hcoupling0 : Real.sqrt coupling ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hcoupling)
  have hρ0 : Real.sqrt ρ ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hρ)
  have hscoupling : (Real.sqrt coupling) ^ 2 = coupling := Real.sq_sqrt hcoupling.le
  have hsρ : (Real.sqrt ρ) ^ 2 = ρ := Real.sq_sqrt hρ.le
  simp only [mul_pow, div_pow, hscoupling, hsρ]
  field_simp

/-- The numerical angle in the source's cone family. -/
noncomputable def coneAngle (hbar coupling : ℝ) : ℝ := Real.pi * hbar / Real.sqrt coupling

/-- Angle rescaling of one supplied physical clock period. -/
theorem angular_period (hbar coupling : ℝ) :
    hbar / (2 * Real.sqrt coupling) * (2 * Real.pi) = coneAngle hbar coupling := by
  unfold coneAngle
  ring

/-- Algebraic angle criterion; this makes no claim of smooth completion. -/
theorem coneAngle_eq_two_pi_iff (hbar coupling : ℝ) (hh : 0 < hbar) (hcoupling : 0 < coupling) :
    coneAngle hbar coupling = 2 * Real.pi ↔ coupling = hbar ^ 2 / 4 := by
  have hs : (Real.sqrt coupling) ^ 2 = coupling := Real.sq_sqrt hcoupling.le
  have hspos : 0 < Real.sqrt coupling := Real.sqrt_pos.2 hcoupling
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  unfold coneAngle
  constructor
  · intro h
    have hmul := (div_eq_iff (ne_of_gt hspos)).1 h
    have heq : hbar = 2 * Real.sqrt coupling := by
      apply mul_left_cancel₀ hpi
      nlinarith [hmul]
    rw [heq]
    nlinarith [hs]
  · intro h
    have heq : hbar = 2 * Real.sqrt coupling := by nlinarith [hs]
    apply (div_eq_iff (ne_of_gt hspos)).2
    rw [heq]
    ring

/-- Scalar cone-angle formula for the family allowed by the corrected source.
It holds for every positive real `k`; no winding or map degree is asserted. -/
theorem coneAngle_family (hbar k : ℝ) (hh : 0 < hbar) (hk : 0 < k) :
    coneAngle hbar (hbar ^ 2 / (4 * k ^ 2)) = 2 * Real.pi * k := by
  have hh0 : hbar ≠ 0 := ne_of_gt hh
  have hk0 : k ≠ 0 := ne_of_gt hk
  have hs : Real.sqrt (hbar ^ 2 / (4 * k ^ 2)) = hbar / (2 * k) := by
    rw [show hbar ^ 2 / (4 * k ^ 2) = (hbar / (2 * k)) ^ 2 by ring]
    exact Real.sqrt_sq (by positivity)
  unfold coneAngle
  rw [hs]
  field_simp

/-- Scalar selection inside that family. PhaseCircle separately proves actual
winding; the numerical angle alone does not establish smooth completion. -/
theorem coneAngle_family_eq_two_pi_iff (hbar k : ℝ) (hh : 0 < hbar) (hk : 0 < k) :
    coneAngle hbar (hbar ^ 2 / (4 * k ^ 2)) = 2 * Real.pi ↔ k = 1 := by
  rw [coneAngle_family hbar k hh hk]
  constructor
  · intro h
    nlinarith [Real.pi_pos]
  · intro h
    rw [h, mul_one]

/-- Coefficient of the source's nonlinear amplitude-curvature term. -/
noncomputable def nonlinearDefectCoefficient (hbar coupling : ℝ) : ℝ :=
  1 - 4 * coupling / hbar ^ 2

/-- Exactly the coefficient vanishes. This does not assert that a particular
field's entire defect term is nonzero at every other parameter value. -/
theorem nonlinearDefectCoefficient_eq_zero_iff (hbar coupling : ℝ) (hh : 0 < hbar) :
    nonlinearDefectCoefficient hbar coupling = 0 ↔ coupling = hbar ^ 2 / 4 := by
  have hh0 : hbar ≠ 0 := ne_of_gt hh
  unfold nonlinearDefectCoefficient
  constructor
  · intro h
    have hdiv : 4 * coupling / hbar ^ 2 = 1 := by linarith
    have hmul := (div_eq_iff (pow_ne_zero 2 hh0)).1 hdiv
    linarith
  · intro h
    rw [h]
    field_simp; ring

end FoliationQM.MasterMetricAndCone
