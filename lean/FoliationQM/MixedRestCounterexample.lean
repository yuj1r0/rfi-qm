module

public import FoliationQM.MixedRestPhase
public import FoliationQM.NonrelativisticParameterFamily
public import FoliationQM.ControlledRestEnvelopeLimit
public import FoliationQM.DressedClockWorldline

/-!
# Slow phase and exact rest direction without strong remainder decay

Source: v13 `cor:schrodinger`, kinds C and D. The same explicit mixed KG
wave has a genuine smooth logarithmic phase, normalized rest velocity and
uniformly small relative phase rate. Its actual scaled second derivative
and Schrödinger residual nevertheless have fixed positive norms. This
tests the unqualified slow-phase inference, while retaining the proved
controlled and weak limit interpretations.
-/

@[expose] public section
noncomputable section

namespace FoliationQM.MixedRestCounterexample

open Filter MixedRestMode MixedRestPhase NonrelativisticParameterFamily
open PolarSecondDifferential RestEnvelopeKG RestEnvelopeRemainder
open DressedMassDensityVariation
open Madelung (coordinateVector)
open scoped Topology ContDiff

private theorem inverse_square_lt_one (p : MassiveParameters) (hc : 1 < p.c) :
    (p.c ^ 2)⁻¹ < 1 :=
  inv_lt_one_of_one_lt₀ (by nlinarith)

/-- The actual reduced-phase derivative has a uniform absolute bound and a vanishing-scale relative bound. -/
theorem slow_phase_bounds (p : MassiveParameters) (hc : 1 < p.c) (t : ℝ) :
    |deriv (reducedAction p) t| ≤ 2 * p.m / (1 - (p.c ^ 2)⁻¹) ∧
      |deriv (reducedAction p) t| / (p.m * p.c ^ 2) ≤ 2 / (p.c ^ 2 - 1) := by
  have hmpos := p.m_pos
  have hcpos := p.c_pos
  have ha := inverse_square_lt_one p hc
  have hb := (right_half_plane p hc t).2
  have hden : 0 < 1 - (p.c ^ 2)⁻¹ := sub_pos.mpr ha
  have hnorm : 0 < ‖curve p t‖ := lt_of_lt_of_le hden hb
  have hbound : |deriv (reducedAction p) t| ≤ 2 * p.m / (1 - (p.c ^ 2)⁻¹) := by
    rw [(hasDerivAt_reducedAction p hc t).deriv, abs_mul, abs_of_pos p.hbar_pos]
    calc
      _ ≤ p.hbar * ‖deriv (curve p) t / curve p t‖ :=
        mul_le_mul_of_nonneg_left (Complex.abs_im_le_norm _) p.hbar_pos.le
      _ = 2 * p.m / ‖curve p t‖ := by
        rw [norm_div, (curve_norms p t).2.1]
        field_simp [p.hbar_pos.ne', hnorm.ne']
      _ ≤ _ := div_le_div_of_nonneg_left (by positivity) hden hb
  refine ⟨hbound, ?_⟩
  calc
    _ ≤ (2 * p.m / (1 - (p.c ^ 2)⁻¹)) / (p.m * p.c ^ 2) :=
      div_le_div_of_nonneg_right hbound (by positivity)
    _ = _ := by
      have hsq : p.c ^ 2 - 1 ≠ 0 := by nlinarith
      field_simp [p.m_pos.ne', p.c_pos.ne', hden.ne', hsq]

/-- The genuine normal-coordinate phase differential determines a positive dressed mass and the exact normalized rest velocity. -/
theorem normal_phase_rest (p : MassiveParameters) (hc : 1 < p.c) (y : Covector) :
    let κ := p.m * (1 - ((p.c ^ 2)⁻¹) ^ 2) / ‖curve p (y 0 / p.c)‖ ^ 2
    0 < κ ∧ phaseDifferential (normalAction p) y = restCovector p.c κ ∧
      0 < minkowski (phaseDifferential (normalAction p) y)
        (phaseDifferential (normalAction p) y) ∧
      phaseDifferential (normalAction p) y 0 < 0 ∧
      effectiveMass p.c (phaseDifferential (normalAction p) y) = κ ∧
      DressedClockWorldline.velocity p (normalAction p) y = p.c • coordinateVector 0 := by
  dsimp only
  let κ := p.m * (1 - ((p.c ^ 2)⁻¹) ^ 2) / ‖curve p (y 0 / p.c)‖ ^ 2
  have ha := inverse_square_lt_one p hc
  have ha0 : 0 < (p.c ^ 2)⁻¹ := by positivity
  have hnorm : 0 < ‖curve p (y 0 / p.c)‖ :=
    lt_of_lt_of_le (sub_pos.mpr ha) (right_half_plane p hc _).2
  have hk : 0 < κ := by
    exact div_pos (mul_pos p.m_pos (by nlinarith)) (sq_pos_of_pos hnorm)
  have hi : HasFDerivAt (fun z : Covector => z 0 / p.c)
      (p.c⁻¹ • (ContinuousLinearMap.proj 0 : Covector →L[ℝ] ℝ)) y := by
    simpa only [div_eq_mul_inv] using (hasFDerivAt_apply (0 : Fin 4) y).mul_const p.c⁻¹
  have hs := (hasDerivAt_totalAction p hc (y 0 / p.c)).comp_hasFDerivAt y hi
  have hs' : HasFDerivAt (normalAction p)
      ((-p.m * p.c ^ 2 * (1 - ((p.c ^ 2)⁻¹) ^ 2) / ‖curve p (y 0 / p.c)‖ ^ 2) •
        (p.c⁻¹ • (ContinuousLinearMap.proj 0 : Covector →L[ℝ] ℝ))) y := hs
  have hd : phaseDifferential (normalAction p) y = restCovector p.c κ := by
    ext i
    change fderiv ℝ (normalAction p) y (coordinateVector i) = _
    rw [hs'.fderiv]
    by_cases hi0 : i = 0
    · subst i
      simp only [smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul,
        coordinateVector, Pi.single_eq_same, mul_one, restCovector]
      dsimp [κ]
      field_simp [p.c_pos.ne', hnorm.ne']
    · simp [smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul,
        coordinateVector, restCovector, hi0]
  have he : minkowski (restCovector p.c κ) (restCovector p.c κ) = (κ * p.c) ^ 2 := by
    simp [minkowski, restCovector]
    ring
  have hm : effectiveMass p.c (phaseDifferential (normalAction p) y) = κ := by
    rw [hd]
    unfold effectiveMass
    rw [he, Real.sqrt_sq (mul_pos hk p.c_pos).le]
    exact mul_div_cancel_right₀ κ p.c_pos.ne'
  refine ⟨hk, hd, ?_, ?_, hm, ?_⟩
  · rw [hd, he]
    exact sq_pos_of_pos (mul_pos hk p.c_pos)
  · rw [hd]
    exact neg_neg_of_pos (mul_pos hk p.c_pos)
  · have hmr : effectiveMass p.c (restCovector p.c κ) = κ := by simpa only [hd] using hm
    ext i
    simp only [DressedClockWorldline.velocity, ContactReeb.sharp, velocityCovector, hd, hmr]
    by_cases hi0 : i = 0
    · subst i
      simp [restCovector, coordinateVector, hk.ne']
    · simp [restCovector, coordinateVector, hi0]

/-- The actual scaled temporal derivative and Schrödinger residual retain positive exact norms for every physical c. -/
theorem field_remainder_norms (p : MassiveParameters) (x : Covector) :
    ‖(p.c ^ 2)⁻¹ • secondDirectionalDerivative (field p) (coordinateVector 0) x‖ =
      4 * p.m ^ 2 / p.hbar ^ 2 ∧
      ‖schrodingerResidual p (field p) x‖ = 2 * p.m := by
  have hcpos := p.c_pos
  have hd : secondDirectionalDerivative (field p) (coordinateVector 0) x =
      deriv (deriv (curve p)) (x 0) := by
    simpa [coordinateVector] using (field_derivatives p x (coordinateVector 0)).2
  constructor
  · rw [hd, norm_smul, Real.norm_eq_abs, abs_of_pos (show 0 < (p.c ^ 2)⁻¹ by positivity),
      (curve_norms p (x 0)).2.2]
    field_simp [p.c_pos.ne']
  · have he := source_norm_residual_of_KG p
      ((contDiff_original p).contDiffAt.of_le (by simp))
      (original_kg p (LaboratoryCoordinates.toNormal p.c x))
    rw [envelope_original, hd, (curve_norms p (x 0)).2.2] at he
    rw [he, temporalCoefficient]
    field_simp [p.m_pos.ne', p.c_pos.ne', p.hbar_pos.ne']
    ring

/-- One explicit original KG family has genuine rest velocity and uniformly slow relative phase, while its actual strong remainders never decay. -/
theorem counterexample_family (p : MassiveParameters) :
    (∀ n, (∀ y, FlatIntegrationByParts.kgOperator (ramp p n) (original (ramp p n))
        coordinateVector y = 0) ∧
      envelope (ramp p n) (original (ramp p n)) = field (ramp p n) ∧
      ContDiff ℝ ∞ (normalAction (ramp p n)) ∧
      (∀ y, DressedClockWorldline.velocity (ramp p n) (normalAction (ramp p n)) y =
        (ramp p n).c • coordinateVector 0)) ∧
    TendstoUniformlyOn (fun n => field (ramp p n)) (fun _ => (1 : ℂ)) atTop Set.univ ∧
    TendstoUniformlyOn (fun n t => deriv (reducedAction (ramp p n)) t /
      (p.m * (ramp p n).c ^ 2)) (fun _ => (0 : ℝ)) atTop Set.univ ∧
    (∀ n x, ‖((ramp p n).c ^ 2)⁻¹ •
        secondDirectionalDerivative (field (ramp p n)) (coordinateVector 0) x‖ =
        4 * p.m ^ 2 / p.hbar ^ 2 ∧
      ‖schrodingerResidual p (field (ramp p n)) x‖ = 2 * p.m) ∧
    0 < 4 * p.m ^ 2 / p.hbar ^ 2 ∧ 0 < 2 * p.m := by
  have hmpos := p.m_pos
  have hhpos := p.hbar_pos
  have hc (n : ℕ) : 1 < (ramp p n).c := (ramp_spec p).1 n |>.2.2.2
  have hsmall : Tendsto (fun n => ((ramp p n).c ^ 2)⁻¹) atTop (𝓝 0) := by
    simpa only [Pi.inv_apply, inv_pow, zero_pow two_ne_zero] using
      (ramp_spec p).2.inv_tendsto_atTop.pow 2
  have hphase : Tendsto (fun n => 2 / ((ramp p n).c ^ 2 - 1)) atTop (𝓝 0) := by
    have h := (hsmall.const_mul 2).div (tendsto_const_nhds.sub hsmall)
      (show (1 : ℝ) - 0 ≠ 0 by norm_num)
    have he (n : ℕ) :
        2 * ((ramp p n).c ^ 2)⁻¹ / (1 - ((ramp p n).c ^ 2)⁻¹) =
          2 / ((ramp p n).c ^ 2 - 1) := by
      have ha := inverse_square_lt_one (ramp p n) (hc n)
      have hs : (ramp p n).c ^ 2 - 1 ≠ 0 := by nlinarith [hc n]
      field_simp [(ramp p n).c_pos.ne', (sub_pos.mpr ha).ne', hs]
    change Tendsto (fun n => 2 * ((ramp p n).c ^ 2)⁻¹ /
      (1 - ((ramp p n).c ^ 2)⁻¹)) atTop (𝓝 (2 * 0 / (1 - 0))) at h
    simpa only [he, mul_zero, sub_zero, zero_div] using h
  refine ⟨?_, ?_, ?_, ?_, by positivity, by positivity⟩
  · intro n
    exact ⟨original_kg (ramp p n), envelope_original (ramp p n),
      (smooth_actions (ramp p n) (hc n)).2.2,
      fun y => (normal_phase_rest (ramp p n) (hc n) y).2.2.2.2.2⟩
  · apply Metric.tendstoUniformlyOn_iff.mpr
    intro ε hε
    filter_upwards [hsmall.eventually_lt_const hε] with n hn x _
    rw [dist_comm, dist_eq_norm]
    exact ((curve_norms (ramp p n) (x 0)).1.trans_lt hn)
  · apply Metric.tendstoUniformlyOn_iff.mpr
    intro ε hε
    filter_upwards [hphase.eventually_lt_const hε] with n hn t _
    have hcpos := (ramp p n).c_pos
    have hb := (slow_phase_bounds (ramp p n) (hc n) t).2
    change |deriv (reducedAction (ramp p n)) t| /
      (p.m * (ramp p n).c ^ 2) ≤ 2 / ((ramp p n).c ^ 2 - 1) at hb
    rw [Real.dist_eq, zero_sub, abs_neg, abs_div, abs_of_pos (show 0 < p.m * (ramp p n).c ^ 2 by positivity)]
    exact hb.trans_lt hn
  · intro n x
    have h := field_remainder_norms (ramp p n) x
    rw [ControlledRestEnvelopeLimit.residual_eq_of_scales p (ramp p n) rfl rfl] at h
    exact h

end FoliationQM.MixedRestCounterexample
