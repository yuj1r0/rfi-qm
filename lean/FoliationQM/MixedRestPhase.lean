module

public import FoliationQM.MixedRestMode
public import FoliationQM.PolarLocalInverse
public import FoliationQM.RestActionPhase

/-!
# The actual global logarithmic phase of the mixed rest mode

Source: v13 `cor:schrodinger`, component kinds C and D. For c greater than
one, the explicit envelope stays in the right half-plane. Its principal
logarithm therefore gives a genuinely smooth global real action. Actual
derivatives and polar reconstruction retain the same original KG field,
with the normal-coordinate action evaluated at physical time y⁰/c.
-/

@[expose] public section
noncomputable section

namespace FoliationQM.MixedRestPhase

open MixedRestMode ActionDensity LaboratoryCoordinates RestEnvelopeKG
open RestEnvelopeDifferential
open scoped ContDiff

/-- The real reduced action is the imaginary part of the actual envelope logarithm. -/
def reducedAction (p : MassiveParameters) (t : ℝ) : ℝ :=
  p.hbar * (Complex.log (curve p t)).im

/-- The actual total action restores the negative physical rest-energy term. -/
def totalAction (p : MassiveParameters) (t : ℝ) : ℝ :=
  -p.m * p.c ^ 2 * t + reducedAction p t

/-- The same total action in original normal coordinates uses physical time y⁰/c. -/
def normalAction (p : MassiveParameters) (y : Covector) : ℝ :=
  totalAction p (y 0 / p.c)

/-- The entire explicit curve lies in the right half-plane and has the stated uniform positive lower norm bound. -/
theorem right_half_plane (p : MassiveParameters) (hc : 1 < p.c) (t : ℝ) :
    0 < (curve p t).re ∧ 1 - (p.c ^ 2)⁻¹ ≤ ‖curve p t‖ := by
  have ha : 0 < (p.c ^ 2)⁻¹ := inv_pos.mpr (sq_pos_of_pos p.c_pos)
  have ha1 : (p.c ^ 2)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by nlinarith [p.c_pos])
  have hz : ‖phase (2 * p.omega0 * t)‖ = 1 := by
    simp only [phase, Complex.norm_exp_ofReal_mul_I]
  have hre : -1 ≤ (phase (2 * p.omega0 * t)).re := by
    have h := Complex.abs_re_le_norm (phase (2 * p.omega0 * t))
    rw [hz] at h
    exact (abs_le.mp h).1
  have hb : 1 - (p.c ^ 2)⁻¹ ≤ (curve p t).re := by
    simp only [curve, Complex.add_re, Complex.one_re, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    nlinarith [mul_le_mul_of_nonneg_left hre ha.le]
  exact ⟨(sub_pos.mpr ha1).trans_le hb, hb.trans (Complex.re_le_norm _)⟩

private theorem curve_mem_slitPlane (p : MassiveParameters) (hc : 1 < p.c) (t : ℝ) :
    curve p t ∈ Complex.slitPlane :=
  Complex.mem_slitPlane_iff.mpr (Or.inl (right_half_plane p hc t).1)

/-- The reduced, total and original-coordinate actions are all genuinely smooth on their entire domains. -/
theorem smooth_actions (p : MassiveParameters) (hc : 1 < p.c) :
    ContDiff ℝ ∞ (reducedAction p) ∧ ContDiff ℝ ∞ (totalAction p) ∧
      ContDiff ℝ ∞ (normalAction p) := by
  have hlog : ContDiff ℝ ∞ (fun t : ℝ => Complex.log (curve p t)) := by
    rw [contDiff_iff_contDiffAt]
    intro t
    exact ((Complex.contDiffAt_log (curve_mem_slitPlane p hc t)).restrict_scalars ℝ).comp t
      (contDiff_curve p).contDiffAt
  have hr : ContDiff ℝ ∞ (reducedAction p) :=
    contDiff_const.mul (Complex.imCLM.contDiff.comp hlog)
  have ht : ContDiff ℝ ∞ (totalAction p) := (contDiff_const.mul contDiff_id).add hr
  have hi : ContDiff ℝ ∞ (fun y : Covector => y 0 / p.c) := by fun_prop
  exact ⟨hr, ht, ht.comp hi⟩

/-- Differentiating the true global logarithmic action gives the actual curve's logarithmic derivative. -/
theorem hasDerivAt_reducedAction (p : MassiveParameters) (hc : 1 < p.c) (t : ℝ) :
    HasDerivAt (reducedAction p) (p.hbar * (deriv (curve p) t / curve p t).im) t := by
  have hlog := (hasDerivAt_curve p t).differentiableAt.hasDerivAt.clog_real
    (curve_mem_slitPlane p hc t)
  have him := Complex.imCLM.hasFDerivAt.comp_hasDerivAt t hlog
  simpa only [reducedAction, Function.comp_apply, Complex.imCLM_apply] using!
    him.const_mul p.hbar

private theorem unit_phase_algebra (a b : ℝ) (z : ℂ) (hz : ‖z‖ = 1) :
    Complex.normSq (1 + (a : ℂ) * z) = 1 + 2 * a * z.re + a ^ 2 ∧
      ((2 * Complex.I * (b : ℂ) * z) / (1 + (a : ℂ) * z)).im =
        2 * b * (z.re + a) / Complex.normSq (1 + (a : ℂ) * z) := by
  have hunit : z.re * z.re + z.im * z.im = 1 := by
    simp only [← Complex.normSq_apply, Complex.normSq_eq_norm_sq, hz, one_pow]
  constructor
  · rw [Complex.normSq_apply]
    simp only [Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im,
      Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
    calc
      _ = 1 + 2 * a * z.re + a ^ 2 * (z.re * z.re + z.im * z.im) := by ring
      _ = _ := by rw [hunit]; ring
  · norm_num [Complex.div_im, Complex.mul_re, Complex.mul_im]
    calc
      _ = (2 * b * (z.re + a * (z.re * z.re + z.im * z.im))) /
          Complex.normSq (1 + (a : ℂ) * z) := by ring
      _ = _ := by rw [hunit]; ring

/-- The same total action has the exact negative time derivative determined by the mixed wave's actual squared modulus. -/
theorem hasDerivAt_totalAction (p : MassiveParameters) (hc : 1 < p.c) (t : ℝ) :
    HasDerivAt (totalAction p)
      (-p.m * p.c ^ 2 * (1 - ((p.c ^ 2)⁻¹) ^ 2) / ‖curve p t‖ ^ 2) t := by
  let a : ℝ := (p.c ^ 2)⁻¹
  let z : ℂ := phase (2 * p.omega0 * t)
  have hz : ‖z‖ = 1 := by simp only [z, phase, Complex.norm_exp_ofReal_mul_I]
  obtain ⟨hN, hQ⟩ := unit_phase_algebra a (p.m / p.hbar) z hz
  change Complex.normSq (curve p t) = 1 + 2 * a * z.re + a ^ 2 at hN
  have hq : (deriv (curve p) t / curve p t).im =
      2 * (p.m / p.hbar) * (z.re + a) / Complex.normSq (curve p t) := by
    rw [(hasDerivAt_curve p t).deriv]
    simpa only [curve, a, z, Complex.ofReal_div] using hQ
  have hNpos : 0 < Complex.normSq (curve p t) :=
    Complex.normSq_pos.mpr (Complex.slitPlane_ne_zero (curve_mem_slitPlane p hc t))
  have hd := ((hasDerivAt_id t).const_mul (-p.m * p.c ^ 2)).add
    (hasDerivAt_reducedAction p hc t)
  change HasDerivAt (totalAction p) _ t at hd
  apply hd.congr_deriv
  simp only [mul_one]
  rw [hq, ← Complex.normSq_eq_norm_sq]
  field_simp [hNpos.ne', p.hbar_pos.ne']
  rw [hN]
  dsimp [a]
  field_simp [p.c_pos.ne']
  ring

/-- The actual logarithmic reduced action reconstructs the same curve as a whole function, including any zero value. -/
theorem curve_reconstruction (p : MassiveParameters) :
    actionField p (fun t => Complex.normSq (curve p t)) (reducedAction p) = curve p := by
  funext t
  simp only [actionField, PolarDifferential.polarField, reducedAction,
    mul_div_cancel_left₀ _ p.hbar_pos.ne', ← Complex.norm_def]
  exact PolarLocalInverse.norm_mul_phase_log (curve p t)

private theorem normal_reconstruction (p : MassiveParameters) :
    actionField p (fun y => Complex.normSq (curve p (y 0 / p.c))) (normalAction p) =
      original p := by
  have he : actionField p (fun x : Covector => Complex.normSq (curve p (x 0)))
      (fun x => reducedAction p (x 0)) = field p := by
    funext x
    exact congrFun (curve_reconstruction p) (x 0)
  have hp : actionField p (fun x : Covector => Complex.normSq (curve p (x 0)))
      (fun x => totalAction p (x 0)) = pullback p.c (original p) := by
    unfold totalAction
    rw [RestActionPhase.actionField_rest_split, he, ← envelope_original,
      dressedField_envelope]
  funext y
  have hi : toNormal p.c (toNormal p.c⁻¹ y) = y := by
    ext i
    by_cases h : i = 0
    · subst i
      simp [toNormal_apply, p.c_pos.ne']
    · simp [toNormal_apply, h]
  have h := congrFun hp (toNormal p.c⁻¹ y)
  change _ = original p (toNormal p.c (toNormal p.c⁻¹ y)) at h
  rw [hi] at h
  simpa only [actionField, PolarDifferential.polarField, normalAction,
    toNormal_apply, ite_true, div_eq_mul_inv, mul_comm] using h

/-- A genuinely smooth positive normal-coordinate density and the same smooth action reconstruct the original mixed KG wave exactly. -/
theorem normal_polar_data (p : MassiveParameters) (hc : 1 < p.c) :
    ContDiff ℝ ∞ (fun y : Covector => Complex.normSq (curve p (y 0 / p.c))) ∧
      (∀ y : Covector, 0 < Complex.normSq (curve p (y 0 / p.c))) ∧
      actionField p (fun y => Complex.normSq (curve p (y 0 / p.c))) (normalAction p) =
        original p := by
  have hi : ContDiff ℝ ∞ (fun y : Covector => y 0 / p.c) := by fun_prop
  refine ⟨(PolarLocalInverse.contDiff_normSq ∞).comp ((contDiff_curve p).comp hi),
    ?_, normal_reconstruction p⟩
  intro y
  exact Complex.normSq_pos.mpr (Complex.slitPlane_ne_zero
    (curve_mem_slitPlane p hc (y 0 / p.c)))

end FoliationQM.MixedRestPhase
