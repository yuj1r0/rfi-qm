module

public import FoliationQM.RestPlaneWave
public import FoliationQM.RestEnvelopeKG

/-!
# A concrete mixture of the two rest-frequency branches

Source: v13 `cor:schrodinger`, components C and D. This spatially constant
mixed-frequency Klein–Gordon solution has a small envelope perturbation,
but its actual time derivatives retain a finite scaled second derivative.
All derivatives and the original KG equation belong to the same explicit
field. No slow-phase or limiting-equation assumption is used here.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.MixedRestMode

open PolarSecondDifferential
open Madelung (coordinateVector)
open scoped ContDiff ComplexConjugate

/-- The actual rest-removed time curve, including its small opposite branch. -/
def curve (p : MassiveParameters) (t : ℝ) : ℂ :=
  1 + (((p.c ^ 2)⁻¹ : ℝ) : ℂ) * phase (2 * p.omega0 * t)

/-- The spatially constant envelope in physical-time coordinates. -/
def field (p : MassiveParameters) (x : Covector) : ℂ := curve p (x 0)

/-- The original wave in normal coordinates, as a real-linear branch mixture. -/
def original (p : MassiveParameters) (y : Covector) : ℂ :=
  RestPlaneWave.restWave p y + (((p.c ^ 2)⁻¹ : ℝ) : ℂ) * conj (RestPlaneWave.restWave p y)

/-- The explicit envelope curve is smooth to every order. -/
theorem contDiff_curve (p : MassiveParameters) : ContDiff ℝ ∞ (curve p) := by
  have hθ : ContDiff ℝ ∞ (fun t : ℝ => 2 * p.omega0 * t) :=
    contDiff_const.mul contDiff_id
  exact contDiff_const.add (contDiff_const.mul
    (((Complex.ofRealCLM.contDiff.comp hθ).mul contDiff_const).cexp))

/-- The same envelope is genuinely smooth on spacetime. -/
theorem contDiff_field (p : MassiveParameters) : ContDiff ℝ ∞ (field p) :=
  (contDiff_curve p).comp (contDiff_apply ℝ (fun _ : Fin 4 => ℝ) 0)

/-- The original mixed wave is smooth in its actual normal coordinates. -/
theorem contDiff_original (p : MassiveParameters) : ContDiff ℝ ∞ (original p) := by
  exact (RestPlaneWave.contDiff_restWave p ∞).add (contDiff_const.mul
    (Complex.conjCLE.contDiff.comp (RestPlaneWave.contDiff_restWave p ∞)))

private theorem phase_derivative (p : MassiveParameters) (t : ℝ) :
    HasDerivAt (fun s : ℝ => phase (2 * p.omega0 * s))
      (phase (2 * p.omega0 * t) * ((2 * p.omega0 : ℝ) : ℂ) * Complex.I) t := by
  have h := ((hasDerivAt_id t).const_mul (2 * p.omega0)).ofReal_comp.mul_const Complex.I
  simpa only [phase, id_eq, mul_one, mul_assoc] using h.cexp

/-- The actual first derivative has constant nonvanishing amplitude. -/
theorem hasDerivAt_curve (p : MassiveParameters) (t : ℝ) :
    HasDerivAt (curve p)
      ((2 * Complex.I * (p.m / p.hbar : ℂ)) * phase (2 * p.omega0 * t)) t := by
  have hd := ((phase_derivative p t).const_mul (((p.c ^ 2)⁻¹ : ℝ) : ℂ)).const_add 1
  change HasDerivAt (curve p) _ t at hd
  apply hd.congr_deriv
  have hc : (p.c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr p.c_pos.ne'
  simp only [MassiveParameters.omega0]
  push_cast
  field_simp

/-- Differentiating the first derivative as a function gives the actual second derivative. -/
theorem hasDerivAt_deriv_curve (p : MassiveParameters) (t : ℝ) :
    HasDerivAt (deriv (curve p))
      ((-(4 * p.m ^ 2 * p.c ^ 2 / p.hbar ^ 2 : ℝ) : ℂ) *
        phase (2 * p.omega0 * t)) t := by
  have heq : deriv (curve p) = fun s =>
      (2 * Complex.I * (p.m / p.hbar : ℂ)) * phase (2 * p.omega0 * s) :=
    funext fun s => (hasDerivAt_curve p s).deriv
  rw [heq]
  apply ((phase_derivative p t).const_mul (2 * Complex.I * (p.m / p.hbar : ℂ))).congr_deriv
  simp only [MassiveParameters.omega0]
  push_cast
  ring_nf
  simp only [Complex.I_sq]
  ring

/-- The genuine spacetime jets are the time-curve jets times the actual zeroth direction component. -/
theorem field_derivatives (p : MassiveParameters) (x v : Covector) :
    directionalDerivative (field p) v x = (v 0 : ℂ) * deriv (curve p) (x 0) ∧
      secondDirectionalDerivative (field p) v x =
        (v 0 : ℂ) ^ 2 * deriv (deriv (curve p)) (x 0) := by
  have hfirst (y : Covector) : directionalDerivative (field p) v y =
      (v 0 : ℂ) * deriv (curve p) (y 0) := by
    have hproj : HasFDerivAt (fun z : Covector => z 0)
        (ContinuousLinearMap.proj (0 : Fin 4) : Covector →L[ℝ] ℝ) y :=
      hasFDerivAt_apply 0 y
    have hd := (hasDerivAt_curve p (y 0)).hasFDerivAt.comp y hproj
    change HasFDerivAt (field p) _ y at hd
    change fderiv ℝ (field p) y v = _
    rw [hd.fderiv, (hasDerivAt_curve p (y 0)).deriv]
    simp [ContinuousLinearMap.comp_apply, Complex.real_smul]
  refine ⟨hfirst x, ?_⟩
  have heq := funext hfirst
  have hproj : HasFDerivAt (fun z : Covector => z 0)
      (ContinuousLinearMap.proj (0 : Fin 4) : Covector →L[ℝ] ℝ) x :=
    hasFDerivAt_apply 0 x
  have hd := ((hasDerivAt_deriv_curve p (x 0)).hasFDerivAt.comp x hproj).const_mul (v 0 : ℂ)
  change HasFDerivAt (fun y : Covector => (v 0 : ℂ) * deriv (curve p) (y 0)) _ x at hd
  change fderiv ℝ (directionalDerivative (field p) v) x v = _
  rw [heq, hd.fderiv, (hasDerivAt_deriv_curve p (x 0)).deriv]
  simp only [smul_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply,
    ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul, Complex.real_smul]
  ring

private theorem directional_linear (T : ℂ →L[ℝ] ℂ) {f : Covector → ℂ}
    (v x : Covector) (hf : DifferentiableAt ℝ f x) :
    directionalDerivative (fun y => T (f y)) v x = T (directionalDerivative f v x) := by
  have hd := T.hasFDerivAt.comp x hf.hasFDerivAt
  change fderiv ℝ (T ∘ f) x v = _
  rw [hd.fderiv]
  rfl

private theorem second_linear (T : ℂ →L[ℝ] ℂ) {f : Covector → ℂ}
    (v x : Covector) (hf : ContDiff ℝ 2 f) :
    secondDirectionalDerivative (fun y => T (f y)) v x =
      T (secondDirectionalDerivative f v x) := by
  unfold secondDirectionalDerivative
  rw [show directionalDerivative (fun y => T (f y)) v =
    fun y => T (directionalDerivative f v y) from
    funext fun y => directional_linear T v y (hf.differentiable (by norm_num) y)]
  exact directional_linear T v x
    (PolarRegularity.differentiableAt_directionalDerivative_of_contDiffAt_two hf.contDiffAt v)

/-- The actual dimensional Klein–Gordon operator vanishes on the original mixed wave. -/
theorem original_kg (p : MassiveParameters) (y : Covector) :
    FlatIntegrationByParts.kgOperator p (original p) coordinateVector y = 0 := by
  let T : ℂ →L[ℝ] ℂ := ContinuousLinearMap.id ℝ ℂ +
    (p.c ^ 2)⁻¹ • Complex.conjCLE.toContinuousLinearMap
  have heq : original p = fun x => T (RestPlaneWave.restWave p x) := by
    funext x
    simp [original, T, Complex.real_smul]
  apply (StationaryAction.kgOperator_eq_zero_iff p _ _ _).2
  rw [heq]
  have hb : box (fun x => T (RestPlaneWave.restWave p x)) coordinateVector y =
      T (box (RestPlaneWave.restWave p) coordinateVector y) := by
    simp only [box, second_linear T _ y (RestPlaneWave.contDiff_restWave p 2), ← map_sub]
  have hk := congrArg T (RestPlaneWave.restWave_kg p y)
  have hm (z : ℂ) : T (((p.m ^ 2 * p.c ^ 2 / p.hbar ^ 2 : ℝ) : ℂ) * z) =
      (((p.m ^ 2 * p.c ^ 2 / p.hbar ^ 2 : ℝ) : ℂ) * T z) := by
    simpa only [Complex.real_smul] using T.map_smul (p.m ^ 2 * p.c ^ 2 / p.hbar ^ 2) z
  rw [hb, ← hm, ← map_add, hk, map_zero]

/-- Removing the actual rest carrier reconstructs this same envelope as a function. -/
theorem envelope_original (p : MassiveParameters) :
    RestEnvelopeKG.envelope p (original p) = field p := by
  funext x
  have hw : RestPlaneWave.restWave p (LaboratoryCoordinates.toNormal p.c x) =
      RestEnvelopeDifferential.carrierField p x := by
    simp only [RestPlaneWave.restWave, ActionDensity.actionField, PolarDifferential.polarField,
      RestPlaneWave.restAction, Real.sqrt_one, Complex.ofReal_one, one_mul,
      RestEnvelopeDifferential.carrierField, RestPhaseDerivatives.carrier]
    congr 1
    simp only [LaboratoryCoordinates.toNormal_apply, ite_true, MassiveParameters.omega0]
    ring
  simp only [RestEnvelopeKG.envelope, LaboratoryCoordinates.pullback, original, hw,
    field, curve]
  rw [mul_add, inv_mul_cancel₀ (RestEnvelopeDifferential.carrierField_ne_zero p x)]
  congr 1
  simp only [RestEnvelopeDifferential.carrierField, RestPhaseDerivatives.carrier, phase]
  rw [← Complex.exp_neg, ← Complex.exp_conj]
  calc
    _ = (((p.c ^ 2)⁻¹ : ℝ) : ℂ) *
        (Complex.exp (-(((-p.omega0 * x 0 : ℝ) : ℂ) * Complex.I)) *
          Complex.exp (conj (((-p.omega0 * x 0 : ℝ) : ℂ) * Complex.I))) := by ring
    _ = _ := by
      rw [← Complex.exp_add]
      congr 2
      simp
      ring

/-- Exact norms quantify the small field perturbation and its actual first and second derivatives. -/
theorem curve_norms (p : MassiveParameters) (t : ℝ) :
    ‖curve p t - 1‖ = (p.c ^ 2)⁻¹ ∧
      ‖deriv (curve p) t‖ = 2 * p.m / p.hbar ∧
      ‖deriv (deriv (curve p)) t‖ = 4 * p.m ^ 2 * p.c ^ 2 / p.hbar ^ 2 := by
  have hn : ‖phase (2 * p.omega0 * t)‖ = 1 := by
    simp only [phase, Complex.norm_exp_ofReal_mul_I]
  refine ⟨?_, ?_, ?_⟩
  · simp only [curve, add_sub_cancel_left, norm_mul, hn, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_inv, abs_pow, abs_of_pos p.c_pos]
  · rw [(hasDerivAt_curve p t).deriv]
    simp only [norm_mul, Complex.norm_I, mul_one, hn, norm_div, Complex.norm_real,
      Real.norm_eq_abs, Complex.norm_two, abs_of_pos p.m_pos, abs_of_pos p.hbar_pos]
    ring
  · rw [(hasDerivAt_deriv_curve p t).deriv]
    simp only [norm_mul, hn, mul_one, norm_neg, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (show 0 ≤ 4 * p.m ^ 2 * p.c ^ 2 / p.hbar ^ 2 by positivity)]

end FoliationQM.MixedRestMode
