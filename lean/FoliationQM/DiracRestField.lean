module
public import FoliationQM.DiracEquation
public import FoliationQM.SpinorRegularity
public import FoliationQM.RestPlaneWave

/-!
# Regular flat rest solution of the Dirac equation

For v13 `thm:dirac_lift`, the unit-amplitude rest spinor carries the
phase of the action −mc x⁰. Its genuine four coordinate derivatives
give a zero Dirac residual when ℏ is nonzero. Its scalar and pseudoscalar
invariants yield invariant density one throughout spacetime.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.DiracRestField
open DiracMatrices DiracAdjoint DiracFieldDensity DiracEquation SpinorRegularity

/-- Unit complex phase for a flat rest wave, in the coordinate convention x⁰ = ct. -/
def wave (hbar c m : ℝ) (x : Covector) : ℂ := phase (-(m * c / hbar) * x 0)

/-- The actual rest-plane spinor field. -/
def field (hbar c m : ℝ) (x : Covector) : Spinor := wave hbar c m x • restSpinor

/-- With positive massive parameters, this scalar phase agrees with the existing rest plane wave. -/
theorem wave_eq_restWave (p : MassiveParameters) (x : Covector) :
    wave p.hbar p.c p.m x = RestPlaneWave.restWave p x := by
  change phase _ = (Real.sqrt (1 : ℝ) : ℂ) * phase (-(p.m * p.c) * x 0 / p.hbar)
  rw [Real.sqrt_one, Complex.ofReal_one, one_mul]
  congr 1
  ring

variable (hbar c m : ℝ)

/-- The phase field is smooth to every differentiability order. -/
theorem contDiff_wave (n : WithTop ℕ∞) : ContDiff ℝ n (wave hbar c m) := by
  have hθ : ContDiff ℝ n (fun x : Covector => -(m * c / hbar) * x 0) :=
    contDiff_const.mul (contDiff_apply ℝ (fun _ : Fin 4 => ℝ) 0)
  exact ((Complex.ofRealCLM.contDiff.comp hθ).mul (contDiff_const (c := Complex.I))).cexp

/-- The actual spinor field is smooth at every order. -/
theorem contDiff_field (n : WithTop ℕ∞) : ContDiff ℝ n (field hbar c m) :=
  (contDiff_wave hbar c m n).smul contDiff_const

/-- Differentiating the actual complex exponential only uses the time coordinate of a direction. -/
theorem fderiv_wave_apply (x v : Covector) : fderiv ℝ (wave hbar c m) x v =
    ((-(m * c / hbar) * v 0 : ℝ) : ℂ) * Complex.I * wave hbar c m x := by
  let a := -(m * c / hbar)
  have hθ : HasFDerivAt (fun y : Covector => a * y 0)
      (a • (ContinuousLinearMap.proj (0 : Fin 4) : Covector →L[ℝ] ℝ)) x :=
    (hasFDerivAt_apply 0 x).const_mul a
  have he := ((Complex.ofRealCLM.hasFDerivAt.comp x hθ).mul_const Complex.I).cexp
  simp only [Function.comp_apply, Complex.ofRealCLM_apply] at he
  change fderiv ℝ (fun y : Covector => Complex.exp ((a * y 0 : ℝ) * Complex.I)) x v = _
  rw [he.fderiv]
  simp only [wave, phase, smul_apply, ContinuousLinearMap.comp_apply,
    Complex.ofRealCLM_apply, ContinuousLinearMap.proj_apply, smul_eq_mul]
  ring

/-- All first jets of the spinor are derivatives of the original phase times the rest spinor. -/
theorem fderiv_field_apply (x v : Covector) : fderiv ℝ (field hbar c m) x v =
    (((-(m * c / hbar) * v 0 : ℝ) : ℂ) * Complex.I * wave hbar c m x) • restSpinor := by
  have h := ((contDiff_wave hbar c m 1).differentiable (by norm_num) x).hasFDerivAt.smul_const restSpinor
  change fderiv ℝ (fun y => wave hbar c m y • restSpinor) x v = _
  rw [h.fderiv, ContinuousLinearMap.smulRight_apply, fderiv_wave_apply]

/-- The spatial momentum vanishes; the time matrix fixes the constant rest spinor. -/
theorem slash_field (x : Covector) : slashField (field hbar c m) x =
    (((-(m * c / hbar) : ℝ) : ℂ) * Complex.I * wave hbar c m x) • restSpinor := by
  unfold slashField slashJet
  simp_rw [fderiv_field_apply]
  rw [Finset.sum_eq_single (0 : Fin 4)]
  · rw [Matrix.mulVec_smul, gamma_zero_mulVec_restSpinor]
    simp [coordinateDirections]
  · intro μ _ hμ
    simp [coordinateDirections, Ne.symm hμ]
  · simp

/-- The genuine flat Dirac residual vanishes pointwise for every nonzero ℏ. -/
theorem diracField_zero (hhbar : hbar ≠ 0) (x : Covector) :
    diracField hbar m c (field hbar c m) x = 0 := by
  change (Complex.I * (hbar : ℂ)) • slashField (field hbar c m) x -
    ((m * c : ℝ) : ℂ) • field hbar c m x = 0
  rw [sub_eq_zero, slash_field, field, smul_smul, smul_smul]
  congr 1
  calc
    _ = ((-(m * c / hbar) : ℝ) : ℂ) * (hbar : ℂ) * (Complex.I * Complex.I) * wave hbar c m x := by ring
    _ = _ := by
      rw [Complex.I_mul_I]
      push_cast
      field_simp [Complex.ofReal_ne_zero.mpr hhbar]

/-- The squared complex modulus of the rest phase is one for arbitrary real parameters. -/
theorem wave_normSq (x : Covector) : Complex.normSq (wave hbar c m x) = 1 := by
  simp only [wave, phase, Complex.normSq_apply, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
  nlinarith [Real.sin_sq_add_cos_sq (-(m * c / hbar) * x 0)]

/-- The two invariant scalar contractions of the rest field are 1 and 0. -/
theorem scalar_pseudoscalar (x : Covector) :
    scalar (field hbar c m x) = 1 ∧ pseudoscalar (field hbar c m x) = 0 := by
  have hs : star (wave hbar c m x) * wave hbar c m x = 1 := by
    rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, wave_normSq, Complex.ofReal_one]
  have hss : wave hbar c m x * star (wave hbar c m x) = 1 := (mul_comm _ _).trans hs
  simp only [field, scalar, pseudoscalar, bilinear_smul_left, bilinear_smul_right,
    rest_scalar, rest_pseudoscalar, mul_one, mul_zero, hss, Complex.one_re, Complex.zero_re, and_self]

/-- The rest solution has invariant density exactly one on the full spacetime domain. -/
theorem invariantDensity_one (x : Covector) : invariantDensity (field hbar c m x) = 1 := by
  rw [invariantDensity, (scalar_pseudoscalar hbar c m x).1, (scalar_pseudoscalar hbar c m x).2]
  norm_num

/-- The rest field is strictly regular everywhere. -/
theorem regular (x : Covector) : Regular (field hbar c m x) := by
  change 0 < invariantDensity _
  rw [invariantDensity_one]
  norm_num

end FoliationQM.DiracRestField
