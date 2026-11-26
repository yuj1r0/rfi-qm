module

public import FoliationQM.ChiralMatrix
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Actual derivatives of the chiral factor and positive amplitude

Sources: v13 `prop:takabayasi` and the differentiated polar ansatz in the
proof of `thm:dirac_lift`. The chiral parameter beta is the full source angle;
the generator therefore has coefficient i/2. We differentiate the actual
sine-cosine matrix, identify the genuine matrix-exponential derivative, and
apply the actual Frechet chain rule over an arbitrary real normed domain.
The inverse factor is the actual nonsingular matrix inverse.

Matrix calculus uses the same `Matrix.Norms.Operator` normed-algebra scope
as the other analytic rotor modules. Square-root and logarithmic amplitude
formulas require positive density at the point. Their derivatives and the
half-logarithmic amplitude coefficient are derived rather than postulated.
-/

@[expose] public section
noncomputable section
open scoped Matrix.Norms.Operator

namespace FoliationQM.ChiralDifferential
open DiracMatrices ChiralMatrix

/-- The actual real derivative of the full-angle chiral matrix is i/2 times gamma5 times that matrix. -/
theorem hasDerivAt_chiral (beta : ℝ) :
    HasDerivAt chiral ((Complex.I / 2 : ℂ) • (gamma5 * chiral beta)) beta := by
  have hhalf : HasDerivAt (fun t : ℝ => t / 2) (1 / 2) beta :=
    (hasDerivAt_id beta).div_const 2
  have hc := ((Real.hasDerivAt_cos (beta / 2)).comp beta hhalf).ofReal_comp.smul_const (1 : Mat)
  have hs := (((Real.hasDerivAt_sin (beta / 2)).comp beta hhalf).ofReal_comp.const_mul Complex.I).smul_const gamma5
  have hd : HasDerivAt chiral
      ((-(Real.sin (beta / 2) : ℂ) / 2) • (1 : Mat) +
        (Complex.I * (Real.cos (beta / 2) : ℂ) / 2) • gamma5) beta := by
    simpa only [chiral, Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_div,
      Complex.ofReal_one, Complex.ofReal_ofNat, mul_one_div, mul_div_assoc] using! hc.add hs
  convert hd using 1
  simp only [chiral, mul_add, mul_smul_comm, mul_one, gamma5_sq, smul_add, smul_smul]
  match_scalars <;> ring_nf
  norm_num

/-- The actual chiral derivative also has the commuting right-gamma5 form. -/
theorem hasDerivAt_chiral_right (beta : ℝ) :
    HasDerivAt chiral ((Complex.I / 2 : ℂ) • (chiral beta * gamma5)) beta := by
  simpa only [(chiral_gamma5_commute beta).eq] using hasDerivAt_chiral beta

/-- The actual chiral derivative is left multiplication by the constant generator (i/2) gamma5. -/
theorem hasDerivAt_chiral_left_mul (beta : ℝ) :
    HasDerivAt chiral (((Complex.I / 2 : ℂ) • gamma5) * chiral beta) beta := by
  simpa only [smul_mul_assoc] using hasDerivAt_chiral beta

/-- The actual scalar-domain Frechet derivative of the chiral matrix is the continuous linear map multiplying the real increment by its generator derivative. -/
theorem hasFDerivAt_chiral (beta : ℝ) :
    HasFDerivAt chiral ((ContinuousLinearMap.id ℝ ℝ).smulRight
      ((Complex.I / 2 : ℂ) • (gamma5 * chiral beta))) beta := by
  simpa using! (hasDerivAt_chiral beta).hasFDerivAt

/-- The genuine normed-algebra matrix exponential has the actual chiral generator derivative along the real full-angle parameter. -/
theorem hasDerivAt_exp_chiral (beta : ℝ) :
    HasDerivAt (fun t : ℝ => NormedSpace.exp ((Complex.I * (t : ℂ) / 2) • gamma5))
      (((Complex.I / 2 : ℂ) • gamma5) *
        NormedSpace.exp ((Complex.I * (beta : ℂ) / 2) • gamma5)) beta := by
  simpa only [exp_chiral] using hasDerivAt_chiral_left_mul beta

/-- Mathlib's actual real derivative of the chiral matrix equals its proved generator formula. -/
theorem deriv_chiral (beta : ℝ) :
    deriv chiral beta = (Complex.I / 2 : ℂ) • (gamma5 * chiral beta) :=
  (hasDerivAt_chiral beta).deriv

/-- The actual full-angle chiral matrix is real differentiable everywhere. -/
theorem differentiable_chiral : Differentiable ℝ chiral :=
  fun beta => (hasDerivAt_chiral beta).differentiableAt

/-- The actual full-angle chiral matrix is smooth to every differentiability order. -/
theorem contDiff_chiral (n : WithTop ℕ∞) : ContDiff ℝ n chiral := by
  have hh : ContDiff ℝ n (fun beta : ℝ => beta / 2) := contDiff_id.div_const 2
  have hc : ContDiff ℝ n (fun beta : ℝ => (Real.cos (beta / 2) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (Real.contDiff_cos.comp hh)
  have hs : ContDiff ℝ n (fun beta : ℝ => (Real.sin (beta / 2) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (Real.contDiff_sin.comp hh)
  exact (hc.smul contDiff_const).add ((contDiff_const.mul hs).smul contDiff_const)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- An actual scalar Frechet derivative gives the actual matrix-valued chiral chain rule on any real normed domain. -/
theorem hasFDerivAt_chiral_comp {beta : E → ℝ} {beta' : E →L[ℝ] ℝ} {x : E}
    (hbeta : HasFDerivAt beta beta' x) :
    HasFDerivAt (fun y => chiral (beta y))
      (beta'.smulRight ((Complex.I / 2 : ℂ) • (gamma5 * chiral (beta x)))) x := by
  have h := (hasDerivAt_chiral (beta x)).hasFDerivAt.comp x hbeta
  convert! h using 1

/-- Every directional evaluation of the actual chiral Frechet derivative is i times the angle derivative divided by two, multiplying gamma5 times the chiral factor. -/
theorem fderiv_chiral_comp_apply {beta : E → ℝ} {x : E}
    (hbeta : DifferentiableAt ℝ beta x) (v : E) :
    fderiv ℝ (fun y => chiral (beta y)) x v =
      (Complex.I * (fderiv ℝ beta x v : ℂ) / 2) • (gamma5 * chiral (beta x)) := by
  rw [(hasFDerivAt_chiral_comp hbeta.hasFDerivAt).fderiv]
  simp only [ContinuousLinearMap.smulRight_apply]
  rw [← IsScalarTower.algebraMap_smul ℂ (fderiv ℝ beta x v)
    ((Complex.I / 2 : ℂ) • (gamma5 * chiral (beta x))), smul_smul]
  congr 1
  change (fderiv ℝ beta x v : ℂ) * (Complex.I / 2) = _
  ring

/-- The actual inverse chiral factor has the Frechet chain rule with the negated angle derivative. -/
theorem hasFDerivAt_chiral_inverse_comp {beta : E → ℝ} {beta' : E →L[ℝ] ℝ} {x : E}
    (hbeta : HasFDerivAt beta beta' x) :
    HasFDerivAt (fun y => (chiral (beta y))⁻¹)
      ((-beta').smulRight ((Complex.I / 2 : ℂ) • (gamma5 * (chiral (beta x))⁻¹))) x := by
  simpa only [chiral_inv, Pi.neg_apply] using! hasFDerivAt_chiral_comp hbeta.neg

/-- Every directional derivative of the actual inverse chiral factor has the negative i/2 generator coefficient. -/
theorem fderiv_chiral_inverse_comp_apply {beta : E → ℝ} {x : E}
    (hbeta : DifferentiableAt ℝ beta x) (v : E) :
    fderiv ℝ (fun y => (chiral (beta y))⁻¹) x v =
      (-Complex.I * (fderiv ℝ beta x v : ℂ) / 2) • (gamma5 * (chiral (beta x))⁻¹) := by
  rw [(hasFDerivAt_chiral_inverse_comp hbeta.hasFDerivAt).fderiv]
  simp only [ContinuousLinearMap.smulRight_apply, neg_apply]
  rw [← IsScalarTower.algebraMap_smul ℂ (-fderiv ℝ beta x v)
    ((Complex.I / 2 : ℂ) • (gamma5 * (chiral (beta x))⁻¹)), smul_smul]
  congr 1
  change ((-fderiv ℝ beta x v : ℝ) : ℂ) * (Complex.I / 2) = _
  push_cast
  ring


/-- The actual nonsingular inverse chiral factor has real derivative minus i/2 times gamma5 times that inverse. -/
theorem hasDerivAt_chiral_inverse (beta : ℝ) :
    HasDerivAt (fun t : ℝ => (chiral t)⁻¹)
      ((-Complex.I / 2 : ℂ) • (gamma5 * (chiral beta)⁻¹)) beta := by
  have h := (hasFDerivAt_chiral_inverse_comp (hasFDerivAt_id beta)).hasDerivAt
  simpa only [ContinuousLinearMap.smulRight_apply, neg_apply,
    ContinuousLinearMap.id_apply, neg_smul, one_smul, neg_div, neg_smul] using! h

/-- The actual inverse chiral factor is smooth to every real differentiability order. -/
theorem contDiff_chiral_inverse (n : WithTop ℕ∞) :
    ContDiff ℝ n (fun beta : ℝ => (chiral beta)⁻¹) := by
  simpa only [chiral_inv, Function.comp_def, id_eq] using! (contDiff_chiral n).comp contDiff_id.neg

/-- Positive density and an actual density derivative give the actual square-root amplitude Frechet derivative. -/
theorem hasFDerivAt_sqrt {rho : E → ℝ} {rho' : E →L[ℝ] ℝ} {x : E}
    (hrho : HasFDerivAt rho rho' x) (hpos : 0 < rho x) :
    HasFDerivAt (fun y => Real.sqrt (rho y)) ((1 / (2 * Real.sqrt (rho x))) • rho') x :=
  hrho.sqrt hpos.ne'

/-- Positive density and an actual density derivative give the actual logarithmic density Frechet derivative. -/
theorem hasFDerivAt_log {rho : E → ℝ} {rho' : E →L[ℝ] ℝ} {x : E}
    (hrho : HasFDerivAt rho rho' x) (hpos : 0 < rho x) :
    HasFDerivAt (fun y => Real.log (rho y)) ((rho x)⁻¹ • rho') x :=
  hrho.log hpos.ne'

/-- The actual directional square-root amplitude derivative is the density derivative divided by twice its positive square root. -/
theorem fderiv_sqrt_apply {rho : E → ℝ} {x : E}
    (hrho : DifferentiableAt ℝ rho x) (hpos : 0 < rho x) (v : E) :
    fderiv ℝ (fun y => Real.sqrt (rho y)) x v =
      fderiv ℝ rho x v / (2 * Real.sqrt (rho x)) := by
  rw [(hasFDerivAt_sqrt hrho.hasFDerivAt hpos).fderiv]
  simp [div_eq_mul_inv, mul_comm]

/-- The actual directional log-density derivative is the density derivative divided by the positive density. -/
theorem fderiv_log_apply {rho : E → ℝ} {x : E}
    (hrho : DifferentiableAt ℝ rho x) (hpos : 0 < rho x) (v : E) :
    fderiv ℝ (fun y => Real.log (rho y)) x v = fderiv ℝ rho x v / rho x := by
  rw [(hasFDerivAt_log hrho.hasFDerivAt hpos).fderiv]
  simp [div_eq_mul_inv, mul_comm]

/-- For positive density, the square-root derivative coefficient equals half the logarithmic coefficient times the amplitude. -/
theorem sqrt_coefficient_eq_half_log {rho : ℝ} (hpos : 0 < rho) (d : ℝ) :
    d / (2 * Real.sqrt rho) = (d / rho / 2) * Real.sqrt rho := by
  have hs := Real.mul_self_sqrt hpos.le
  have hm := congrArg (fun t : ℝ => d * t) hs
  field_simp [hpos.ne', (Real.sqrt_pos.mpr hpos).ne']
  nlinarith [hm]

/-- The actual amplitude derivative is one half of the actual log-density derivative times the positive square-root amplitude. -/
theorem fderiv_sqrt_eq_half_log_mul {rho : E → ℝ} {x : E}
    (hrho : DifferentiableAt ℝ rho x) (hpos : 0 < rho x) (v : E) :
    fderiv ℝ (fun y => Real.sqrt (rho y)) x v =
      (fderiv ℝ (fun y => Real.log (rho y)) x v / 2) * Real.sqrt (rho x) := by
  rw [fderiv_sqrt_apply hrho hpos, fderiv_log_apply hrho hpos]
  exact sqrt_coefficient_eq_half_log hpos _

end FoliationQM.ChiralDifferential
