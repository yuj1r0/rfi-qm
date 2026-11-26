module

public import FoliationQM.ScalarPhaseCurrent
public import FoliationQM.RelativeAction
public import FoliationQM.DressedMassDensityVariation
public import Mathlib.Analysis.Complex.Circle

/-!
# Localizing the scalar Klein–Gordon phase symmetry

For v13 `eq:noether_current`, multiply the original scalar field by
exp(i t b(x)) and differentiate its true spacetime jets. For constant b
this is the global circle symmetry of the massive action density. For
variable b the linear coefficient pairs the physical current with db.
The exact quadratic correction contains the Minkowski square of db.
-/

@[expose] public section
noncomputable section
open scoped ComplexConjugate
namespace FoliationQM.ScalarNoetherSymmetry
open ActionDensity DressedMassDensityVariation Madelung

/-- A localized U(1) rotation of the original field by the dimensionless real angle t b(x). -/
def rotate (b : Covector → ℝ) (ψ : Covector → ℂ) (t : ℝ) (x : Covector) : ℂ :=
  phase (t * b x) * ψ x

/-- The unperturbed member of the local phase family is the original field. -/
theorem rotate_zero (b : Covector → ℝ) (ψ : Covector → ℂ) : rotate b ψ 0 = ψ := by
  funext x
  simp [rotate, phase]

/-- The family leaves the field fixed off the support of the real test. -/
theorem rotate_of_eq_zero {b : Covector → ℝ} (ψ : Covector → ℂ) (t : ℝ) {x : Covector}
    (hb : b x = 0) : rotate b ψ t x = ψ x := by simp [rotate, hb, phase]

private theorem phase_normSq (a : ℝ) : Complex.normSq (phase a) = 1 := by
  simp only [phase, Complex.normSq_apply, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
  nlinarith [Real.sin_sq_add_cos_sq a]

private theorem jetDensity_real (p : MassiveParameters) (z : ℂ) (dz : Fin 4 → ℂ) :
    kgDensity p z dz =
      ((p.hbar ^ 2 * realKinetic dz - p.m ^ 2 * p.c ^ 2 * Complex.normSq z : ℝ) : ℂ) := by
  rw [kgDensity, complexKinetic_eq_realKinetic, ← Complex.normSq_eq_conj_mul_self]
  push_cast
  rfl

private theorem jetDensity_unit (p : MassiveParameters) (z u : ℂ) (dz : Fin 4 → ℂ)
    (hu : Complex.normSq u = 1) :
    kgDensity p (u * z) (fun i => u * dz i) = kgDensity p z dz := by
  simp [jetDensity_real, realKinetic, Complex.normSq_mul, hu]

/-- The literal massive density with derivatives of the field and its conjugate is invariant
under every global U(1) rotation, at nodes as well as at nonzero values. -/
theorem global_invariance (p : MassiveParameters) (u : Circle) {ψ : Covector → ℂ} {x : Covector}
    (hψ : DifferentiableAt ℝ ψ x) :
    fieldDensity p (fun y => (u : ℂ) * ψ y) x coordinateVector = fieldDensity p ψ x coordinateVector := by
  have hd := hψ.hasFDerivAt.const_mul (u : ℂ)
  rw [fieldDensity_eq_kgDensity p hd.differentiableAt, fieldDensity_eq_kgDensity p hψ, hd.fderiv]
  apply jetDensity_unit
  simp [Complex.normSq_eq_norm_sq]

private theorem phaseFactor_deriv {b : Covector → ℝ} {x : Covector} (hb : DifferentiableAt ℝ b x)
    (t : ℝ) : HasFDerivAt (fun y => phase (t * b y))
      (phase (t*b x) • (Complex.I • (Complex.ofRealCLM.comp (t • fderiv ℝ b x)))) x := by
  have hc := Complex.ofRealCLM.hasFDerivAt.comp x (hb.hasFDerivAt.const_mul t)
  exact (hc.mul_const Complex.I).cexp

/-- Spatial differentiability of the genuinely phase-rotated field. -/
theorem differentiableAt_rotate {ψ : Covector → ℂ} {b : Covector → ℝ} {x : Covector}
    (hψ : DifferentiableAt ℝ ψ x) (hb : DifferentiableAt ℝ b x) (t : ℝ) :
    DifferentiableAt ℝ (rotate b ψ t) x := (phaseFactor_deriv hb t).differentiableAt.mul hψ

/-- The true derivative of the local rotation contains the derivative of the test angle. -/
theorem fderiv_rotate {ψ : Covector → ℂ} {b : Covector → ℝ} {x : Covector}
    (hψ : DifferentiableAt ℝ ψ x) (hb : DifferentiableAt ℝ b x) (t : ℝ) (v : Covector) :
    fderiv ℝ (rotate b ψ t) x v =
      phase (t*b x) * (fderiv ℝ ψ x v + Complex.I * (t : ℂ) * (fderiv ℝ b x v : ℂ) * ψ x) := by
  have hd := (phaseFactor_deriv hb t).fun_mul hψ.hasFDerivAt
  unfold rotate
  rw [hd.fderiv]
  simp [add_apply, smul_apply]
  ring

private theorem jet_square (z dz : ℂ) (t b : ℝ) :
    Complex.normSq (dz + Complex.I * (t : ℂ) * (b : ℂ) * z) =
      Complex.normSq dz + 2 * t * b * (conj z * dz).im + t^2 * b^2 * Complex.normSq z := by
  simp [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  ring

/-- Coefficient of the local phase test in the massive density, expressed through the
source current and the inverse Minkowski pairing of lower covectors. -/
def linear (p : MassiveParameters) (b : Covector → ℝ) (ψ : Covector → ℂ) (x : Covector) : ℝ :=
  -2 * p.m * p.hbar * minkowski (ScalarPhaseCurrent.current p ψ x) (phaseDifferential b x)

/-- The quadratic contribution of the local phase test. -/
def quadratic (p : MassiveParameters) (b : Covector → ℝ) (ψ : Covector → ℂ) (x : Covector) : ℝ :=
  p.hbar^2 * Complex.normSq (ψ x) * minkowski (phaseDifferential b x) (phaseDifferential b x)

/-- The physical Klein–Gordon density has this exact polynomial along a localized U(1) rotation. -/
theorem density_change (p : MassiveParameters) {ψ : Covector → ℂ} {b : Covector → ℝ} {x : Covector}
    (hψ : DifferentiableAt ℝ ψ x) (hb : DifferentiableAt ℝ b x) (t : ℝ) :
    (fieldDensity p (rotate b ψ t) x coordinateVector).re =
      (fieldDensity p ψ x coordinateVector).re + t * linear p b ψ x + t^2 * quadratic p b ψ x := by
  let d := fun i => fderiv ℝ ψ x (coordinateVector i)
  let v := phaseDifferential b x
  have hj (i : Fin 4) : fderiv ℝ (rotate b ψ t) x (coordinateVector i) =
      phase (t * b x) * (d i + Complex.I * (t : ℂ) * (v i : ℂ) * ψ x) := fderiv_rotate hψ hb t _
  rw [fieldDensity_eq_kgDensity p (differentiableAt_rotate hψ hb t), fieldDensity_eq_kgDensity p hψ]
  simp_rw [hj]
  rw [rotate, jetDensity_unit _ _ _ _ (phase_normSq _)]
  change (kgDensity p (ψ x) (fun i => d i + Complex.I * (t : ℂ) * (v i : ℂ) * ψ x)).re =
    (kgDensity p (ψ x) d).re + t * (-2 * p.m * p.hbar *
      minkowski (fun i => -(p.hbar / p.m) * (conj (ψ x) * d i).im) v) +
      t^2 * (p.hbar^2 * Complex.normSq (ψ x) * minkowski v v)
  simp only [jetDensity_real, Complex.ofReal_re, realKinetic, jet_square, minkowski]
  field_simp [p.m_pos.ne']
  ring

/-- The actual relative density of a locally rotated field requires only the two test
coefficients, including when the original field vanishes. -/
theorem relativeDensity_eq (p : MassiveParameters) {ψ : Covector → ℂ} {b : Covector → ℝ} {x : Covector}
    (hψ : DifferentiableAt ℝ ψ x) (hb : DifferentiableAt ℝ b x) (t : ℝ) :
    RelativeAction.relativeDensity p ψ (rotate b ψ t) coordinateVector x =
      t * linear p b ψ x + t^2 * quadratic p b ψ x := by
  rw [RelativeAction.relativeDensity, ActionVariation.fieldPairing_self_eq_fieldDensity p hψ,
    ActionVariation.fieldPairing_self_eq_fieldDensity p (differentiableAt_rotate hψ hb t), density_change p hψ hb]
  ring

/-- The first derivative at the original field is the normalized Noether pairing
−2mℏ η(j,db), without an equation-of-motion or nonvanishing hypothesis. -/
theorem hasDerivAt_density (p : MassiveParameters) {ψ : Covector → ℂ} {b : Covector → ℝ} {x : Covector}
    (hψ : DifferentiableAt ℝ ψ x) (hb : DifferentiableAt ℝ b x) :
    HasDerivAt (fun t => (fieldDensity p (rotate b ψ t) x coordinateVector).re) (linear p b ψ x) 0 := by
  simp_rw [density_change p hψ hb]
  simp only [pow_two]
  convert ((hasDerivAt_const (0 : ℝ) (fieldDensity p ψ x coordinateVector).re).add
    ((hasDerivAt_id (0 : ℝ)).mul_const (linear p b ψ x))).add
    (((hasDerivAt_id (0 : ℝ)).mul (hasDerivAt_id (0 : ℝ))).mul_const (quadratic p b ψ x)) using 1
  · ext s
    simp only [Pi.add_apply, Pi.mul_apply, id_eq]
  · simp

end FoliationQM.ScalarNoetherSymmetry
