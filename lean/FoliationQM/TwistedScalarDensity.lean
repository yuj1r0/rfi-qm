module
public import FoliationQM.TwistedScalarField
public import FoliationQM.ScalarRestKinetic
public import FoliationQM.ScalarSpinDefect

/-!
# The actual massive spinor density on a chiral scalar family

For v13 `eq:spinor_quadratic_exact` and `thm:dirac_lift`, evaluate the
neutralized contraction on a chiral rotation of an arbitrary complex
field in the rest-spinor line. Its difference from the scalar density
is the Lorentzian square of the angle gradient times the squared scalar
modulus, with factor −ℏ²/4.
-/

@[expose] public section
noncomputable section
open scoped Matrix.Norms.Operator
namespace FoliationQM.TwistedScalarDensity
open DiracMatrices DiracFieldDensity RealLorentzFrame ScalarSpinDefect NeutralizedSpinorKinetic
open TwistedScalarJet TwistedScalarField

/-- The chiral gradient term per unit scalar modulus squared. -/
def potential (p : MassiveParameters) (β : Covector → ℝ) (x : Covector) : ℝ :=
  p.hbar ^ 2 / 4 * minkowski (gradient β x) (gradient β x)

/-- The massive action density of the actual chiral scalar field. -/
def density (p : MassiveParameters) (β : Covector → ℝ) (z : Covector → ℂ) (x : Covector) : ℝ :=
  MassiveSpinKinetic.density p (β x) (field β z) x

/-- A constant chiral angle contributes zero potential everywhere. -/
theorem potential_const (p : MassiveParameters) (b : ℝ) (x : Covector) :
    potential p (fun _ => b) x = 0 := by simp [potential, gradient, minkowski]

/-- Algebraic splitting of the chiral derivative term after summing the four signed squares. -/
theorem sum_correction (h : ℝ) (u b : Covector) (ρ : ℝ) :
    h ^ 2 * (∑ μ, sign μ * (u μ - (b μ ^ 2 / 4) * ρ)) =
      h ^ 2 * (∑ μ, sign μ * u μ) - (h ^ 2 / 4 * minkowski b b) * ρ := by
  have hb : (∑ μ, sign μ * (b μ ^ 2 / 4 * ρ)) = minkowski b b * (ρ / 4) := by
    rw [← signed_square, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro μ _
    ring
  simp only [mul_sub, Finset.sum_sub_distrib, hb]
  ring

variable (p : MassiveParameters) {β : Covector → ℝ} {z : Covector → ℂ} {x : Covector}

/-- The real kinetic contraction includes only the scalar kinetic sum and the signed chiral term. -/
theorem kinetic_re (hβ : DifferentiableAt ℝ β x) (hz : DifferentiableAt ℝ z x) :
    fieldKineticRe p.hbar (β x) (field β z) x coordinateDirections =
      p.hbar ^ 2 * (∑ μ, sign μ * Complex.normSq (fderiv ℝ z x (coordinateDirections μ))) -
        potential p β x * Complex.normSq (z x) := by
  let u : Covector := fun μ => Complex.normSq (fderiv ℝ z x (coordinateDirections μ))
  let b := gradient β x
  have he : fieldKinetic p.hbar (β x) (field β z) x coordinateDirections =
      ((p.hbar ^ 2 * ∑ μ, sign μ * (u μ - (b μ ^ 2 / 4) * Complex.normSq (z x)) : ℝ) : ℂ) := by
    unfold fieldKinetic kinetic
    simp_rw [fderiv_field_apply hβ hz, jet_square]
    simp only [Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_sum]
    rfl
  exact (congrArg Complex.re he).trans (sum_correction p.hbar u b _)

/-- The density identity holds for every differentiable scalar field, including its zeros. -/
theorem density_eq_pairing (hβ : DifferentiableAt ℝ β x) (hz : DifferentiableAt ℝ z x) :
    density p β z x = (ActionVariation.fieldPairing p z z coordinateDirections x).re -
      potential p β x * Complex.normSq (z x) := by
  have hz0 : field (fun _ => (0 : ℝ)) z = ScalarRestKinetic.lift z := by
    funext y
    exact value_zero (z y)
  have hc := kinetic_re p (β := fun _ => (0 : ℝ)) (differentiableAt_const 0) hz
  rw [potential_const, zero_mul, sub_zero, hz0] at hc
  rw [← ScalarRestKinetic.completed_eq_pairing p hz]
  unfold density MassiveSpinKinetic.density
  rw [kinetic_re p hβ hz, hc, invariantDensity_field, ScalarRestKinetic.lift,
    ScalarRestKinetic.invariantDensity_embed]
  ring

/-- On a smooth positive amplitude-phase chart the spin density equals the scalar
Hamilton–Jacobi–Fisher integrand less the actual chiral potential times ρ. -/
theorem density_eq_hydro (hβ : DifferentiableAt ℝ β x) {ρ S : Covector → ℝ}
    (hρ : DifferentiableAt ℝ ρ x) (hS : DifferentiableAt ℝ S x) (hp : 0 < ρ x) :
    density p β (ActionDensity.actionField p ρ S) x =
      PolarChartAction.hydroIntegrand p ρ S coordinateDirections x - potential p β x * ρ x := by
  have hphase : DifferentiableAt ℝ (fun y => S y / p.hbar) x := by
    simpa only [div_eq_mul_inv, mul_comm] using hS.const_mul p.hbar⁻¹
  have hz : DifferentiableAt ℝ (ActionDensity.actionField p ρ S) x :=
    PolarDifferential.differentiableAt_polarField hρ hphase hp
  rw [density_eq_pairing p hβ hz, ← PolarChartAction.hydroIntegrand_eq p hρ hS hp]
  exact congrArg (fun a => PolarChartAction.hydroIntegrand p ρ S coordinateDirections x - potential p β x * a)
    (ActionDensity.polarField_normSq ρ _ x hp.le)

/-- The chiral potential scales quadratically when the angle is scaled by a constant. -/
theorem potential_scale (p : MassiveParameters) (k : ℝ) {β : Covector → ℝ} {x : Covector}
    (hβ : DifferentiableAt ℝ β x) :
    potential p (fun y => k * β y) x = k ^ 2 * potential p β x := by
  have hd (μ : Fin 4) : gradient (fun y => k * β y) x μ = k * gradient β x μ := by
    unfold gradient
    rw [(hβ.hasFDerivAt.const_mul k).fderiv]
    rfl
  unfold potential
  simp only [← signed_square]
  simp_rw [hd]
  rw [show (∑ μ, sign μ * (k * gradient β x μ)^2) = k^2 * ∑ μ, sign μ * (gradient β x μ)^2 by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro μ _; ring]
  ring

end FoliationQM.TwistedScalarDensity
