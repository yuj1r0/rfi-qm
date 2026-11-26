module

public import FoliationQM.PolarDiracDensity
public import FoliationQM.ChiralNeutralization
public import FoliationQM.LorentzGeneratorQuadratic

/-!
# Actual chiral-neutralized polar derivative contraction

Source: v13 `eq:spinor_quadratic_exact`, the forward quadratic identity in
`thm:dirac_lift` (ii). The kinetic expression is built from actual complex
Dirac bilinears and the genuine inverse chiral exponential. Its four jets
are actual Frechet derivatives along supplied directions. The diagonal
(+---) contraction is also identified with the full two-index metric sum.

Actual differentiability, positive density, local gamma5 commutation and
Dirac isometry, and actual antisymmetric body-generator coefficients give
the complete complex identity before taking real parts. The amplitude,
chiral and six-pair terms have the source signs and factor one quarter.
Only first derivatives are needed for this quadratic expression. No
second-order field equation, inverse polar reconstruction, variational
principle or Dirac-equation equivalence is claimed.
-/

@[expose] public section
noncomputable section
open scoped Matrix.Norms.Operator
set_option backward.isDefEq.respectTransparency false
open Filter Topology
namespace FoliationQM.NeutralizedSpinorKinetic
open DiracMatrices DiracAdjoint MatrixDifferential
open PolarSpinorBilinears PolarSpinorDifferential PolarConnectionContraction
open ChiralNeutralization LorentzGeneratorQuadratic RealLorentzFrame SixTermConnection
open MaurerCartanDifferential CliffordCommutators PolarDiracDensity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The actual neutralized quadratic spinor-jet contraction with the diagonal (+---) spacetime metric. -/
def kinetic (hbar beta : ℝ) (jet : Fin 4 → Spinor) : ℂ :=
  (hbar : ℂ)^2 * ∑ mu, (sign mu : ℂ) * bilinear (jet mu) (neutralizer beta) (jet mu)

/-- The real part of the actual neutralized quadratic spinor-jet contraction. -/
def kineticRe (hbar beta : ℝ) (jet : Fin 4 → Spinor) : ℝ := (kinetic hbar beta jet).re

/-- The neutralized quadratic kinetic expression evaluated on actual Frechet derivatives of a spinor field. -/
def fieldKinetic (hbar beta : ℝ) (psi : E → Spinor) (x : E) (directions : Fin 4 → E) : ℂ :=
  kinetic hbar beta (fun mu => fderiv ℝ psi x (directions mu))

/-- The real part of the actual neutralized quadratic spinor-field expression. -/
def fieldKineticRe (hbar beta : ℝ) (psi : E → Spinor) (x : E)
    (directions : Fin 4 → E) : ℝ := (fieldKinetic hbar beta psi x directions).re

/-- The diagonal spacetime contraction equals the genuine two-index contraction by the actual Dirac metric. -/
theorem kinetic_eq_metric_contraction (hbar beta : ℝ) (jet : Fin 4 → Spinor) :
    kinetic hbar beta jet = (hbar : ℂ)^2 *
      ∑ mu, ∑ nu, eta mu nu * bilinear (jet mu) (neutralizer beta) (jet nu) := by
  unfold kinetic
  congr 1
  apply Finset.sum_congr rfl
  intro mu _
  by_cases h : mu = 0 <;> simp [eta, sign, h]

/-- The actual quadratic contraction is fixed by complex conjugation for every spinor jet. -/
theorem kinetic_star (hbar beta : ℝ) (jet : Fin 4 → Spinor) :
    star (kinetic hbar beta jet) = kinetic hbar beta jet := by
  simp only [kinetic, star_mul, star_pow, star_sum, star_bilinear,
    neutralizer_diracAdjoint, Complex.star_def, Complex.conj_ofReal]
  simp only [mul_comm]

/-- The actual neutralized kinetic expression has zero imaginary part for arbitrary spinor jets. -/
theorem kinetic_im_eq_zero (hbar beta : ℝ) (jet : Fin 4 → Spinor) :
    (kinetic hbar beta jet).im = 0 :=
  Complex.conj_eq_iff_im.mp (kinetic_star hbar beta jet)

/-- Taking the real part preserves the full neutralized kinetic expression. -/
theorem kinetic_eq_ofReal (hbar beta : ℝ) (jet : Fin 4 → Spinor) :
    kinetic hbar beta jet = (kineticRe hbar beta jet : ℂ) := by
  apply Complex.ext
  · rfl
  · simpa only [Complex.ofReal_im] using kinetic_im_eq_zero hbar beta jet

/-- The actual field kinetic expression is faithfully reconstructed from its real part. -/
theorem fieldKinetic_eq_ofReal (hbar beta : ℝ) (psi : E → Spinor) (x : E)
    (directions : Fin 4 → E) :
    fieldKinetic hbar beta psi x directions = (fieldKineticRe hbar beta psi x directions : ℂ) :=
  kinetic_eq_ofReal hbar beta _

/-- The left spinor slot is exactly the actual derivative of the Dirac-adjoint row field. -/
theorem fieldKinetic_eq_row (hbar beta : ℝ) {psi : E → Spinor} {x : E}
    (hpsi : DifferentiableAt ℝ psi x) (directions : Fin 4 → E) :
    fieldKinetic hbar beta psi x directions = (hbar : ℂ)^2 *
      ∑ mu, (sign mu : ℂ) * dotProduct
        (fderiv ℝ (fun y => spinorAdjoint (psi y)) x (directions mu))
        ((neutralizer beta).mulVec (fderiv ℝ psi x (directions mu))) := by
  simp only [fieldKinetic, kinetic, DiracDensity.bilinear_eq_row,
    fderiv_spinorAdjoint_apply hpsi]

/-- The spacetime-first signed generator contraction equals the source pair-first contraction with its raised spacetime index. -/
theorem connection_contraction_eq_pair_first (omega : Fin 4 → Fin 4 → Fin 4 → ℝ) :
    (∑ mu, sign mu * pairedProductSum (omega mu) (omega mu)) =
      signedPairSum (fun a b => ∑ mu, sign mu * omega mu a b * omega mu a b) := by
  simp only [pairedProductSum_eq_six_terms, signedPairSum_eq_six_terms]
  simp only [mul_add, mul_sub, mul_neg, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.sum_neg_distrib, mul_assoc]

/-- Each actual polar-field derivative has the exact neutralized amplitude, chiral and six-pair square, with no mixed terms. -/
theorem neutralized_derivative_square {rho beta : E → ℝ} {L : E → Mat} {x : E}
    (hrho : DifferentiableAt ℝ rho x) (hbeta : DifferentiableAt ℝ beta x)
    (hL : DifferentiableAt ℝ L x) (hpos : 0 < rho x) (hunit : IsUnit (L x))
    (h5 : ∀ᶠ y in 𝓝 x, Commute (L y) gamma5)
    (hiso : ∀ᶠ y in 𝓝 x, diracAdjoint (L y)*L y=1)
    (v : E) (omega : Fin 4 → Fin 4 → ℝ)
    (hbody : body L x v=generator omega) (hanti : ∀ a b, omega a b = -omega b a) :
    bilinear (fderiv ℝ (polarField rho beta L) x v) (neutralizer (beta x))
      (fderiv ℝ (polarField rho beta L) x v) =
      ((rho x / 4 * ((fderiv ℝ (fun y => Real.log (rho y)) x v)^2 -
        (fderiv ℝ beta x v)^2 + pairedProductSum omega omega) : ℝ) : ℂ) := by
  rw [fderiv_polarField_source hrho hbeta hL hpos hunit h5,
    spatial_eq_transportedGenerator hunit v omega hbody]
  have hhalf : Complex.I*(fderiv ℝ beta x v : ℂ)/2 =
      Complex.I*((fderiv ℝ beta x v/2 : ℝ) : ℂ) := by push_cast; ring
  rw [hhalf]
  simp only [polarField]
  rw [polar_generator_jet_square (rho x) (beta x)
    (fderiv ℝ (fun y => Real.log (rho y)) x v/2) (fderiv ℝ beta x v/2)
    (L x) omega hpos.le hunit hiso.self_of_nhds h5.self_of_nhds]
  rw [sub_eq_add_neg, rest_generator_square omega hanti]
  push_cast
  ring

private theorem weighted_quadratic_sum (rho hbar : ℝ) (p q r : Fin 4 → ℝ) :
    (hbar : ℂ)^2 * (∑ mu, (sign mu : ℂ)*((rho/4*(p mu^2-q mu^2+r mu) : ℝ) : ℂ)) =
      ((rho*hbar^2/4*((∑ mu, sign mu*p mu^2)-(∑ mu, sign mu*q mu^2)+
        (∑ mu, sign mu*r mu)) : ℝ) : ℂ) := by
  push_cast
  simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.mul_sum]
  congr 2 <;> first | (apply Finset.sum_congr rfl; intro mu _; ring) | (funext mu; ring)

/-- The complete complex neutralized kinetic density of an actual polar field equals the exact source quadratic expression using only first derivatives. -/
theorem fieldKinetic_polar {rho beta : E → ℝ} {L : E → Mat} {x : E}
    (hrho : DifferentiableAt ℝ rho x) (hbeta : DifferentiableAt ℝ beta x)
    (hL : DifferentiableAt ℝ L x) (hpos : 0 < rho x) (hunit : IsUnit (L x))
    (h5 : ∀ᶠ y in 𝓝 x, Commute (L y) gamma5)
    (hiso : ∀ᶠ y in 𝓝 x, diracAdjoint (L y)*L y=1)
    (directions : Fin 4 → E) (omega : Fin 4 → Fin 4 → Fin 4 → ℝ)
    (hbody : ∀ mu, body L x (directions mu)=generator (omega mu))
    (hanti : ∀ mu a b, omega mu a b = -omega mu b a) (hbar : ℝ) :
    fieldKinetic hbar (beta x) (polarField rho beta L) x directions =
      ((rho x*hbar^2/4*
        ((∑ mu, sign mu*(fderiv ℝ (fun y => Real.log (rho y)) x (directions mu))^2) -
         (∑ mu, sign mu*(fderiv ℝ beta x (directions mu))^2) +
         (∑ mu, sign mu*pairedProductSum (omega mu) (omega mu))) : ℝ) : ℂ) := by
  simp only [fieldKinetic, kinetic]
  simp_rw [neutralized_derivative_square hrho hbeta hL hpos hunit h5 hiso
    _ _ (hbody _) (hanti _)]
  exact weighted_quadratic_sum _ _ _ _ _

/-- The faithful real kinetic density has the same exact amplitude, chiral and Lorentz-connection quadratic terms. -/
theorem fieldKineticRe_polar {rho beta : E → ℝ} {L : E → Mat} {x : E}
    (hrho : DifferentiableAt ℝ rho x) (hbeta : DifferentiableAt ℝ beta x)
    (hL : DifferentiableAt ℝ L x) (hpos : 0 < rho x) (hunit : IsUnit (L x))
    (h5 : ∀ᶠ y in 𝓝 x, Commute (L y) gamma5)
    (hiso : ∀ᶠ y in 𝓝 x, diracAdjoint (L y)*L y=1)
    (directions : Fin 4 → E) (omega : Fin 4 → Fin 4 → Fin 4 → ℝ)
    (hbody : ∀ mu, body L x (directions mu)=generator (omega mu))
    (hanti : ∀ mu a b, omega mu a b = -omega mu b a) (hbar : ℝ) :
    fieldKineticRe hbar (beta x) (polarField rho beta L) x directions =
      rho x*hbar^2/4*
        ((∑ mu, sign mu*(fderiv ℝ (fun y => Real.log (rho y)) x (directions mu))^2) -
         (∑ mu, sign mu*(fderiv ℝ beta x (directions mu))^2) +
         (∑ mu, sign mu*pairedProductSum (omega mu) (omega mu))) := by
  exact congrArg Complex.re (fieldKinetic_polar hrho hbeta hL hpos hunit h5 hiso
    directions omega hbody hanti hbar)

end FoliationQM.NeutralizedSpinorKinetic
