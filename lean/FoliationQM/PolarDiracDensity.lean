module

public import FoliationQM.DiracFieldDensity
public import FoliationQM.PolarSpinorDifferential
public import FoliationQM.PolarConnectionContraction

/-!
# Actual polar-field substitution into the symmetric Dirac density

Source: v13 `eq:dirac_polar_lagrangian_main` and the local first-order
calculation in `thm:dirac_lift` (i). The input density is the stipulated
symmetric Dirac density. Its spinor jets are actual real Frechet derivatives,
and DiracFieldDensity identifies its adjoint slot with the actual derivative
of the Dirac-adjoint row field.

The polar derivatives, local Dirac-isometry and gamma5 constraints, actual
real frame expansion and actual body-generator coefficients yield the
canonical, chiral and mass terms. In particular, no amplitude derivative
survives. Two genuinely differentiable density fields with the same value
at the point give the same result without requiring equal derivatives.
This local forward substitution does not establish inverse polar
reconstruction, a variational equation, or an integrated action equivalence.
-/

@[expose] public section
noncomputable section
open scoped Matrix.Norms.Operator
set_option backward.isDefEq.respectTransparency false
open Filter Topology
namespace FoliationQM.PolarDiracDensity
open DiracMatrices DiracAdjoint DiracDensity DiracFieldDensity
open PolarSpinorBilinears PolarSpinorDifferential PolarConnectionContraction
open PolarVectorGeometry RealLorentzFrame MaurerCartanDifferential CliffordCommutators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The actual body-generator expansion identifies the actual spatial derivative connection with the transported generator. -/
theorem spatial_eq_transportedGenerator {L : E → Mat} {x : E}
    (hunit : IsUnit (L x)) (v : E) (omega : Fin 4 → Fin 4 → ℝ)
    (hbody : body L x v=generator omega) :
    spatial L x v=transportedGenerator (L x) omega := by
  rw [spatial_eq_conjugate_body hunit v, hbody]
  rfl

/-- Substituting the actual polar-field derivative cancels its actual real amplitude gradient in each directional Dirac pair. -/
theorem directionalPair_polarField {rho beta : E → ℝ} {L : E → Mat} {x : E}
    (hrho : DifferentiableAt ℝ rho x) (hbeta : DifferentiableAt ℝ beta x)
    (hL : DifferentiableAt ℝ L x) (hpos : 0 < rho x) (hunit : IsUnit (L x))
    (h5 : ∀ᶠ y in 𝓝 x, Commute (L y) gamma5)
    (hiso : ∀ᶠ y in 𝓝 x, diracAdjoint (L y)*L y=1) (v : E) (mu : Fin 4) :
    directionalPair (polarField rho beta L x) (fderiv ℝ (polarField rho beta L) x v) mu =
      Complex.I*(fderiv ℝ beta x v : ℂ)*
        bilinear (polarField rho beta L x) (gamma mu*gamma5) (polarField rho beta L x) +
      bilinear (polarField rho beta L x)
        (gamma mu*spatial L x v+spatial L x v*gamma mu) (polarField rho beta L x) := by
  rw [fderiv_polarField_source hrho hbeta hL hpos hunit h5]
  exact directionalPair_polar_matrix _ mu _ _ _ (spatial_diracAdjoint hL hunit hiso v)

private theorem chiral_kinetic_sum (rho hbar c : ℝ) (betaDir spin : Fin 4 → ℝ) :
    (Complex.I*(hbar : ℂ)*(c : ℂ)/2)*
        (∑ mu, Complex.I*(betaDir mu : ℂ)*((rho : ℂ)*(spin mu : ℂ))) =
      ((-(rho*(hbar*c/2)*(∑ mu, spin mu*betaDir mu)) : ℝ) : ℂ) := by
  have hs : (∑ mu, Complex.I*(betaDir mu : ℂ)*((rho : ℂ)*(spin mu : ℂ))) =
      (Complex.I*(rho : ℂ))*(∑ mu, ((spin mu*betaDir mu : ℝ) : ℂ)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro mu _
    push_cast
    ring
  rw [hs, ← Complex.ofReal_sum]
  push_cast
  ring_nf
  simp only [Complex.I_sq]
  ring

/-- The actual symmetric Dirac field density of the polar field equals its real canonical, chiral and mass expression with the exact source coefficients. -/
theorem fieldDensity_polar {rho beta : E → ℝ} {L : E → Mat} {x : E}
    (hrho : DifferentiableAt ℝ rho x) (hbeta : DifferentiableAt ℝ beta x)
    (hL : DifferentiableAt ℝ L x) (hpos : 0 < rho x) (hunit : IsUnit (L x))
    (h5 : ∀ᶠ y in 𝓝 x, Commute (L y) gamma5)
    (hiso : ∀ᶠ y in 𝓝 x, diracAdjoint (L y)*L y=1)
    {u : Fin 4 → Covector} (hu : ∀ A, L x*gamma A*(L x)⁻¹=gammaExpansion (u A))
    (directions : Fin 4 → E) (omega : Fin 4 → Fin 4 → Fin 4 → ℝ)
    (hbody : ∀ mu, body L x (directions mu)=generator (omega mu)) (hbar c m : ℝ) :
    fieldDensity hbar c m (polarField rho beta L) x directions =
      ((rho x*(canonicalContraction hbar c u omega -
        (hbar*c/2)*(∑ mu, inverseCoefficients u mu 3*fderiv ℝ beta x (directions mu)) -
        m*c^2*Real.cos (beta x)) : ℝ) : ℂ) := by
  have hp (mu : Fin 4) :
      directionalPair (polarField rho beta L x)
        (fderiv ℝ (polarField rho beta L) x (directions mu)) mu =
      Complex.I*(fderiv ℝ beta x (directions mu) : ℂ)*
        bilinear (polarField rho beta L x) (gamma mu*gamma5) (polarField rho beta L x) +
      bilinear (polarField rho beta L x)
        (gamma mu*transportedGenerator (L x) (omega mu)+
          transportedGenerator (L x) (omega mu)*gamma mu) (polarField rho beta L x) := by
    rw [directionalPair_polarField hrho hbeta hL hpos hunit h5 hiso,
      spatial_eq_transportedGenerator hunit (directions mu) (omega mu) (hbody mu)]
  simp only [fieldDensity, density]
  simp_rw [hp]
  rw [Finset.sum_add_distrib, mul_add]
  simp only [polarField]
  simp_rw [polar_axial_frame (rho x) (beta x) hpos.le hunit hiso.self_of_nhds h5.self_of_nhds hu]
  rw [connection_kinetic_sum (rho x) (beta x) hbar c hpos.le hunit
      hiso.self_of_nhds h5.self_of_nhds hu omega,
    polar_scalar (rho x) (beta x) (L x) hpos.le hiso.self_of_nhds h5.self_of_nhds]
  simp only [spinVector]
  rw [chiral_kinetic_sum]
  simp only [Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_pow,
    Complex.ofReal_div, Complex.ofReal_ofNat, Complex.ofReal_neg]
  ring

/-- The faithful real Dirac density equals the actual real polar expression, with no density-gradient term. -/
theorem fieldDensityRe_polar {rho beta : E → ℝ} {L : E → Mat} {x : E}
    (hrho : DifferentiableAt ℝ rho x) (hbeta : DifferentiableAt ℝ beta x)
    (hL : DifferentiableAt ℝ L x) (hpos : 0 < rho x) (hunit : IsUnit (L x))
    (h5 : ∀ᶠ y in 𝓝 x, Commute (L y) gamma5)
    (hiso : ∀ᶠ y in 𝓝 x, diracAdjoint (L y)*L y=1)
    {u : Fin 4 → Covector} (hu : ∀ A, L x*gamma A*(L x)⁻¹=gammaExpansion (u A))
    (directions : Fin 4 → E) (omega : Fin 4 → Fin 4 → Fin 4 → ℝ)
    (hbody : ∀ mu, body L x (directions mu)=generator (omega mu)) (hbar c m : ℝ) :
    fieldDensityRe hbar c m (polarField rho beta L) x directions =
      rho x*(canonicalContraction hbar c u omega -
        (hbar*c/2)*(∑ mu, inverseCoefficients u mu 3*fderiv ℝ beta x (directions mu)) -
        m*c^2*Real.cos (beta x)) := by
  unfold fieldDensityRe
  rw [fieldDensity_polar hrho hbeta hL hpos hunit h5 hiso hu directions omega hbody hbar c m]
  rfl

/-- Two actual differentiable density fields with the same positive value give the same polar Dirac density even when their actual derivatives differ. -/
theorem fieldDensity_amplitude_gradient_independent {rho₁ rho₂ beta : E → ℝ}
    {L : E → Mat} {x : E}
    (hrho₁ : DifferentiableAt ℝ rho₁ x) (hrho₂ : DifferentiableAt ℝ rho₂ x)
    (hvalue : rho₁ x=rho₂ x) (hbeta : DifferentiableAt ℝ beta x)
    (hL : DifferentiableAt ℝ L x) (hpos : 0 < rho₁ x) (hunit : IsUnit (L x))
    (h5 : ∀ᶠ y in 𝓝 x, Commute (L y) gamma5)
    (hiso : ∀ᶠ y in 𝓝 x, diracAdjoint (L y)*L y=1)
    {u : Fin 4 → Covector} (hu : ∀ A, L x*gamma A*(L x)⁻¹=gammaExpansion (u A))
    (directions : Fin 4 → E) (omega : Fin 4 → Fin 4 → Fin 4 → ℝ)
    (hbody : ∀ mu, body L x (directions mu)=generator (omega mu)) (hbar c m : ℝ) :
    fieldDensity hbar c m (polarField rho₁ beta L) x directions =
      fieldDensity hbar c m (polarField rho₂ beta L) x directions := by
  have hpos₂ : 0 < rho₂ x := by rw [← hvalue]; exact hpos
  rw [fieldDensity_polar hrho₁ hbeta hL hpos hunit h5 hiso hu directions omega hbody hbar c m,
    fieldDensity_polar hrho₂ hbeta hL hpos₂ hunit h5 hiso hu directions omega hbody hbar c m,
    hvalue]

end FoliationQM.PolarDiracDensity
