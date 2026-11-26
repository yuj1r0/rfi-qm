module

public import FoliationQM.NeutralizedSpinorKinetic
public import FoliationQM.VelocitySpinKinetic

/-!
# The actual spin Fisher density and neutralized kinetic decomposition

Source: v13 `eq:sl2c_fisher_metric_main` and the concluding decomposition in
`thm:dirac_lift` (iii). The coefficient expression retains the Lorentzian
spacetime metric and the Minkowski vector contractions. The actual field
density substitutes genuine Frechet derivatives of log density, chiral
angle and physical velocity, together with the actual Fermi--Walker
projection of the spin derivative.

The complete complex neutralized kinetic expression is the spin-connection
square plus this real density, by the two previously verified actual
field identities. The explicit local matrix and coefficient hypotheses are
retained. This forward kinematic identity does not assert positivity,
polar reconstruction, scalar phase exactness or a variational equation.
-/

@[expose] public section
noncomputable section
open scoped Matrix.Norms.Operator
open Filter Topology
namespace FoliationQM.SpinFisherDensity
open DiracMatrices DiracAdjoint RealLorentzFrame PolarVectorGeometry
open PolarSpinorDifferential NeutralizedSpinorKinetic VelocitySpinKinetic
open CanonicalDiracContraction MaurerCartanDifferential CliffordCommutators

/-- The Lorentzian coefficient expression with amplitude and chiral gradients, already projected spin gradients, and physical velocity gradients. -/
def quadraticFisher (rho hbar c : ℝ) (g b : Fin 4 → ℝ)
    (ds du : Fin 4 → Covector) : ℝ :=
  rho*hbar^2/4*((∑ mu, sign mu*(g mu)^2) - (∑ mu, sign mu*(b mu)^2) -
    (∑ mu, sign mu*minkowski (ds mu) (ds mu)) +
    (1/c^2)*(∑ mu, sign mu*minkowski (du mu) (du mu)))

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The source spin Fisher density evaluated on actual first derivatives and the actual projected spin derivative. -/
def spinFisherDensity (rho beta : E → ℝ) (u : E → Fin 4 → Covector) (x : E)
    (directions : Fin 4 → E) (hbar c : ℝ) : ℝ :=
  quadraticFisher (rho x) hbar c
    (fun mu => fderiv ℝ (fun y => Real.log (rho y)) x (directions mu))
    (fun mu => fderiv ℝ beta x (directions mu))
    (fun mu => fwSpinDerivative c u x (directions mu))
    (fun mu => fderiv ℝ (fun y => velocity c (u y)) x (directions mu))

/-- The actual density is the coefficient expression evaluated on genuine log-density, angle, projected-spin and velocity derivatives. -/
theorem spinFisherDensity_eq_quadraticFisher (rho beta : E → ℝ)
    (u : E → Fin 4 → Covector) (x : E) (directions : Fin 4 → E) (hbar c : ℝ) :
    spinFisherDensity rho beta u x directions hbar c =
      quadraticFisher (rho x) hbar c
        (fun mu => fderiv ℝ (fun y => Real.log (rho y)) x (directions mu))
        (fun mu => fderiv ℝ beta x (directions mu))
        (fun mu => fwSpinDerivative c u x (directions mu))
        (fun mu => fderiv ℝ (fun y => velocity c (u y)) x (directions mu)) := rfl

/-- The actual source density has the explicit Lorentzian log-density, chiral-angle, projected-spin and velocity-gradient terms. -/
theorem spinFisherDensity_eq_source (rho beta : E → ℝ)
    (u : E → Fin 4 → Covector) (x : E) (directions : Fin 4 → E) (hbar c : ℝ) :
    spinFisherDensity rho beta u x directions hbar c =
      rho x*hbar^2/4*
        ((∑ mu, sign mu*(fderiv ℝ (fun y => Real.log (rho y)) x (directions mu))^2) -
         (∑ mu, sign mu*(fderiv ℝ beta x (directions mu))^2) -
         (∑ mu, sign mu*minkowski (fwSpinDerivative c u x (directions mu))
           (fwSpinDerivative c u x (directions mu))) +
         (1/c^2)*(∑ mu, sign mu*minkowski
           (fderiv ℝ (fun y => velocity c (u y)) x (directions mu))
           (fderiv ℝ (fun y => velocity c (u y)) x (directions mu)))) := rfl

/-- The faithful real neutralized kinetic density equals the actual spin-connection square plus the actual source spin Fisher density. -/
theorem fieldKineticRe_eq_spinFisher {rho beta : E → ℝ} {L : E → Mat}
    {u : E → Fin 4 → Covector} {x : E}
    (hrho : DifferentiableAt ℝ rho x) (hbeta : DifferentiableAt ℝ beta x)
    (hL : DifferentiableAt ℝ L x) (hpos : 0 < rho x) (hunit : IsUnit (L x))
    (h5 : ∀ᶠ y in 𝓝 x, Commute (L y) gamma5)
    (hiso : ∀ᶠ y in 𝓝 x, diracAdjoint (L y)*L y=1)
    (hu : ∀ A nu, DifferentiableAt ℝ (fun y => u y A nu) x)
    (hframe : ∀ᶠ y in 𝓝 x, ∀ A, L y*gamma A*(L y)⁻¹=gammaExpansion (u y A))
    (directions : Fin 4 → E) (omega : Fin 4 → Fin 4 → Fin 4 → ℝ)
    (hbody : ∀ mu, body L x (directions mu)=generator (omega mu))
    (hanti : ∀ mu a b, omega mu a b = -omega mu b a)
    (hbar c : ℝ) (hc : c ≠ 0) :
    fieldKineticRe hbar (beta x) (polarField rho beta L) x directions =
      rho x*(∑ mu, sign mu*(spinCoefficient hbar omega mu)^2) +
        spinFisherDensity rho beta u x directions hbar c := by
  have hmc := mc_velocity_spin_identity hL hunit hu hframe directions omega hanti hbody
    (rho x) hbar c hc
  rw [fieldKineticRe_polar hrho hbeta hL hpos hunit h5 hiso directions omega hbody hanti hbar,
    spinFisherDensity_eq_source]
  linear_combination hmc

/-- The complete complex neutralized kinetic expression is the real spin-connection square plus the actual spin Fisher density, with no discarded imaginary term. -/
theorem fieldKinetic_eq_spinFisher {rho beta : E → ℝ} {L : E → Mat}
    {u : E → Fin 4 → Covector} {x : E}
    (hrho : DifferentiableAt ℝ rho x) (hbeta : DifferentiableAt ℝ beta x)
    (hL : DifferentiableAt ℝ L x) (hpos : 0 < rho x) (hunit : IsUnit (L x))
    (h5 : ∀ᶠ y in 𝓝 x, Commute (L y) gamma5)
    (hiso : ∀ᶠ y in 𝓝 x, diracAdjoint (L y)*L y=1)
    (hu : ∀ A nu, DifferentiableAt ℝ (fun y => u y A nu) x)
    (hframe : ∀ᶠ y in 𝓝 x, ∀ A, L y*gamma A*(L y)⁻¹=gammaExpansion (u y A))
    (directions : Fin 4 → E) (omega : Fin 4 → Fin 4 → Fin 4 → ℝ)
    (hbody : ∀ mu, body L x (directions mu)=generator (omega mu))
    (hanti : ∀ mu a b, omega mu a b = -omega mu b a)
    (hbar c : ℝ) (hc : c ≠ 0) :
    fieldKinetic hbar (beta x) (polarField rho beta L) x directions =
      ((rho x*(∑ mu, sign mu*(spinCoefficient hbar omega mu)^2) +
        spinFisherDensity rho beta u x directions hbar c : ℝ) : ℂ) := by
  rw [fieldKinetic_eq_ofReal,
    fieldKineticRe_eq_spinFisher hrho hbeta hL hpos hunit h5 hiso hu hframe
      directions omega hbody hanti hbar c hc]

end FoliationQM.SpinFisherDensity
