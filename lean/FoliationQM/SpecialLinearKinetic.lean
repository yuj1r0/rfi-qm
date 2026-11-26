module
public import FoliationQM.SpinFisherDensity
public import FoliationQM.SpecialLinearRicci

/-!
# Actual determinant-one polar kinetic and spin Fisher identities

Sources: v13 `eq:spinor_quadratic_exact`, `eq:sl2c_fisher_metric_main`,
and the forward quadratic decomposition in `thm:dirac_lift`. The matrix
field is actually differentiable and has determinant one on a neighborhood.
Its concrete spin representative supplies invertibility, gamma5
commutation and Dirac isometry. Its actual constructed real frame and
body coefficients supply the gamma and generator expansions and frame
entry differentiability.

Consequently the neutralized directional square, full complex kinetic
contraction, faithful real contraction and actual spin Fisher decomposition
require no supplied frame or generator premises. The original scalar
fields have actual derivatives and positive density at the point; the
physical projection uses explicit nonzero c. Only first derivatives are
needed. These are forward local kinematic identities, with no positivity,
phase exactness, variational equivalence or Dirac equation conclusion.
-/

@[expose] public section
noncomputable section
open scoped Matrix.Norms.Operator
open Filter Topology
namespace FoliationQM.SpecialLinearKinetic
open DiracMatrices DiracAdjoint SpinorMatrix SpecialLinearSpin SpecialLinearSpinDifferential
open SpecialLinearConnection SpecialLinearFrame SpecialLinearRicci
open PolarSpinorDifferential NeutralizedSpinorKinetic ChiralNeutralization
open SpinFisherDensity RealLorentzFrame SixTermConnection CanonicalDiracContraction
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The actual derivative of a determinant-one polar field has the complete complex neutralized square with its constructed body coefficients and no supplied matrix-connection premise. -/
theorem neutralized_derivative_square {rho beta : E → ℝ} {A : E → Mat2} {x : E}
    (hrho : DifferentiableAt ℝ rho x) (hbeta : DifferentiableAt ℝ beta x)
    (hA : DifferentiableAt ℝ A x) (hpos : 0 < rho x)
    (hdet : ∀ᶠ y in 𝓝 x, (A y).det = 1) (v : E) :
    bilinear (fderiv ℝ (polarField rho beta (fun y => spin (A y))) x v) (neutralizer (beta x))
      (fderiv ℝ (polarField rho beta (fun y => spin (A y))) x v) =
      ((rho x / 4 * ((fderiv ℝ (fun y => Real.log (rho y)) x v)^2 -
        (fderiv ℝ beta x v)^2 + pairedProductSum (bodyOmega A x v) (bodyOmega A x v)) : ℝ) : ℂ) :=
  NeutralizedSpinorKinetic.neutralized_derivative_square hrho hbeta
    (differentiableAt_spin_field hA) hpos (spin_isUnit _ hdet.self_of_nhds)
    (Filter.Eventually.of_forall (fun y => spin_gamma5_commute (A y)))
    (hdet.mono (fun y hy => spin_dirac_isometry (A y) hy))
    v (bodyOmega A x v) (body_eq_generator hA hdet v) (bodyOmega_antisymmetric A x v)

/-- The complete complex neutralized kinetic density of an actual determinant-one polar field equals its amplitude, chiral and constructed Lorentz-coefficient quadratic terms. -/
theorem fieldKinetic_polar {rho beta : E → ℝ} {A : E → Mat2} {x : E}
    (hrho : DifferentiableAt ℝ rho x) (hbeta : DifferentiableAt ℝ beta x)
    (hA : DifferentiableAt ℝ A x) (hpos : 0 < rho x)
    (hdet : ∀ᶠ y in 𝓝 x, (A y).det = 1) (directions : Fin 4 → E) (hbar : ℝ) :
    fieldKinetic hbar (beta x) (polarField rho beta (fun y => spin (A y))) x directions =
      ((rho x*hbar^2/4*
        ((∑ mu, sign mu*(fderiv ℝ (fun y => Real.log (rho y)) x (directions mu))^2) -
         (∑ mu, sign mu*(fderiv ℝ beta x (directions mu))^2) +
         (∑ mu, sign mu*pairedProductSum (bodyOmega A x (directions mu))
           (bodyOmega A x (directions mu)))) : ℝ) : ℂ) :=
  NeutralizedSpinorKinetic.fieldKinetic_polar hrho hbeta
    (differentiableAt_spin_field hA) hpos (spin_isUnit _ hdet.self_of_nhds)
    (Filter.Eventually.of_forall (fun y => spin_gamma5_commute (A y)))
    (hdet.mono (fun y hy => spin_dirac_isometry (A y) hy))
    directions (fun mu => bodyOmega A x (directions mu))
    (fun mu => body_eq_generator hA hdet (directions mu))
    (fun mu => bodyOmega_antisymmetric A x (directions mu)) hbar

/-- The faithful real neutralized kinetic density has the same actual derivative and constructed Lorentz-coefficient quadratic decomposition. -/
theorem fieldKineticRe_polar {rho beta : E → ℝ} {A : E → Mat2} {x : E}
    (hrho : DifferentiableAt ℝ rho x) (hbeta : DifferentiableAt ℝ beta x)
    (hA : DifferentiableAt ℝ A x) (hpos : 0 < rho x)
    (hdet : ∀ᶠ y in 𝓝 x, (A y).det = 1) (directions : Fin 4 → E) (hbar : ℝ) :
    fieldKineticRe hbar (beta x) (polarField rho beta (fun y => spin (A y))) x directions =
      rho x*hbar^2/4*
        ((∑ mu, sign mu*(fderiv ℝ (fun y => Real.log (rho y)) x (directions mu))^2) -
         (∑ mu, sign mu*(fderiv ℝ beta x (directions mu))^2) +
         (∑ mu, sign mu*pairedProductSum (bodyOmega A x (directions mu))
           (bodyOmega A x (directions mu)))) :=
  congrArg Complex.re (fieldKinetic_polar hrho hbeta hA hpos hdet directions hbar)

/-- The actual real neutralized kinetic density is the constructed spin-connection square plus the actual spin Fisher density of the constructed real frame. -/
theorem fieldKineticRe_eq_spinFisher {rho beta : E → ℝ} {A : E → Mat2} {x : E}
    (hrho : DifferentiableAt ℝ rho x) (hbeta : DifferentiableAt ℝ beta x)
    (hA : DifferentiableAt ℝ A x) (hpos : 0 < rho x)
    (hdet : ∀ᶠ y in 𝓝 x, (A y).det = 1) (directions : Fin 4 → E)
    (hbar c : ℝ) (hc : c ≠ 0) :
    fieldKineticRe hbar (beta x) (polarField rho beta (fun y => spin (A y))) x directions =
      rho x*(∑ mu, sign mu*(spinCoefficient hbar (fun mu => bodyOmega A x (directions mu)) mu)^2) +
        spinFisherDensity rho beta (fun y => frame (A y)) x directions hbar c :=
  SpinFisherDensity.fieldKineticRe_eq_spinFisher hrho hbeta
    (differentiableAt_spin_field hA) hpos (spin_isUnit _ hdet.self_of_nhds)
    (Filter.Eventually.of_forall (fun y => spin_gamma5_commute (A y)))
    (hdet.mono (fun y hy => spin_dirac_isometry (A y) hy))
    (differentiableAt_frame_entry hA) (eventual_frame_expansion hdet)
    directions (fun mu => bodyOmega A x (directions mu))
    (fun mu => body_eq_generator hA hdet (directions mu))
    (fun mu => bodyOmega_antisymmetric A x (directions mu)) hbar c hc

/-- The complete complex neutralized kinetic expression equals the real constructed spin-connection square plus the actual spin Fisher density, without discarding an imaginary term. -/
theorem fieldKinetic_eq_spinFisher {rho beta : E → ℝ} {A : E → Mat2} {x : E}
    (hrho : DifferentiableAt ℝ rho x) (hbeta : DifferentiableAt ℝ beta x)
    (hA : DifferentiableAt ℝ A x) (hpos : 0 < rho x)
    (hdet : ∀ᶠ y in 𝓝 x, (A y).det = 1) (directions : Fin 4 → E)
    (hbar c : ℝ) (hc : c ≠ 0) :
    fieldKinetic hbar (beta x) (polarField rho beta (fun y => spin (A y))) x directions =
      ((rho x*(∑ mu, sign mu*(spinCoefficient hbar (fun mu => bodyOmega A x (directions mu)) mu)^2) +
        spinFisherDensity rho beta (fun y => frame (A y)) x directions hbar c : ℝ) : ℂ) := by
  rw [fieldKinetic_eq_ofReal, fieldKineticRe_eq_spinFisher hrho hbeta hA hpos hdet directions hbar c hc]

end FoliationQM.SpecialLinearKinetic
