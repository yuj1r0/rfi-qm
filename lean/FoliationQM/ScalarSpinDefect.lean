module
public import FoliationQM.MassiveSpinKinetic
public import FoliationQM.DiracHSDensity
public import FoliationQM.PolarChartAction

/-!
# Exact comparison with the scalar Hamilton–Jacobi–Fisher density

For v13 `thm:dirac_lift`, `eq:sl2c_fisher_metric_main` and `eq:coupled_action`,
the difference at a regular point consists of the difference of squared
phase covectors, the chiral gradient, the projected spin derivative and
the physical velocity derivative. All spacetime signs are Lorentzian.
-/

@[expose] public section
noncomputable section
open scoped Matrix.Norms.Operator
namespace FoliationQM.ScalarSpinDefect
open DiracMatrices DiracFieldDensity SpinorMatrix SpinorRegularity
open SpinFisherDensity CanonicalDiracContraction RealLorentzFrame SpecialLinearConnection
open VelocitySpinKinetic PolarVectorGeometry ReconstructedFrameGeometry DiracHSDensity

/-- The four derivatives of a real field in the spacetime coordinates. -/
def gradient (f : Covector → ℝ) (x : Covector) : Covector :=
  fun μ => fderiv ℝ f x (coordinateDirections μ)

/-- The spin-axis connection extracted from the true determinant-one matrix field. -/
def connection (p : MassiveParameters) (A : Covector → Mat2) (x : Covector) : Covector :=
  spinCoefficient p.hbar (fun ν => bodyOmega A x (coordinateDirections ν))

/-- Chiral, projected-spin and velocity terms in addition to the scalar Fisher term. -/
def auxiliary (p : MassiveParameters) (ρ : ℝ) (b : Covector) (ds du : Fin 4 → Covector) : ℝ :=
  ρ * p.hbar ^ 2 / 4 * (-minkowski b b -
    (∑ μ, sign μ * minkowski (ds μ) (ds μ)) +
    (1 / p.c ^ 2) * ∑ μ, sign μ * minkowski (du μ) (du μ))

/-- The signed sum of squared components is the covector's Minkowski square. -/
theorem signed_square (a : Covector) : (∑ μ, sign μ * (a μ)^2) = minkowski a a := by
  rw [minkowski_eq_sum]
  apply Finset.sum_congr rfl
  intro μ _
  ring

/-- The exact coefficient identity allows independent phase and connection covectors. -/
theorem coefficient_comparison (p : MassiveParameters) (ρ : ℝ) (a dS g b : Covector)
    (ds du : Fin 4 → Covector) :
    ρ * minkowski a a + quadraticFisher ρ p.hbar p.c g b ds du - ρ * (p.m ^ 2 * p.c ^ 2) =
      ActionDensity.hydroDensity p ρ dS g + ρ * (minkowski a a - minkowski dS dS) +
      auxiliary p ρ b ds du := by
  simp only [quadraticFisher, ActionDensity.hydroDensity, auxiliary, signed_square]
  ring

/-- Vanishing chiral and frame derivatives eliminate all three correction terms. -/
theorem auxiliary_zero (p : MassiveParameters) (ρ : ℝ) : auxiliary p ρ 0 0 0 = 0 := by
  simp [auxiliary, minkowski]

/-- The true projected-spin derivative array in the reconstructed frame. -/
def spinGradient (p : MassiveParameters) (ψ : Covector → Spinor) (x : Covector) (μ : Fin 4) : Covector :=
  fwSpinDerivative p.c (fun y => reconstructedFrame (ψ y)) x (coordinateDirections μ)

/-- The true velocity derivative array in the reconstructed frame. -/
def velocityGradient (p : MassiveParameters) (ψ : Covector → Spinor) (x : Covector) (μ : Fin 4) : Covector :=
  fderiv ℝ (fun y => velocity p.c (reconstructedFrame (ψ y))) x (coordinateDirections μ)

/-- Pointwise comparison on an actual polar germ, for an arbitrary scalar phase field. -/
theorem density_comparison (p : MassiveParameters) {ψ : Covector → Spinor} {x : Covector}
    (P : LocalFactors ψ x) (S : Covector → ℝ) :
    MassiveSpinKinetic.density p (P.angle x) ψ x =
      PolarChartAction.hydroIntegrand p (fun y => invariantDensity (ψ y)) S coordinateDirections x +
        invariantDensity (ψ x) * (minkowski (connection p P.rotor x) (connection p P.rotor x) -
          minkowski (gradient S x) (gradient S x)) +
        auxiliary p (invariantDensity (ψ x)) (gradient P.angle x) (spinGradient p ψ x) (velocityGradient p ψ x) := by
  unfold MassiveSpinKinetic.density
  rw [ReconstructedSpinFisher.fieldKineticRe_of_local_polar P.density_smooth.differentiableAt_one
    P.angle_smooth.differentiableAt_one P.rotor_smooth.differentiableAt_one P.realization
    coordinateDirections p.hbar p.c (ne_of_gt p.c_pos), signed_square]
  exact coefficient_comparison p _ _ _ _ _ _ _

/-- A phase primitive removes the connection difference. The auxiliary terms remain explicit. -/
theorem density_of_primitive (p : MassiveParameters) {ψ : Covector → Spinor} {x : Covector}
    (P : LocalFactors ψ x) (S : Covector → ℝ) (ha : connection p P.rotor x = gradient S x) :
    MassiveSpinKinetic.density p (P.angle x) ψ x =
      PolarChartAction.hydroIntegrand p (fun y => invariantDensity (ψ y)) S coordinateDirections x +
        auxiliary p (invariantDensity (ψ x)) (gradient P.angle x) (spinGradient p ψ x) (velocityGradient p ψ x) := by
  rw [density_comparison p P S, ha, sub_self, mul_zero, add_zero]

/-- At vanishing auxiliary gradients the massive quadratic expression equals the scalar integrand. -/
theorem density_eq_scalar (p : MassiveParameters) {ψ : Covector → Spinor} {x : Covector}
    (P : LocalFactors ψ x) (S : Covector → ℝ) (ha : connection p P.rotor x = gradient S x)
    (hb : gradient P.angle x = 0) (hs : spinGradient p ψ x = 0) (hu : velocityGradient p ψ x = 0) :
    MassiveSpinKinetic.density p (P.angle x) ψ x =
      PolarChartAction.hydroIntegrand p (fun y => invariantDensity (ψ y)) S coordinateDirections x := by
  rw [density_of_primitive p P S ha, hb, hs, hu, auxiliary_zero, add_zero]

end FoliationQM.ScalarSpinDefect
