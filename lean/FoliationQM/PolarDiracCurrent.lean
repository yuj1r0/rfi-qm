module
public import FoliationQM.DiracCurrent
public import FoliationQM.PolarSpinorDifferential
public import FoliationQM.PolarVectorGeometry

/-!
# The actual polar Dirac current and local continuity transfer

Source: the current identification J = rho u preceding v13
`eq:gordon_decomp`. The actual c-scaled Dirac bilinear equals density times
the physical velocity derived from the supplied real frame expansion.
The equality is proved for both the complete complex current and its
faithful real value; it is not a supplied current hypothesis.

For differentiable positive-density polar fields, local actual invertibility,
Dirac isometry and real frame expansion derive equality of the two current
fields near the point. Their genuine derivatives therefore agree. The
conditional Dirac current conservation theorem transfers to the actual
rho-times-velocity divergence. No scalar phase, inverse polar construction,
variational equation, or integrated charge/boundary statement is asserted.
-/

@[expose] public section
noncomputable section
open scoped Matrix.Norms.Operator
open Filter Topology
namespace FoliationQM.PolarDiracCurrent
open DiracMatrices DiracAdjoint DiracCurrent DiracEquation
open PolarSpinorBilinears PolarSpinorDifferential PolarVectorGeometry RealLorentzFrame

/-- The actual complex current of the forward polar ansatz is density times the physical velocity derived from the actual frame. -/
theorem polar_current_eq_density_velocity (rho beta c : ℝ) {L : Mat} {u : Fin 4 → Covector}
    (hrho : 0 ≤ rho) (hunit : IsUnit L) (hiso : diracAdjoint L*L=1)
    (hframe : ∀ A, L*gamma A*L⁻¹=gammaExpansion (u A)) (mu : Fin 4) :
    current c (polarSpinor rho beta L) mu = ((rho * velocity c u mu : ℝ) : ℂ) := by
  rw [current, polar_vector_frame rho beta hrho hunit hiso hframe]
  simp only [velocity, Complex.ofReal_mul]
  ring

/-- The faithful real polar current is exactly density times its derived physical velocity. -/
theorem polar_currentRe_eq_density_velocity (rho beta c : ℝ) {L : Mat} {u : Fin 4 → Covector}
    (hrho : 0 ≤ rho) (hunit : IsUnit L) (hiso : diracAdjoint L*L=1)
    (hframe : ∀ A, L*gamma A*L⁻¹=gammaExpansion (u A)) (mu : Fin 4) :
    currentRe c (polarSpinor rho beta L) mu = rho * velocity c u mu := by
  have h := congrArg Complex.re (polar_current_eq_density_velocity rho beta c hrho hunit hiso hframe mu)
  simpa only [currentRe, Complex.ofReal_re] using h

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The actual density-velocity current has zero directional divergence under the actual Dirac equation for a differentiable positive-density polar field and local actual matrix/frame conditions. -/
theorem polar_current_continuity {rho beta : E → ℝ} {L : E → Mat}
    {u : E → Fin 4 → Covector} {x : E}
    (hrho : DifferentiableAt ℝ rho x) (hbeta : DifferentiableAt ℝ beta x)
    (hL : DifferentiableAt ℝ L x) (hpos : 0 < rho x)
    (hunit : ∀ᶠ y in 𝓝 x, IsUnit (L y))
    (hiso : ∀ᶠ y in 𝓝 x, diracAdjoint (L y)*L y=1)
    (hframe : ∀ᶠ y in 𝓝 x, ∀ A, L y*gamma A*(L y)⁻¹=gammaExpansion (u y A))
    (directions : Fin 4 → E) (hbar m c : ℝ) (hhbar : hbar ≠ 0)
    (hDirac : jetEquation hbar m c (polarField rho beta L x)
      (fun mu => fderiv ℝ (polarField rho beta L) x (directions mu))) :
    (∑ mu, fderiv ℝ (fun y => rho y * velocity c (u y) mu) x (directions mu)) = 0 := by
  have hp : ∀ᶠ y in 𝓝 x, 0 < rho y := hrho.continuousAt.eventually (lt_mem_nhds hpos)
  have heq (mu : Fin 4) :
      (fun y => currentRe c (polarField rho beta L y) mu) =ᶠ[𝓝 x]
        (fun y => rho y * velocity c (u y) mu) := by
    filter_upwards [hp, hunit, hiso, hframe] with y hy hu hi hf
    exact polar_currentRe_eq_density_velocity (rho y) (beta y) c hy.le hu hi hf mu
  calc
    _ = ∑ mu, fderiv ℝ (fun y => currentRe c (polarField rho beta L y) mu) x (directions mu) := by
      apply Finset.sum_congr rfl
      intro mu _
      rw [(heq mu).fderiv_eq]
    _ = 0 := currentRe_conservation (differentiableAt_polarField hrho hbeta hL hpos)
      directions hbar m c hhbar hDirac

/-- A genuine flat-coordinate Dirac solution in the forward polar domain satisfies the actual continuity equation for rho times physical velocity. -/
theorem coordinate_polar_current_continuity {rho beta : Covector → ℝ} {L : Covector → Mat}
    {u : Covector → Fin 4 → Covector} {x : Covector}
    (hrho : DifferentiableAt ℝ rho x) (hbeta : DifferentiableAt ℝ beta x)
    (hL : DifferentiableAt ℝ L x) (hpos : 0 < rho x)
    (hunit : ∀ᶠ y in 𝓝 x, IsUnit (L y))
    (hiso : ∀ᶠ y in 𝓝 x, diracAdjoint (L y)*L y=1)
    (hframe : ∀ᶠ y in 𝓝 x, ∀ A, L y*gamma A*(L y)⁻¹=gammaExpansion (u y A))
    (hbar m c : ℝ) (hhbar : hbar ≠ 0)
    (hDirac : diracField hbar m c (polarField rho beta L) x = 0) :
    (∑ mu, fderiv ℝ (fun y => rho y * velocity c (u y) mu) x
      (DiracFieldDensity.coordinateDirections mu)) = 0 :=
  polar_current_continuity hrho hbeta hL hpos hunit hiso hframe _ hbar m c hhbar
    ((diracField_eq_zero_iff hbar m c _ x).mp hDirac)

end FoliationQM.PolarDiracCurrent
