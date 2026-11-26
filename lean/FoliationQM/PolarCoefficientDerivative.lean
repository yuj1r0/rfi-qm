module
public import FoliationQM.PolarSpinorDifferential
public import FoliationQM.CliffordCommutators

/-!
# Lorentz coefficients in the actual polar derivative

Source: v13 `lem:maurer_cartan`, the displayed spinor and adjoint derivatives.
The actual body connection is supplied in its real Lorentz-generator expansion,
exactly as in the source lemma. This expansion is a source-admissibility premise;
local Dirac isometry and gamma5 commutation alone do not imply Spin membership.
All field derivatives are the actual Frechet derivatives proved in the preceding
block. The conjugated generator sums and their opposite adjoint signs are
calculated from that expansion, with the full antisymmetric double-sum convention.
-/

@[expose] public section
noncomputable section
open scoped Matrix.Norms.Operator
open Filter Topology
namespace FoliationQM.PolarCoefficientDerivative
open DiracMatrices DiracAdjoint MatrixDifferential MaurerCartanDifferential
open PolarSpinorDifferential CliffordCommutators
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The actual conjugated Lorentz-generator sum with the source minus-i over four coefficient. -/
def expandedSpatial (M : Mat) (omega : Fin 4 → Fin 4 → ℝ) : Mat :=
  ∑ a, ∑ b, (-Complex.I * (omega a b : ℂ) / 4) • (M * sigma a b * M⁻¹)

/-- Conjugating the actual body generator expands into the source conjugated sigma matrices. -/
theorem conjugate_generator (M : Mat) (omega : Fin 4 → Fin 4 → ℝ) :
    M * generator omega * M⁻¹ = expandedSpatial M omega := by
  simp only [generator, expandedSpatial, Finset.mul_sum, Finset.sum_mul,
    mul_smul_comm, smul_mul_assoc]

/-- The actual spatial connection has the displayed generator sum when the actual body connection has the source expansion. -/
theorem spatial_eq_expanded {L : E → Mat} {x : E} (hunit : IsUnit (L x))
    (v : E) (omega : Fin 4 → Fin 4 → ℝ) (hbody : body L x v = generator omega) :
    spatial L x v = expandedSpatial (L x) omega := by
  rw [spatial_eq_conjugate_body hunit, hbody, conjugate_generator]

/-- Negating the conjugated connection changes the minus-i coefficient to plus-i without changing matrix order. -/
theorem neg_expandedSpatial (M : Mat) (omega : Fin 4 → Fin 4 → ℝ) :
    -expandedSpatial M omega =
      ∑ a, ∑ b, (Complex.I * (omega a b : ℂ) / 4) • (M * sigma a b * M⁻¹) := by
  simp only [expandedSpatial, ← Finset.sum_neg_distrib, ← neg_smul, neg_div, neg_mul]
  simp only [neg_neg]

/-- Actual polar differentiation with an actual body-generator expansion gives the source indexed spinor derivative. -/
theorem fderiv_polarField_coefficients {rho beta : E → ℝ} {L : E → Mat} {x : E}
    (hrho : DifferentiableAt ℝ rho x) (hbeta : DifferentiableAt ℝ beta x)
    (hL : DifferentiableAt ℝ L x) (hpos : 0 < rho x) (hunit : IsUnit (L x))
    (h5 : ∀ᶠ y in 𝓝 x, Commute (L y) gamma5) (v : E)
    (omega : Fin 4 → Fin 4 → ℝ) (hbody : body L x v = generator omega) :
    fderiv ℝ (polarField rho beta L) x v =
      (((fderiv ℝ (fun y => Real.log (rho y)) x v / 2 : ℝ) : ℂ) • (1 : Mat) +
        (Complex.I * (fderiv ℝ beta x v : ℂ) / 2) • gamma5 +
        ∑ a, ∑ b, (-Complex.I * (omega a b : ℂ) / 4) •
          (L x * sigma a b * (L x)⁻¹)).mulVec (polarField rho beta L x) := by
  rw [fderiv_polarField_source hrho hbeta hL hpos hunit h5,
    spatial_eq_expanded hunit v omega hbody]
  rfl

/-- Actual adjoint-row differentiation with the actual body expansion gives the source indexed plus-i connection term. -/
theorem fderiv_adjointField_coefficients {rho beta : E → ℝ} {L : E → Mat} {x : E}
    (hrho : DifferentiableAt ℝ rho x) (hbeta : DifferentiableAt ℝ beta x)
    (hL : DifferentiableAt ℝ L x) (hpos : 0 < rho x) (hunit : IsUnit (L x))
    (h5 : ∀ᶠ y in 𝓝 x, Commute (L y) gamma5)
    (hiso : ∀ᶠ y in 𝓝 x, diracAdjoint (L y) * L y = 1) (v : E)
    (omega : Fin 4 → Fin 4 → ℝ) (hbody : body L x v = generator omega) :
    fderiv ℝ (adjointField rho beta L) x v =
      Matrix.vecMul (adjointField rho beta L x)
        (((fderiv ℝ (fun y => Real.log (rho y)) x v / 2 : ℝ) : ℂ) • (1 : Mat) +
          (Complex.I * (fderiv ℝ beta x v : ℂ) / 2) • gamma5 +
          ∑ a, ∑ b, (Complex.I * (omega a b : ℂ) / 4) •
            (L x * sigma a b * (L x)⁻¹)) := by
  rw [fderiv_adjointField_source hrho hbeta hL hpos hunit h5 hiso,
    spatial_eq_expanded hunit v omega hbody, sub_eq_add_neg, neg_expandedSpatial]

end FoliationQM.PolarCoefficientDerivative
