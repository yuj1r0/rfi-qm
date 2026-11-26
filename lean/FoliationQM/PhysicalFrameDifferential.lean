module

public import FoliationQM.RicciRotation
public import FoliationQM.PolarVectorGeometry
/-!
# Actual derivatives of the physical source tetrad

Source: v13 `eq:mc_velocity_spin_identity` and the velocity/spin derivative
formulas in its proof. The physical tetrad uses the source lower-gamma
coefficients, equivalently the inverse columns of the actual upper-gamma
expansion. Both frame and coordinate metric signs are retained.

A local actual matrix/frame expansion, differentiable real coefficients,
and an actual body-generator expansion are inputs. RicciRotation derives
the source coefficient transport from genuine Frechet differentiation.
Here that transport gives the actual time-row, spin-row and c-scaled
velocity derivatives; none of their final derivative identities is an
assumption. Orthonormality comes from the actual Clifford matrix expansion.
The results do not assert existence of a real frame expansion for arbitrary
matrices, time orientation, or a global spin reconstruction.
-/

@[expose] public section
noncomputable section
open scoped Matrix.Norms.Operator
open Filter Topology
namespace FoliationQM.PhysicalFrameDifferential
open DiracMatrices DiracAdjoint RealLorentzFrame RicciRotation
open PolarVectorGeometry MaurerCartanDifferential CliffordCommutators

/-- The physical source tetrad is the lower-gamma coefficient row, with both Minkowski index signs included. -/
def physicalFrame (u : Fin 4 → Covector) (A : Fin 4) : Covector := sourceFrame u A

/-- Every physical source tetrad row equals the corresponding column of the derived inverse real frame. -/
theorem physicalFrame_eq_inverseColumn (u : Fin 4 → Covector) (A : Fin 4) :
    physicalFrame u A = fun mu => inverseCoefficients u mu A := by
  funext mu
  simp only [physicalFrame, sourceFrame, inverseCoefficients]
  ring

/-- The physical temporal tetrad row is the established dimensionless time vector. -/
theorem physicalFrame_zero_eq_timeVector (u : Fin 4 → Covector) :
    physicalFrame u 0 = timeVector u := physicalFrame_eq_inverseColumn u 0

/-- The physical third spatial tetrad row is the established spin vector. -/
theorem physicalFrame_three_eq_spinVector (u : Fin 4 → Covector) :
    physicalFrame u 3 = spinVector u := physicalFrame_eq_inverseColumn u 3

/-- The physical velocity is exactly c times the physical temporal tetrad row. -/
theorem velocity_eq_smul_physicalFrame_zero (c : ℝ) (u : Fin 4 → Covector) :
    velocity c u = c • physicalFrame u 0 := by
  rw [physicalFrame_zero_eq_timeVector]
  rfl

/-- An actual invertible real gamma-frame expansion derives the Minkowski orthonormality of the physical source tetrad. -/
theorem physicalFrame_orthonormal {L : Mat} {u : Fin 4 → Covector}
    (hunit : IsUnit L) (hframe : ∀A, L*gamma A*L⁻¹=gammaExpansion (u A)) (A B : Fin 4) :
    minkowski (physicalFrame u A) (physicalFrame u B) = if A=B then sign A else 0 := by
  rw [physicalFrame_eq_inverseColumn, physicalFrame_eq_inverseColumn]
  exact inverse_columns_orthonormal hunit hframe A B

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Differentiability of the actual coefficient fields gives differentiability of each physical tetrad row. -/
theorem differentiableAt_physicalFrame {u : E → Fin 4 → Covector} {x : E}
    (hu : ∀ A mu, DifferentiableAt ℝ (fun y => u y A mu) x) (A : Fin 4) :
    DifferentiableAt ℝ (fun y => physicalFrame (u y) A) x := by
  apply differentiableAt_pi.mpr
  intro mu
  exact (hu A mu).const_mul (sign A*sign mu)

/-- The actual physical time-vector field is differentiable when the frame coefficient fields are differentiable. -/
theorem differentiableAt_timeVector {u : E → Fin 4 → Covector} {x : E}
    (hu : ∀ A mu, DifferentiableAt ℝ (fun y => u y A mu) x) :
    DifferentiableAt ℝ (fun y => timeVector (u y)) x := by
  simpa only [physicalFrame_zero_eq_timeVector] using differentiableAt_physicalFrame hu 0

/-- The actual physical spin-vector field is differentiable when the frame coefficient fields are differentiable. -/
theorem differentiableAt_spinVector {u : E → Fin 4 → Covector} {x : E}
    (hu : ∀ A mu, DifferentiableAt ℝ (fun y => u y A mu) x) :
    DifferentiableAt ℝ (fun y => spinVector (u y)) x := by
  simpa only [physicalFrame_three_eq_spinVector] using differentiableAt_physicalFrame hu 3

/-- The actual physical tetrad derivative is the signed source transport derived from the local matrix expansion and body generator. -/
theorem fderiv_physicalFrame {L : E → Mat} {u : E → Fin 4 → Covector} {x : E}
    (hL : DifferentiableAt ℝ L x) (hunit : IsUnit (L x))
    (hu : ∀ A mu, DifferentiableAt ℝ (fun y => u y A mu) x)
    (hframe : ∀ᶠ y in 𝓝 x, ∀ A, L y*gamma A*(L y)⁻¹=gammaExpansion (u y A))
    (v : E) (omega : Fin 4 → Fin 4 → ℝ) (hanti : ∀ a b, omega a b = -omega b a)
    (hbody : body L x v=generator omega) (A : Fin 4) :
    fderiv ℝ (fun y => physicalFrame (u y) A) x v =
      fun mu => ∑ a, sourceOmega omega a A*sign A*physicalFrame (u x) a mu := by
  funext mu
  have hcoord := congrArg (fun T : E →L[ℝ] ℝ => T v)
    (fderiv_apply (differentiableAt_physicalFrame hu A) mu)
  change fderiv ℝ (fun y => physicalFrame (u y) A mu) x v =
    (fderiv ℝ (fun y => physicalFrame (u y) A) x v) mu at hcoord
  rw [← hcoord]
  exact sourceFrame_transport hL hunit hu hframe v omega hanti hbody A mu

private theorem antisymmetric_diagonal {omega : Fin 4 → Fin 4 → ℝ}
    (hanti : ∀ a b, omega a b = -omega b a) (a : Fin 4) : omega a a=0 := by
  have h := hanti a a
  linarith

/-- The actual temporal source-row derivative is the sum of the three positive boost coefficients times the spatial rows. -/
theorem fderiv_physicalFrame_zero {L : E → Mat} {u : E → Fin 4 → Covector} {x : E}
    (hL : DifferentiableAt ℝ L x) (hunit : IsUnit (L x))
    (hu : ∀ A mu, DifferentiableAt ℝ (fun y => u y A mu) x)
    (hframe : ∀ᶠ y in 𝓝 x, ∀ A, L y*gamma A*(L y)⁻¹=gammaExpansion (u y A))
    (v : E) (omega : Fin 4 → Fin 4 → ℝ) (hanti : ∀ a b, omega a b = -omega b a)
    (hbody : body L x v=generator omega) :
    fderiv ℝ (fun y => physicalFrame (u y) 0) x v =
      omega 0 1 • physicalFrame (u x) 1 + omega 0 2 • physicalFrame (u x) 2 +
        omega 0 3 • physicalFrame (u x) 3 := by
  rw [fderiv_physicalFrame hL hunit hu hframe v omega hanti hbody]
  funext mu
  simp [sourceOmega, sign, Fin.sum_univ_succ, antisymmetric_diagonal hanti,
    hanti 1 0, hanti 2 0, hanti 3 0]
  ring

/-- The actual spin-row derivative has the positive temporal boost term and the two negative spatial rotation terms. -/
theorem fderiv_physicalFrame_three {L : E → Mat} {u : E → Fin 4 → Covector} {x : E}
    (hL : DifferentiableAt ℝ L x) (hunit : IsUnit (L x))
    (hu : ∀ A mu, DifferentiableAt ℝ (fun y => u y A mu) x)
    (hframe : ∀ᶠ y in 𝓝 x, ∀ A, L y*gamma A*(L y)⁻¹=gammaExpansion (u y A))
    (v : E) (omega : Fin 4 → Fin 4 → ℝ) (hanti : ∀ a b, omega a b = -omega b a)
    (hbody : body L x v=generator omega) :
    fderiv ℝ (fun y => physicalFrame (u y) 3) x v =
      omega 0 3 • physicalFrame (u x) 0 - omega 1 3 • physicalFrame (u x) 1 -
        omega 2 3 • physicalFrame (u x) 2 := by
  rw [fderiv_physicalFrame hL hunit hu hframe v omega hanti hbody]
  funext mu
  simp [sourceOmega, sign, Fin.sum_univ_succ, antisymmetric_diagonal hanti,
    sub_eq_add_neg]
  ring

/-- The actual established time-vector derivative has the three source boost components. -/
theorem fderiv_timeVector {L : E → Mat} {u : E → Fin 4 → Covector} {x : E}
    (hL : DifferentiableAt ℝ L x) (hunit : IsUnit (L x))
    (hu : ∀ A mu, DifferentiableAt ℝ (fun y => u y A mu) x)
    (hframe : ∀ᶠ y in 𝓝 x, ∀ A, L y*gamma A*(L y)⁻¹=gammaExpansion (u y A))
    (v : E) (omega : Fin 4 → Fin 4 → ℝ) (hanti : ∀ a b, omega a b = -omega b a)
    (hbody : body L x v=generator omega) :
    fderiv ℝ (fun y => timeVector (u y)) x v =
      omega 0 1 • physicalFrame (u x) 1 + omega 0 2 • physicalFrame (u x) 2 +
        omega 0 3 • physicalFrame (u x) 3 := by
  simpa only [physicalFrame_zero_eq_timeVector] using
    fderiv_physicalFrame_zero hL hunit hu hframe v omega hanti hbody

/-- The actual established spin-vector derivative has the exact source boost and rotation signs. -/
theorem fderiv_spinVector {L : E → Mat} {u : E → Fin 4 → Covector} {x : E}
    (hL : DifferentiableAt ℝ L x) (hunit : IsUnit (L x))
    (hu : ∀ A mu, DifferentiableAt ℝ (fun y => u y A mu) x)
    (hframe : ∀ᶠ y in 𝓝 x, ∀ A, L y*gamma A*(L y)⁻¹=gammaExpansion (u y A))
    (v : E) (omega : Fin 4 → Fin 4 → ℝ) (hanti : ∀ a b, omega a b = -omega b a)
    (hbody : body L x v=generator omega) :
    fderiv ℝ (fun y => spinVector (u y)) x v =
      omega 0 3 • physicalFrame (u x) 0 - omega 1 3 • physicalFrame (u x) 1 -
        omega 2 3 • physicalFrame (u x) 2 := by
  simpa only [physicalFrame_three_eq_spinVector] using
    fderiv_physicalFrame_three hL hunit hu hframe v omega hanti hbody

/-- The genuine derivative of the physical velocity is c times the genuine time-vector derivative. -/
theorem fderiv_velocity_eq_smul_timeVector {u : E → Fin 4 → Covector} {x : E}
    (hu : ∀ A mu, DifferentiableAt ℝ (fun y => u y A mu) x) (c : ℝ) (v : E) :
    fderiv ℝ (fun y => velocity c (u y)) x v =
      c • fderiv ℝ (fun y => timeVector (u y)) x v := by
  have hd := congrArg (fun T : E →L[ℝ] Covector => T v)
    ((differentiableAt_timeVector hu).hasFDerivAt.const_smul c).fderiv
  simpa only [velocity, Pi.smul_apply, smul_eq_mul, _root_.smul_apply] using! hd

/-- The actual physical velocity derivative is c times the source boost combination derived from the actual matrix/frame fields. -/
theorem fderiv_velocity {L : E → Mat} {u : E → Fin 4 → Covector} {x : E}
    (hL : DifferentiableAt ℝ L x) (hunit : IsUnit (L x))
    (hu : ∀ A mu, DifferentiableAt ℝ (fun y => u y A mu) x)
    (hframe : ∀ᶠ y in 𝓝 x, ∀ A, L y*gamma A*(L y)⁻¹=gammaExpansion (u y A))
    (v : E) (omega : Fin 4 → Fin 4 → ℝ) (hanti : ∀ a b, omega a b = -omega b a)
    (hbody : body L x v=generator omega) (c : ℝ) :
    fderiv ℝ (fun y => velocity c (u y)) x v =
      c • (omega 0 1 • physicalFrame (u x) 1 + omega 0 2 • physicalFrame (u x) 2 +
        omega 0 3 • physicalFrame (u x) 3) := by
  rw [fderiv_velocity_eq_smul_timeVector hu c v,
    fderiv_timeVector hL hunit hu hframe v omega hanti hbody]

end FoliationQM.PhysicalFrameDifferential
