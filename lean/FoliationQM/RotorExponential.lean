module

public import FoliationQM.PlaneRotor
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.Matrix.Normed

/-!
# The genuine matrix exponential of the spatial-plane rotor

Sources: v13 `thm:contact_period` (iii), `eq:rotor_compton_evolution`, and
the plane specialization of `lem:maurer_cartan`. The parameter theta is half
the tetrad angle. The analytic operation is Mathlib's actual `NormedSpace.exp`;
its equality with the trigonometric rotor follows from the actual diagonal
matrix exponential and the complex exponential, not from a replacement
exponential definition.

The operator-norm scope agrees with the subsequent analytic rotor modules.
The matrix inverse below is the actual nonsingular matrix inverse. Identities
with an arbitrary initial matrix do not presume its invertibility; cancellation
of its inverse explicitly requires that initial matrix to be a unit.
-/

@[expose] public section
noncomputable section

open scoped Matrix.Norms.Operator

namespace FoliationQM.RotorExponential
open DiracMatrices PlaneRotor

private theorem scalar_exp_negative (theta : ℝ) :
    NormedSpace.exp (-((theta : ℂ) * Complex.I)) =
      (Real.cos theta : ℂ) - (Real.sin theta : ℂ) * Complex.I := by
  rw [← Complex.exp_eq_exp_ℂ]
  simpa [mul_comm, sub_eq_add_neg] using (negative_phase_identity theta).symm

private theorem scalar_exp_positive (theta : ℝ) :
    NormedSpace.exp ((theta : ℂ) * Complex.I) =
      (Real.cos theta : ℂ) + (Real.sin theta : ℂ) * Complex.I := by
  rw [← Complex.exp_eq_exp_ℂ]
  exact Complex.exp_ofReal_mul_I theta

/-- The genuine matrix exponential of the plane generator is the proved trigonometric Dirac rotor. -/
theorem exp_generator (theta : ℝ) :
    NormedSpace.exp ((theta : ℂ) • planeGenerator) = rotor theta := by
  rw [planeGenerator_diagonal, ← Matrix.diagonal_smul, Matrix.exp_diagonal, rotor_diagonal]
  congr 1
  ext i
  fin_cases i <;>
    simp [Pi.coe_exp, scalar_exp_negative, scalar_exp_positive]

/-- The actual matrix inverse of a plane rotor is the rotor at the negative half-angle. -/
theorem rotor_inv (theta : ℝ) : (rotor theta)⁻¹ = rotor (-theta) := by
  rw [← exp_generator theta, ← Matrix.exp_neg, ← exp_generator (-theta)]
  congr 1
  simp

/-- The genuine sigma12 exponential with source negative-i orientation equals the same actual rotor. -/
theorem exp_sigma12 (theta : ℝ) :
    NormedSpace.exp ((-Complex.I * theta) • sigma 1 2) = rotor theta := by
  rw [sigma12_eq_I_smul_generator, smul_smul]
  have h : (-Complex.I * (theta : ℂ)) * Complex.I = theta := by
    calc
      _ = -(Complex.I * Complex.I) * theta := by ring
      _ = _ := by simp
  rw [h, exp_generator]

/-- The actual matrix exponential acts on the reference rest spinor as the negative complex phase exp(-i theta). -/
theorem exp_generator_mulVec_restSpinor (theta : ℝ) :
    (NormedSpace.exp ((theta : ℂ) • planeGenerator)).mulVec restSpinor =
      Complex.exp (-Complex.I * theta) • restSpinor := by
  rw [exp_generator, rotor_mulVec_restSpinor]

/-- An arbitrary initial matrix multiplying the genuine exponential gives the same actual rotor evolution formula. -/
theorem initial_mul_exp_generator (L0 : Mat) (theta : ℝ) :
    L0 * NormedSpace.exp ((theta : ℂ) • planeGenerator) = L0 * rotor theta := by
  rw [exp_generator]

/-- The source initial-matrix exponential formula equals its displayed cosine-plus-generator-sine expression. -/
theorem initial_mul_exp_trigonometric (L0 : Mat) (theta : ℝ) :
    L0 * NormedSpace.exp ((theta : ℂ) • planeGenerator) =
      L0 * ((Real.cos theta : ℂ) • 1 + (Real.sin theta : ℂ) • planeGenerator) := by
  rw [exp_generator]
  rfl

/-- The genuine exponential of the lowered-index source generator equals the same actual rotor. -/
theorem exp_lower_generator (theta : ℝ) :
    NormedSpace.exp ((theta : ℂ) • (gammaLower 1 * gammaLower 2)) = rotor theta := by
  rw [gammaLower_planeGenerator, exp_generator]

/-- Multiplying the rotor by its actual nonsingular matrix inverse gives the identity. -/
theorem rotor_mul_inv (theta : ℝ) : rotor theta * (rotor theta)⁻¹ = 1 := by
  rw [rotor_inv, rotor_mul_negative]

/-- The actual nonsingular matrix inverse is also a left inverse of the rotor. -/
theorem rotor_inv_mul (theta : ℝ) : (rotor theta)⁻¹ * rotor theta = 1 := by
  rw [rotor_inv, rotor_negative_mul]

/-- An arbitrary initial matrix transports the actual exponential rest-spinor phase by its ordinary spinor action. -/
theorem initial_exp_mulVec_restSpinor (L0 : Mat) (theta : ℝ) :
    (L0 * NormedSpace.exp ((theta : ℂ) • planeGenerator)).mulVec restSpinor =
      Complex.exp (-Complex.I * theta) • L0.mulVec restSpinor := by
  rw [← Matrix.mulVec_mulVec, exp_generator_mulVec_restSpinor, Matrix.mulVec_smul]

/-- For an invertible initial matrix, the actual relative evolution acts on the rest spinor by exp(-i theta). -/
theorem relative_exp_mulVec_restSpinor (L0 : Mat) (hL0 : IsUnit L0) (theta : ℝ) :
    (L0⁻¹ * (L0 * NormedSpace.exp ((theta : ℂ) • planeGenerator))).mulVec restSpinor =
      Complex.exp (-Complex.I * theta) • restSpinor := by
  rw [← mul_assoc, Matrix.nonsing_inv_mul L0 (L0.isUnit_iff_isUnit_det.mp hL0), one_mul,
    exp_generator_mulVec_restSpinor]

end FoliationQM.RotorExponential
