module

public import FoliationQM.DiracMatrices
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Tactic.Module
public import Mathlib.Tactic.Ring

/-!
# The explicit spatial-plane Dirac rotor

Source: v13 `thm:contact_period` (iii), `eq:rotor_compton_evolution`,
and the plane-rotation specialization of `lem:maurer_cartan`.
The parameter theta is half the tetrad rotation angle. The rotor is an actual
complex four-by-four matrix, formed from the concrete Clifford generator.
Its group law follows from trigonometric addition and the proved generator
square. This module establishes matrix algebra and the rest-spinor phase;
matrix exponentiation, differential equations and full spin-group membership
are separate results.
-/

@[expose] public section
noncomputable section

namespace FoliationQM.PlaneRotor
open DiracMatrices

/-- The actual plane rotor at half tetrad angle theta, with explicit complex scalar coefficients. -/
def rotor (theta : ℝ) : Mat :=
  (Real.cos theta : ℂ) • 1 + (Real.sin theta : ℂ) • planeGenerator

/-- At zero half-angle the plane rotor is the identity matrix. -/
@[simp]
theorem rotor_zero : rotor 0 = 1 := by
  simp [rotor]

/-- Trigonometric angle addition gives the actual matrix group law. -/
theorem rotor_add (a b : ℝ) : rotor (a + b) = rotor a * rotor b := by
  simp only [rotor, Real.cos_add, Real.sin_add, Complex.ofReal_sub,
    Complex.ofReal_mul, Complex.ofReal_add, add_mul, mul_add, smul_mul_assoc,
    mul_smul_comm, one_mul, mul_one, generator_sq, smul_neg]
  module

/-- Reversing the half-angle reverses the generator term and preserves the scalar term. -/
theorem rotor_neg (theta : ℝ) :
    rotor (-theta) = (Real.cos theta : ℂ) • 1 - (Real.sin theta : ℂ) • planeGenerator := by
  simp [rotor, sub_eq_add_neg]

/-- The rotor at the negative half-angle is an actual right inverse. -/
theorem rotor_mul_negative (theta : ℝ) : rotor theta * rotor (-theta) = 1 := by
  rw [← rotor_add, add_neg_cancel, rotor_zero]

/-- The rotor at the negative half-angle is an actual left inverse. -/
theorem rotor_negative_mul (theta : ℝ) : rotor (-theta) * rotor theta = 1 := by
  rw [← rotor_add, neg_add_cancel, rotor_zero]

/-- The actual rotor is a matrix unit, with inverse given by the negative half-angle rotor. -/
theorem rotor_isUnit (theta : ℝ) : IsUnit (rotor theta) :=
  ⟨⟨rotor theta, rotor (-theta), rotor_mul_negative theta, rotor_negative_mul theta⟩, rfl⟩

/-- Rotors in this fixed plane commute, as follows from addition of their real half-angles. -/
theorem rotor_commute (a b : ℝ) : Commute (rotor a) (rotor b) := by
  change rotor a * rotor b = rotor b * rotor a
  rw [← rotor_add, ← rotor_add, add_comm]

/-- The exact diagonal entries of the actual Dirac plane rotor in the chosen representation. -/
theorem rotor_diagonal (theta : ℝ) :
    rotor theta = Matrix.diagonal
      ![(Real.cos theta : ℂ) - (Real.sin theta : ℂ) * Complex.I,
        (Real.cos theta : ℂ) + (Real.sin theta : ℂ) * Complex.I,
        (Real.cos theta : ℂ) - (Real.sin theta : ℂ) * Complex.I,
        (Real.cos theta : ℂ) + (Real.sin theta : ℂ) * Complex.I] := by
  rw [rotor, planeGenerator_diagonal]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal, sub_eq_add_neg]

/-- Euler's identity identifies the negative complex phase carried by the reference rest spinor. -/
theorem negative_phase_identity (theta : ℝ) :
    (Real.cos theta : ℂ) + (Real.sin theta : ℂ) * (-Complex.I) =
      Complex.exp (-Complex.I * theta) := by
  have h := Complex.exp_ofReal_mul_I (-theta)
  simp only [Complex.ofReal_neg, Real.cos_neg, Real.sin_neg] at h
  rw [show -Complex.I * (theta : ℂ) = -(theta : ℂ) * Complex.I by ring, h]
  ring

/-- The actual rotor action on the supplied rest spinor is exp(-i theta) times that spinor. -/
theorem rotor_mulVec_restSpinor (theta : ℝ) :
    (rotor theta).mulVec restSpinor = Complex.exp (-Complex.I * theta) • restSpinor := by
  rw [rotor, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec,
    Matrix.one_mulVec, generator_mulVec_restSpinor, smul_smul, ← add_smul,
    negative_phase_identity]

/-- A half-angle of pi gives minus the identity matrix, the rotor double-cover sign. -/
theorem rotor_pi : rotor Real.pi = -1 := by
  simp [rotor]

/-- A half-angle of minus pi has the same minus-identity value. -/
theorem rotor_neg_pi : rotor (-Real.pi) = -1 := by
  simp [rotor]

/-- Advancing the half-angle by pi reverses the sign of the actual rotor. -/
theorem rotor_add_pi (theta : ℝ) : rotor (theta + Real.pi) = -rotor theta := by
  rw [rotor_add, rotor_pi, mul_neg_one]

/-- Retreating the half-angle by pi also reverses the sign of the actual rotor. -/
theorem rotor_sub_pi (theta : ℝ) : rotor (theta - Real.pi) = -rotor theta := by
  rw [sub_eq_add_neg, rotor_add, rotor_neg_pi, mul_neg_one]

/-- A full two-pi half-angle turn gives the identity matrix. -/
theorem rotor_two_pi : rotor (2 * Real.pi) = 1 := by
  simp [rotor]

/-- Advancing the half-angle by two pi leaves the actual rotor unchanged. -/
theorem rotor_add_two_pi (theta : ℝ) : rotor (theta + 2 * Real.pi) = rotor theta := by
  rw [rotor_add, rotor_two_pi, mul_one]

/-- The actual matrix-valued rotor is periodic with half-angle period two pi. -/
theorem rotor_periodic : Function.Periodic rotor (2 * Real.pi) := rotor_add_two_pi

/-- The actual invertible rotor matrix is never the zero matrix. -/
theorem rotor_ne_zero (theta : ℝ) : rotor theta ≠ 0 := by
  intro h
  have hi := rotor_mul_negative theta
  rw [h, zero_mul] at hi
  exact zero_ne_one hi

end FoliationQM.PlaneRotor
