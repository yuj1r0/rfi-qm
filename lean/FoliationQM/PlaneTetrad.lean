module

public import FoliationQM.RotorExponential
public import FoliationQM.DressedVelocity
public import Mathlib.Tactic.LinearCombination

/-!
# The actual Dirac tetrad under a spatial-plane rotor

Sources: v13 `thm:contact_period` (iii), `eq:rotor_compton_evolution`, and the
plane specialization of `lem:maurer_cartan`. The input theta is half the
physical tetrad angle. Every tetrad matrix is actual rotor conjugation of a
Dirac matrix, and the real coefficient rows reconstruct that conjugation.
The coefficient-row orthonormality uses the explicit Minkowski form (+---).
-/

@[expose] public section
noncomputable section
namespace FoliationQM.PlaneTetrad
open DiracMatrices PlaneRotor RotorExponential

/-- The actual rotor-conjugated Dirac frame, with theta the half physical angle. -/
def tetrad (theta : ℝ) (a : Fin 4) : Mat := rotor theta * gamma a * rotor (-theta)

/-- The actual real frame coefficient rows for a spatial 1–2 rotation through physical angle 2 theta. -/
def coefficients (theta : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![1, 0, 0, 0;
     0, Real.cos (2 * theta), Real.sin (2 * theta), 0;
     0, -Real.sin (2 * theta), Real.cos (2 * theta), 0;
     0, 0, 0, 1]

/-- The displayed conjugation uses the actual nonsingular matrix inverse of the rotor. -/
theorem tetrad_eq_conjugation (theta : ℝ) (a : Fin 4) :
    tetrad theta a = rotor theta * gamma a * (rotor theta)⁻¹ := by
  rw [rotor_inv]
  rfl

/-- A pi shift of the half-angle preserves each actual frame matrix because both rotor signs reverse. -/
theorem tetrad_add_pi (theta : ℝ) (a : Fin 4) :
    tetrad (theta + Real.pi) a = tetrad theta a := by
  have h : -(theta + Real.pi) = -theta - Real.pi := by ring
  rw [tetrad, rotor_add_pi, h, rotor_sub_pi, neg_mul, neg_mul_neg]
  rfl

/-- The full actual Dirac tetrad family is periodic with half-angle period pi. -/
theorem tetrad_periodic : Function.Periodic tetrad Real.pi := by
  intro theta
  funext a
  exact tetrad_add_pi theta a

/-- At zero half-angle the actual tetrad is the original Dirac frame. -/
theorem tetrad_zero (a : Fin 4) : tetrad 0 a = gamma a := by
  simp [tetrad]

private theorem cosine_sub_sine (theta : ℝ) :
    (Real.cos theta : ℂ) - (Real.sin theta : ℂ) * Complex.I =
      Complex.exp (-Complex.I * theta) := by
  simpa only [mul_neg, sub_eq_add_neg] using negative_phase_identity theta

/-- One actual rotated gamma1 matrix entry carries the phase exp(-2i theta), detecting the doubled physical angle. -/
theorem tetrad_one_entry (theta : ℝ) :
    tetrad theta 1 0 3 = Complex.exp (-Complex.I * (2 * theta)) := by
  have he : tetrad theta 1 0 3 =
      ((Real.cos theta : ℂ) - (Real.sin theta : ℂ) * Complex.I) *
        ((Real.cos theta : ℂ) - (Real.sin theta : ℂ) * Complex.I) := by
    simp [tetrad, rotor_diagonal, gamma, Matrix.mul_apply,
      Matrix.diagonal_apply, sub_eq_add_neg]
  rw [he, cosine_sub_sine, ← Complex.exp_add]
  congr 1
  ring

/-- Actual spatial-plane rotor conjugation fixes the temporal Dirac matrix. -/
theorem tetrad_time (theta : ℝ) : tetrad theta 0 = gamma 0 := by
  have h := Complex.cos_sq_add_sin_sq (theta : ℂ)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [tetrad, rotor_diagonal, gamma, Matrix.mul_apply, Matrix.diagonal_apply] <;>
    ring_nf <;> norm_num <;>
    first | linear_combination h | linear_combination -h

/-- The actual first spatial frame matrix rotates by physical angle 2 theta with positive gamma2 component. -/
theorem tetrad_one (theta : ℝ) :
    tetrad theta 1 = (Real.cos (2 * theta) : ℂ) • gamma 1 +
      (Real.sin (2 * theta) : ℂ) • gamma 2 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [tetrad, rotor_diagonal, gamma, Matrix.mul_apply, Matrix.diagonal_apply,
      Real.cos_two_mul', Real.sin_two_mul] <;>
    ring_nf <;> norm_num <;> simp only [sub_eq_add_neg]

/-- The actual second spatial frame matrix rotates by physical angle 2 theta with negative gamma1 component. -/
theorem tetrad_two (theta : ℝ) :
    tetrad theta 2 = (-(Real.sin (2 * theta) : ℂ)) • gamma 1 +
      (Real.cos (2 * theta) : ℂ) • gamma 2 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [tetrad, rotor_diagonal, gamma, Matrix.mul_apply, Matrix.diagonal_apply,
      Real.cos_two_mul', Real.sin_two_mul] <;>
    ring_nf <;> norm_num <;> simp only [sub_eq_add_neg]

/-- Actual spatial-plane rotor conjugation fixes the third spatial Dirac matrix. -/
theorem tetrad_three (theta : ℝ) : tetrad theta 3 = gamma 3 := by
  have h := Complex.cos_sq_add_sin_sq (theta : ℂ)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [tetrad, rotor_diagonal, gamma, Matrix.mul_apply, Matrix.diagonal_apply] <;>
    ring_nf <;> norm_num <;>
    first | linear_combination h | linear_combination -h

/-- The proved actual conjugated tetrad is reconstructed by its explicit real coefficient rows in the original Dirac basis. -/
theorem tetrad_reconstruction (theta : ℝ) (a : Fin 4) :
    tetrad theta a = ∑ b : Fin 4, (coefficients theta a b : ℂ) • gamma b := by
  fin_cases a <;>
    simp [coefficients, Fin.sum_univ_succ, tetrad_time,
      tetrad_one, tetrad_two, tetrad_three] <;>
    ext i j <;> fin_cases i <;> fin_cases j <;> simp [gamma]

/-- The actual real coefficient rows are orthonormal for the explicit Minkowski form of signature (+---). -/
theorem coefficients_orthonormal (theta : ℝ) (a b : Fin 4) :
    minkowski (coefficients theta a) (coefficients theta b) =
      if a = b then (if a = 0 then 1 else -1) else 0 := by
  have h := Real.cos_sq_add_sin_sq (2 * theta)
  fin_cases a <;> fin_cases b <;> simp [coefficients, minkowski] <;> nlinarith [h]

end FoliationQM.PlaneTetrad
