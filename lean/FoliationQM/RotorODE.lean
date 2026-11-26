module

public import FoliationQM.RotorEvolution
public import FoliationQM.RotorExponential
public import Mathlib.Analysis.Calculus.MeanValue

/-!
# Uniqueness of the actual constant-plane rotor ODE

Source: v13 `thm:contact_period` (iii), `eq:rotor_compton_evolution`,
and the fixed-plane specialization of `lem:maurer_cartan`. The equation is
an actual real HasDerivAt equation for complex four-by-four matrices. Right
multiplication by the opposite half-angle rotor gives an actual derivative
of zero. Mathlib's mean value theorem then identifies every global solution
with the explicit evolution from its initial value, and hence with the
actual matrix exponential.

No invertibility is needed for ODE uniqueness. It is imposed explicitly when
canceling the initial matrix to obtain the source normalized rest-spinor
phase. Matrix calculus uses the same Matrix.Norms.Operator normed-algebra
scope as RotorEvolution and RotorExponential. These statements concern this
fixed plane and do not assert a general spin-group evolution theorem.
-/

@[expose] public section

noncomputable section
open scoped Matrix.Norms.Operator
namespace FoliationQM.RotorODE
open DiracMatrices PlaneRotor RotorEvolution

/-- The actual source constant-plane rotor ODE with fixed real tetrad angular rate. -/
def Solves (L : ℝ → Mat) (omega : ℝ) : Prop :=
  ∀t, HasDerivAt L (((omega / 2 : ℝ) : ℂ) • (L t * planeGenerator)) t

/-- Right multiplication by the opposite half-angle rotor removes the candidate rotation. -/
def removeRotation (L : ℝ → Mat) (omega t : ℝ) : Mat :=
  L t * rotor (-omega * t / 2)

/-- The actual generator-form ODE is exactly the source negative-i sigma12 equation. -/
theorem solves_iff_sigma (L : ℝ → Mat) (omega : ℝ) :
    Solves L omega ↔ ∀t, HasDerivAt L
      ((-Complex.I * (omega : ℂ) / 2) • (L t * sigma 1 2)) t := by
  simp only [Solves, generator_rhs_eq_sigma_rhs]

/-- The explicitly differentiated arbitrary-initial-matrix evolution solves the actual source ODE. -/
theorem evolution_solves (L0 : Mat) (omega : ℝ) : Solves (evolution L0 omega) omega :=
  fun t => hasDerivAt_evolution L0 omega t

/-- An actual ODE solution multiplied by the opposite rotor has actual real derivative zero. -/
theorem hasDerivAt_removeRotation {L : ℝ → Mat} {omega : ℝ} (hL : Solves L omega)
    (t : ℝ) : HasDerivAt (removeRotation L omega) 0 t := by
  have hp := (hL t).mul (hasDerivAt_scaled_rotor (-omega) t)
  have he : (L t * planeGenerator) * rotor (-omega * t / 2) =
      L t * (rotor (-omega * t / 2) * planeGenerator) := by
    rw [mul_assoc, (rotor_generator_commute _).symm.eq]
  have hn : (((-omega / 2 : ℝ) : ℂ)) = -(((omega / 2 : ℝ) : ℂ)) := by
    push_cast
    ring
  apply hp.congr_deriv
  simp only [smul_mul_assoc, mul_smul_comm, he, hn, neg_smul, mul_neg, add_neg_cancel]

/-- The mean value theorem makes the derivative-zero rotated-back solution equal its initial matrix. -/
theorem removeRotation_constant {L : ℝ → Mat} {omega : ℝ} (hL : Solves L omega)
    (t : ℝ) : removeRotation L omega t = L 0 := by
  have h := is_const_of_deriv_eq_zero
    (fun s => (hasDerivAt_removeRotation hL s).differentiableAt)
    (fun s => (hasDerivAt_removeRotation hL s).deriv) t 0
  simpa [removeRotation] using h

/-- Every actual global solution of the constant-plane ODE equals the explicit evolution from its initial matrix. -/
theorem solution_eq_evolution {L : ℝ → Mat} {omega : ℝ} (hL : Solves L omega)
    (t : ℝ) : L t = evolution (L 0) omega t := by
  have h := congrArg (fun A : Mat => A * rotor (omega * t / 2)) (removeRotation_constant hL t)
  have ht : -omega * t / 2 = -(omega * t / 2) := by ring
  simpa only [removeRotation, ht, mul_assoc, rotor_negative_mul, mul_one, evolution] using h

/-- An actual source ODE solution with prescribed initial value equals the explicit evolution. -/
theorem solution_eq_of_initial {L : ℝ → Mat} {omega : ℝ} {L0 : Mat}
    (hL : Solves L omega) (h0 : L 0 = L0) (t : ℝ) : L t = evolution L0 omega t := by
  rw [solution_eq_evolution hL, h0]

/-- Two actual source ODE solutions agreeing initially agree as matrix-valued functions. -/
theorem solution_unique {L M : ℝ → Mat} {omega : ℝ}
    (hL : Solves L omega) (hM : Solves M omega) (h0 : L 0 = M 0) : L = M := by
  funext t
  rw [solution_eq_evolution hL, solution_eq_evolution hM, h0]

/-- The initial-value problem characterizes exactly the explicit matrix evolution. -/
theorem solves_initial_iff (L : ℝ → Mat) (L0 : Mat) (omega : ℝ) :
    (Solves L omega ∧ L 0 = L0) ↔ L = evolution L0 omega := by
  constructor
  · rintro ⟨hL,h0⟩
    funext t
    exact solution_eq_of_initial hL h0 t
  · rintro rfl
    exact ⟨evolution_solves L0 omega,initial_evolution L0 omega⟩

/-- Every actual ODE solution equals the source formula with the genuine normed-space matrix exponential. -/
theorem solution_eq_exponential {L : ℝ → Mat} {omega : ℝ} (hL : Solves L omega)
    (t : ℝ) : L t = L 0 * NormedSpace.exp (((omega * t / 2 : ℝ) : ℂ) • planeGenerator) := by
  rw [RotorExponential.exp_generator]
  exact solution_eq_evolution hL t

/-- An invertible initial matrix cancels from the actual evolved matrix, leaving the plane rotor. -/
theorem initial_inverse_evolution {L0 : Mat} (hL0 : IsUnit L0) (omega t : ℝ) :
    L0⁻¹ * evolution L0 omega t = rotor (omega * t / 2) := by
  rw [evolution, ← mul_assoc,
    Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hL0), one_mul]

/-- An invertible initial matrix cancels from every actual solution to give the plane rotor. -/
theorem initial_inverse_solution {L : ℝ → Mat} {omega : ℝ}
    (hL : Solves L omega) (h0 : IsUnit (L 0)) (t : ℝ) :
    (L 0)⁻¹ * L t = rotor (omega * t / 2) := by
  rw [solution_eq_evolution hL t]
  exact initial_inverse_evolution h0 omega t

/-- The normalized arbitrary-initial evolution acts on the actual rest spinor with the source negative half-angle complex phase. -/
theorem initial_inverse_evolution_restSpinor {L0 : Mat} (hL0 : IsUnit L0) (omega t : ℝ) :
    (L0⁻¹ * evolution L0 omega t).mulVec restSpinor =
      Complex.exp (-Complex.I * ((omega * t / 2 : ℝ) : ℂ)) • restSpinor := by
  rw [initial_inverse_evolution hL0, rotor_mulVec_restSpinor]

/-- Every actual source ODE solution with invertible initial matrix has the source normalized rest-spinor phase. -/
theorem initial_inverse_solution_restSpinor {L : ℝ → Mat} {omega : ℝ}
    (hL : Solves L omega) (h0 : IsUnit (L 0)) (t : ℝ) :
    ((L 0)⁻¹ * L t).mulVec restSpinor =
      Complex.exp (-Complex.I * ((omega * t / 2 : ℝ) : ℂ)) • restSpinor := by
  rw [initial_inverse_solution hL h0, rotor_mulVec_restSpinor]

/-- The actual inverse-weighted derivative of the uniform evolution is the constant-plane Maurer–Cartan generator. -/
theorem evolution_body_derivative {L0 : Mat} (hL0 : IsUnit L0) (omega t : ℝ) :
    (evolution L0 omega t)⁻¹ * deriv (evolution L0 omega) t =
      (((omega / 2 : ℝ) : ℂ) • planeGenerator) := by
  rw [deriv_evolution, mul_smul_comm, ← mul_assoc,
    Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp (evolution_isUnit hL0 omega t)),
    one_mul]

end FoliationQM.RotorODE
