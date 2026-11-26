module
public import FoliationQM.PolarMatrixFibers
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
/-!
# Exact full-angle fibers of actual regular polar spinors

Source: v13 `prop:takabayasi` and `eq:takabayasi_polar`. The actual complex
half-angle exponential is classified using the integer fibers of the
complex exponential. Its equality period is four pi; its negative is
obtained by a two-pi shift followed by an integer four-pi shift.

On positive density parameters and actual determinant-one matrix inputs,
the matrix-coordinate fiber theorem applies to the actual source polar
spinors. Their invariant bilinears first force equal densities. Positive
square-root amplitude cancellation then yields exactly the four-pi and
simultaneous two-pi/matrix-sign alternatives. No decomposition, phase
identity, or final spinor-fiber conclusion is supplied as a premise.

The full angle is never reduced modulo two pi with the matrix fixed. These
are exact pointwise fiber statements; quotient topology, smoothness and
abstract Spin-group or Lorentz-covering classification remain separate.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.PolarAngleFibers
open DiracMatrices SpinorMatrix SpecialLinearSpin SpinorRegularity PolarSpinorBilinears PolarMatrixFibers

/-- The actual complex half-angle factor of the full source chiral angle. -/
def halfPhase (beta : ℝ) : ℂ := Complex.exp (Complex.I*(beta:ℂ)/2)

/-- Equality of actual half-angle factors is exactly a four-pi integer shift of full angles. -/
theorem halfPhase_eq_iff (beta theta : ℝ) :
    halfPhase beta=halfPhase theta ↔ ∃ n : ℤ, beta=theta+(n:ℝ)*(4*Real.pi) := by
  simp only [halfPhase, Complex.exp_eq_exp_iff_exists_int]
  constructor
  · rintro ⟨n,h⟩
    refine ⟨n,?_⟩
    have hi := congrArg Complex.im h
    simp at hi
    linarith
  · rintro ⟨n,h⟩
    refine ⟨n,?_⟩
    rw [h]
    push_cast
    ring

/-- Increasing the full angle by two pi negates its actual half-angle phase. -/
theorem halfPhase_add_two_pi (beta : ℝ) :
    halfPhase (beta+2*Real.pi) = -halfPhase beta := by
  have he : Complex.I*((beta+2*Real.pi:ℝ):ℂ)/2=
      Complex.I*(beta:ℂ)/2+(Real.pi:ℂ)*Complex.I := by push_cast; ring
  rw [halfPhase, he, Complex.exp_add, Complex.exp_pi_mul_I, mul_neg_one]
  rfl

/-- Opposite actual half-angle factors correspond exactly to a two-pi shift followed by an integer four-pi shift. -/
theorem halfPhase_eq_neg_iff (beta theta : ℝ) :
    halfPhase beta = -halfPhase theta ↔
      ∃ n : ℤ, beta=theta+2*Real.pi+(n:ℝ)*(4*Real.pi) := by
  rw [← halfPhase_add_two_pi theta, halfPhase_eq_iff]

/-- The actual half-angle phase never vanishes. -/
theorem halfPhase_ne_zero (beta : ℝ) : halfPhase beta ≠ 0 := Complex.exp_ne_zero _

/-- At fixed positive density, equality of actual polar spinors has precisely the equal-phase/equal-matrix or opposite-phase/opposite-matrix fibers. -/
theorem polarSpinor_fixedDensity_phase_fibers (rho beta theta : ℝ) (A B : Mat2)
    (hrho : 0 < rho) (hA : Matrix.det A=1) (hB : Matrix.det B=1) :
    polarSpinor rho beta (spin A)=polarSpinor rho theta (spin B) ↔
      (halfPhase beta=halfPhase theta ∧ A=B) ∨ (halfPhase beta= -halfPhase theta ∧ A= -B) := by
  have hr : (Real.sqrt rho : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr hrho).ne'
  rw [← parameterSpinor_polarAmplitude rho beta A,
    ← parameterSpinor_polarAmplitude rho theta B]
  change parameterSpinor ((Real.sqrt rho:ℂ)*halfPhase beta) A =
    parameterSpinor ((Real.sqrt rho:ℂ)*halfPhase theta) B ↔ _
  rw [parameterSpinor_fibers_iff _ _ A B
      (mul_ne_zero hr (halfPhase_ne_zero beta))
      (mul_ne_zero hr (halfPhase_ne_zero theta)) hA hB]
  simp only [← mul_neg, mul_right_inj' hr]

/-- At fixed positive density, the full-angle fibers are exactly integer four-pi shifts or two-pi shifts with matrix sign reversal. -/
theorem polarSpinor_fixedDensity_fibers (rho beta theta : ℝ) (A B : Mat2)
    (hrho : 0 < rho) (hA : Matrix.det A=1) (hB : Matrix.det B=1) :
    polarSpinor rho beta (spin A)=polarSpinor rho theta (spin B) ↔
      ((∃ n : ℤ, beta=theta+(n:ℝ)*(4*Real.pi)) ∧ A=B) ∨
      ((∃ n : ℤ, beta=theta+2*Real.pi+(n:ℝ)*(4*Real.pi)) ∧ A= -B) := by
  rw [polarSpinor_fixedDensity_phase_fibers rho beta theta A B hrho hA hB,
    halfPhase_eq_iff, halfPhase_eq_neg_iff]

/-- Equality of actual positive-density polar spinors forces equality of the density parameters by their actual invariant bilinears. -/
theorem polarSpinor_density_eq (rho sigma beta theta : ℝ) (A B : Mat2)
    (hrho : 0 < rho) (hsigma : 0 < sigma) (hA : Matrix.det A=1) (hB : Matrix.det B=1)
    (h : polarSpinor rho beta (spin A)=polarSpinor sigma theta (spin B)) : rho=sigma := by
  have hd := congrArg invariantDensity h
  simpa only [invariantDensity_polar rho beta (spin A) hrho.le
      (spin_dirac_isometry A hA) (spin_gamma5_commute A),
    invariantDensity_polar sigma theta (spin B) hsigma.le
      (spin_dirac_isometry B hB) (spin_gamma5_commute B)] using hd

/-- Actual regular polar parameters have exactly equal densities and the four-pi/equal-matrix or shifted-two-pi/opposite-matrix fibers. -/
theorem polarSpinor_fibers_iff (rho sigma beta theta : ℝ) (A B : Mat2)
    (hrho : 0 < rho) (hsigma : 0 < sigma) (hA : Matrix.det A=1) (hB : Matrix.det B=1) :
    polarSpinor rho beta (spin A)=polarSpinor sigma theta (spin B) ↔
      rho=sigma ∧
        (((∃ n : ℤ, beta=theta+(n:ℝ)*(4*Real.pi)) ∧ A=B) ∨
         ((∃ n : ℤ, beta=theta+2*Real.pi+(n:ℝ)*(4*Real.pi)) ∧ A= -B)) := by
  constructor
  · intro h
    have hd := polarSpinor_density_eq rho sigma beta theta A B hrho hsigma hA hB h
    subst sigma
    exact ⟨rfl, (polarSpinor_fixedDensity_fibers rho beta theta A B hrho hA hB).mp h⟩
  · rintro ⟨rfl,h⟩
    exact (polarSpinor_fixedDensity_fibers rho beta theta A B hrho hA hB).mpr h

end FoliationQM.PolarAngleFibers
