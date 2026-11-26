module
public import FoliationQM.SpinorMatrixSmooth
public import FoliationQM.LorentzCoefficientUniqueness
public import FoliationQM.LorentzGeneratorBracket

/-!
# Actual Lorentz-generator coefficients of trace-zero two-by-two matrices

Source: the real antisymmetric matrix coefficients in v13
`eq:maurer_cartan_def` and `lem:maurer_cartan`. Six explicit real and
imaginary entry combinations construct an antisymmetric coefficient
array. Exact finite algebra proves that the actual four-by-four spin
representative of a trace-zero matrix equals the existing ordered
minus-i-over-four sigma-matrix generator of this array.

The coefficient function extends to a real continuous-linear map on all
two-by-two matrices. Its representation and injectivity results explicitly
require trace zero. Uniqueness is proved among real antisymmetric arrays
using the already established faithful generator expansion. No generator
expansion, matrix-field tangent property or desired coefficient identity
is supplied as a premise of the construction. Deriving trace zero from an
actual local determinant-one field is a separate differential result.
-/

@[expose] public section
noncomputable section
open scoped Matrix.Norms.Operator
namespace FoliationQM.SpecialLinearLieAlgebra
open DiracMatrices SpinorMatrix SpecialLinearSpin CliffordCommutators
open SpinorMatrixSmooth LorentzCoefficientUniqueness LorentzGeneratorBracket

/-- The explicit real antisymmetric Lorentz coefficients extracted from the three complex entries of a trace-zero matrix, extended linearly to all matrix inputs. -/
def omega (T : Mat2) : Fin 4 → Fin 4 → ℝ :=
  !![0, (T 0 1+T 1 0).re, (T 1 0-T 0 1).im, 2*(T 0 0).re;
    -(T 0 1+T 1 0).re, 0, -2*(T 0 0).im, (T 0 1-T 1 0).re;
    -(T 1 0-T 0 1).im, 2*(T 0 0).im, 0, -(T 0 1+T 1 0).im;
    -2*(T 0 0).re, -(T 0 1-T 1 0).re, (T 0 1+T 1 0).im, 0]

/-- The constructed real coefficient array is antisymmetric for every two-by-two matrix input. -/
theorem omega_antisymmetric (T : Mat2) (a b : Fin 4) : omega T a b = -omega T b a := by
  fin_cases a <;> fin_cases b <;> simp [omega]

private theorem trace_zero_entry (T : Mat2) (htrace : Matrix.trace T = 0) : T 1 1 = -T 0 0 := by
  have h : T 0 0+T 1 1=0 := by simpa [Matrix.trace, Fin.sum_univ_succ] using htrace
  linear_combination h

set_option maxHeartbeats 1000000 in
/-- Every actual trace-zero two-by-two matrix has the constructed real Lorentz-generator expansion in the explicit Dirac representation. -/
theorem spin_eq_generator (T : Mat2) (htrace : Matrix.trace T = 0) :
    spin T = generator (omega T) := by
  have ht := trace_zero_entry T htrace
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    simp [spin, weylDual, ht, generator, omega, sigma, gamma,
      Fin.sum_univ_succ, Complex.mul_re, Complex.mul_im] <;> ring


/-- The explicit real coefficient construction preserves addition on all two-by-two matrices. -/
theorem omega_add (T U : Mat2) : omega (T+U) = omega T + omega U := by
  ext a b
  change omega (T+U) a b = omega T a b + omega U a b
  fin_cases a <;> fin_cases b <;> simp [omega] <;> ring

/-- The explicit real coefficient construction preserves real scalar multiplication on all matrix inputs. -/
theorem omega_real_smul (r : ℝ) (T : Mat2) : omega (r • T) = r • omega T := by
  ext a b
  change omega (r • T) a b = r * omega T a b
  fin_cases a <;> fin_cases b <;> simp [omega] <;> ring

/-- The actual coefficient construction packaged as a real continuous-linear map, without a trace restriction on its domain. -/
def omegaCLM : Mat2 →L[ℝ] (Fin 4 → Fin 4 → ℝ) :=
  ({ toFun := omega
     map_add' := omega_add
     map_smul' := omega_real_smul } : Mat2 →ₗ[ℝ] (Fin 4 → Fin 4 → ℝ)).toContinuousLinearMap

/-- The continuous-linear coefficient map evaluates to the explicit six-entry construction. -/
theorem omegaCLM_apply (T : Mat2) : omegaCLM T = omega T := rfl

/-- The zero matrix has zero constructed Lorentz coefficients. -/
theorem omega_zero : omega (0 : Mat2) = 0 := omegaCLM.map_zero


/-- Any real antisymmetric array representing the spin matrix of a trace-zero input is the constructed array. -/
theorem omega_unique (T : Mat2) (htrace : Matrix.trace T = 0)
    (theta : Fin 4 → Fin 4 → ℝ) (hanti : ∀ a b, theta a b = -theta b a)
    (hgen : spin T = generator theta) : theta = omega T :=
  generator_injective_on_antisymmetric hanti (omega_antisymmetric T)
    (hgen.symm.trans (spin_eq_generator T htrace))

/-- On trace-zero two-by-two matrices, the actual constructed real coefficient array determines the input uniquely. -/
theorem omega_injective_traceZero {T U : Mat2} (hT : Matrix.trace T = 0)
    (hU : Matrix.trace U = 0) (heq : omega T = omega U) : T = U := by
  apply spin_injective
  rw [spin_eq_generator T hT, spin_eq_generator U hU, heq]

/-- For a trace-zero input, the constructed Lorentz coefficients vanish exactly when the actual matrix vanishes. -/
theorem omega_eq_zero_iff (T : Mat2) (htrace : Matrix.trace T = 0) :
    omega T = 0 ↔ T = 0 := by
  constructor
  · intro h
    apply omega_injective_traceZero htrace (by simp)
    rw [h, omega_zero]
  · rintro rfl
    exact omega_zero

end FoliationQM.SpecialLinearLieAlgebra
