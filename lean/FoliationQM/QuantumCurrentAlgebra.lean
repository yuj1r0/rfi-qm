module

public import FoliationQM.SobolevDensity

/-!
# Actual complex momentum current and centered energy

Sources: v13 eq:p_var_decomp, eq:p_fisher_bound and thm:uncertainty,
algebraic and differential components. Momentum is the literal complex
multiple of a tangent value. The current identities hold at every amplitude.
The centered energy formula requires either a nonzero amplitude or the
proved reconstruction equality; an actual almost-everywhere derivative
supplies that reconstruction even at nodes. No integral identity or
phase-gradient interpretation is assumed here.
-/

@[expose] public section
noncomputable section

namespace FoliationQM.QuantumCurrentAlgebra
open MeasureTheory WaveScoreAlgebra
open scoped ComplexConjugate

/-- The literal weak-momentum value at a supplied derivative value. -/
def pValue (hbar : ℝ) (v : ℂ) : ℂ := (-Complex.I) * (hbar : ℂ) * v

/-- The actual complex momentum current, before integration. -/
def current (hbar : ℝ) (z v : ℂ) : ℂ := conj z * pValue hbar v

/-- Subtraction of a real momentum center times the actual wave value. -/
def centeredPValue (hbar p : ℝ) (z v : ℂ) : ℂ :=
  pValue hbar v - (p : ℂ) * z

/-- The real current is the density-weighted canonical bulk momentum, including at nodes. -/
theorem current_re (hbar : ℝ) (z v : ℂ) :
    (current hbar z v).re = density z * bulk hbar z v := by
  rw [density_mul_bulk]
  simp [current, pValue, Complex.mul_re, Complex.mul_im]
  ring

/-- The imaginary current is minus half the action scale times the actual density derivative. -/
theorem current_im (hbar : ℝ) (z v : ℂ) :
    (current hbar z v).im = -(hbar / 2) * densityDerivative z v := by
  simp [current, pValue, densityDerivative, Complex.mul_re, Complex.mul_im]
  ring

private theorem centeredPValue_norm_sq_of_reconstruction (hbar p : ℝ) (z v : ℂ)
    (hrec : v = (((score z v / 2 : ℝ) : ℂ) +
      Complex.I * (phaseRate z v : ℂ)) * z) :
    ‖centeredPValue hbar p z v‖ ^ 2 =
      density z * ((bulk hbar z v - p) ^ 2 + (hbar ^ 2 / 4) * score z v ^ 2) := by
  have hfactor : centeredPValue hbar p z v =
      (((bulk hbar z v - p : ℝ) : ℂ) +
        Complex.I * ((-(hbar / 2) * score z v : ℝ) : ℂ)) * z := by
    calc
      centeredPValue hbar p z v =
          (-Complex.I) * (hbar : ℂ) *
            ((((score z v / 2 : ℝ) : ℂ) +
              Complex.I * (phaseRate z v : ℂ)) * z) - (p : ℂ) * z :=
        congrArg (fun w : ℂ => pValue hbar w - (p : ℂ) * z) hrec
      _ = _ := by
        apply Complex.ext <;>
          simp [bulk, Complex.mul_re, Complex.mul_im] <;> ring
  have hcoeff :
      ‖(((bulk hbar z v - p : ℝ) : ℂ) +
        Complex.I * ((-(hbar / 2) * score z v : ℝ) : ℂ))‖ ^ 2 =
      (bulk hbar z v - p) ^ 2 + (-(hbar / 2) * score z v) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp [pow_two]
  rw [hfactor, norm_mul, mul_pow, hcoeff]
  unfold density
  ring

/-- At nonzero amplitude, the actual centered momentum energy splits into bulk and score squares. -/
theorem centeredPValue_norm_sq (hbar p : ℝ) (z v : ℂ) (hz : z ≠ 0) :
    ‖centeredPValue hbar p z v‖ ^ 2 =
      density z * ((bulk hbar z v - p) ^ 2 + (hbar ^ 2 / 4) * score z v ^ 2) :=
  centeredPValue_norm_sq_of_reconstruction hbar p z v
    (WaveScoreAlgebra.derivative_reconstruction z v hz)

/-- An actual almost-everywhere derivative gives the centered energy identity on the whole line. -/
theorem ae_centeredPValue_norm_sq {u v : ℝ → ℂ} (hbar p : ℝ)
    (hd : ∀ᵐ x ∂volume, HasDerivAt u (v x) x) :
    ∀ᵐ x ∂volume, ‖centeredPValue hbar p (u x) (v x)‖ ^ 2 =
      density (u x) * ((bulk hbar (u x) (v x) - p) ^ 2 +
        (hbar ^ 2 / 4) * score (u x) (v x) ^ 2) := by
  filter_upwards [SobolevDensity.ae_derivative_reconstruction hd] with x hx
  exact centeredPValue_norm_sq_of_reconstruction hbar p (u x) (v x) hx

end FoliationQM.QuantumCurrentAlgebra
