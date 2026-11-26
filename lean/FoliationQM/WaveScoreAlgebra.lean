module

public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

/-!
# Actual density, score and phase-rate algebra

Sources: v13 thm:uncertainty, eq:cramer_rao and eq:p_var_decomp,
component kinds A and C. Density is the literal complex norm squared, and
its derivative is obtained from the actual real-domain norm-square chain
rule. The quotient definitions use the standard zero extension at a node.
Weighted cancellations and bounds hold at nodes as well. Reconstructing
an arbitrary complex derivative requires a nonzero amplitude; extending
that reconstruction almost everywhere needs the separate nodal theorem.
-/

@[expose] public section
noncomputable section

namespace FoliationQM.WaveScoreAlgebra
open Complex
open scoped ComplexConjugate

/-- Literal scalar wave density. -/
def density (z : ℂ) : ℝ := ‖z‖ ^ 2

/-- The actual norm-square derivative evaluated on a tangent value. -/
def densityDerivative (z v : ℂ) : ℝ := 2 * (conj z * v).re

/-- Density score, with the totalized zero extension at a node. -/
def score (z v : ℂ) : ℝ := densityDerivative z v / density z

/-- Canonical phase rate, with the totalized zero extension at a node. -/
def phaseRate (z v : ℂ) : ℝ := (conj z * v).im / density z

/-- Canonical bulk momentum at a supplied real action scale. -/
def bulk (hbar : ℝ) (z v : ℂ) : ℝ := hbar * phaseRate z v

/-- The literal wave density is nonnegative at every amplitude. -/
theorem density_nonneg (z : ℂ) : 0 ≤ density z := sq_nonneg ‖z‖

/-- Positive density is equivalent to nonzero complex amplitude. -/
theorem density_pos_iff (z : ℂ) : 0 < density z ↔ z ≠ 0 := by
  simp [density, sq_pos_iff]

/-- Multiplication by density cancels the score, including at a node. -/
theorem density_mul_score (z v : ℂ) :
    density z * score z v = densityDerivative z v := by
  rcases eq_or_ne z 0 with rfl | hz
  · simp [density, score, densityDerivative]
  · have hp := ne_of_gt ((density_pos_iff z).2 hz)
    unfold score
    field_simp

/-- The imaginary current also cancels at every amplitude. -/
theorem density_mul_phaseRate (z v : ℂ) :
    density z * phaseRate z v = (conj z * v).im := by
  rcases eq_or_ne z 0 with rfl | hz
  · simp [density, phaseRate]
  · have hp := ne_of_gt ((density_pos_iff z).2 hz)
    unfold phaseRate
    field_simp

/-- The weighted canonical bulk momentum equals the scaled imaginary current. -/
theorem density_mul_bulk (hbar : ℝ) (z v : ℂ) :
    density z * bulk hbar z v = hbar * (conj z * v).im := by
  unfold bulk
  rw [← mul_assoc, mul_comm (density z) hbar, mul_assoc, density_mul_phaseRate]

/-- An all-point quotient identity; both sides vanish at zero amplitude. -/
theorem score_eq_two_re_div (z v : ℂ) : score z v = 2 * (v / z).re := by
  simp only [score, densityDerivative, density, Complex.div_re, Complex.mul_re,
    Complex.conj_re, Complex.conj_im, Complex.normSq_eq_norm_sq]
  ring

/-- The phase rate is the imaginary quotient component, including its zero extension. -/
theorem phaseRate_eq_im_div (z v : ℂ) : phaseRate z v = (v / z).im := by
  simp only [phaseRate, density, Complex.div_im, Complex.mul_im,
    Complex.conj_re, Complex.conj_im, Complex.normSq_eq_norm_sq]
  ring

private theorem density_mul_normSq_div (z v : ℂ) (hz : z ≠ 0) :
    density z * Complex.normSq (v / z) = density v := by
  rw [Complex.normSq_div, Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
  change density z * (density v / density z) = density v
  have hp := ne_of_gt ((density_pos_iff z).2 hz)
  field_simp

/-- The weighted squared score is controlled by the genuine tangent energy. -/
theorem density_mul_score_sq_le (z v : ℂ) :
    density z * (score z v) ^ 2 ≤ 4 * density v := by
  rcases eq_or_ne z 0 with rfl | hz
  · simp [density, score, densityDerivative]
  · have hr : (v / z).re ^ 2 ≤ Complex.normSq (v / z) := by
      simpa [pow_two] using Complex.re_sq_le_normSq (v / z)
    calc
      density z * (score z v) ^ 2 = 4 * (density z * (v / z).re ^ 2) := by
        rw [score_eq_two_re_div]
        ring
      _ ≤ 4 * (density z * Complex.normSq (v / z)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hr (density_nonneg z)) (by norm_num)
      _ = 4 * density v := by rw [density_mul_normSq_div z v hz]

/-- The weighted squared phase rate is bounded by the genuine tangent energy. -/
theorem density_mul_phaseRate_sq_le (z v : ℂ) :
    density z * (phaseRate z v) ^ 2 ≤ density v := by
  rcases eq_or_ne z 0 with rfl | hz
  · simp [density, phaseRate]
  · have hi : (v / z).im ^ 2 ≤ Complex.normSq (v / z) := by
      simpa [pow_two] using Complex.im_sq_le_normSq (v / z)
    rw [phaseRate_eq_im_div]
    calc
      density z * (v / z).im ^ 2 ≤ density z * Complex.normSq (v / z) :=
        mul_le_mul_of_nonneg_left hi (density_nonneg z)
      _ = density v := density_mul_normSq_div z v hz

/-- Reconstruction at a nonzero amplitude; the real half is taken before casting. -/
theorem derivative_reconstruction (z v : ℂ) (hz : z ≠ 0) :
    v = (((score z v / 2 : ℝ) : ℂ) + Complex.I * (phaseRate z v : ℂ)) * z := by
  rw [score_eq_two_re_div, phaseRate_eq_im_div]
  have hh : 2 * (v / z).re / 2 = (v / z).re := by ring
  rw [hh, mul_comm Complex.I, Complex.re_add_im]
  exact (div_mul_cancel₀ v hz).symm

/-- The real-domain norm-square chain rule, valid even at a node. -/
theorem hasDerivAt_density {u : ℝ → ℂ} {v : ℂ} {x : ℝ}
    (hu : HasDerivAt u v x) :
    HasDerivAt (fun y => density (u y)) (densityDerivative (u x) v) x := by
  simpa only [density, densityDerivative, Complex.inner, mul_comm v] using hu.norm_sq

/-- The score is the actual logarithmic derivative wherever the amplitude is nonzero. -/
theorem hasDerivAt_log_density {u : ℝ → ℂ} {v : ℂ} {x : ℝ}
    (hu : HasDerivAt u v x) (hu0 : u x ≠ 0) :
    HasDerivAt (fun y => Real.log (density (u y))) (score (u x) v) x := by
  exact (hasDerivAt_density hu).log (ne_of_gt ((density_pos_iff (u x)).2 hu0))

end FoliationQM.WaveScoreAlgebra
