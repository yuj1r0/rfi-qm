module

public import FoliationQM.TwoBodyActionDensity

/-!
# Phase-rotated derivatives of a two-particle wave

For v13 `eq:2p_schrodinger` and `eq:2p_HJB`, taking out the common unit
phase separates the amplitude-curvature contribution from the phase and
transport terms. The second derivative is the actual iterated Fréchet
directional derivative on physical time and the two spatial positions.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.TwoBodyPolarSecondJet

open TwoBodyCoordinates TwoBodyPolarWave PolarSecondDifferential
open scoped Topology

variable {R S : Point → ℝ} {p : Point}

/-- The conjugate dimensionless phase cancels the forward phase. -/
theorem cancel_phase (a : ℝ) : star (phase a) * phase a = 1 := by
  rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
  simp [phase]

/-- Removing the common phase preserves the zero equation for any complex residual. -/
theorem rotate_eq_zero_iff (a : ℝ) (z : ℂ) : star (phase a) * z = 0 ↔ z = 0 := by
  have hn : star (phase a) ≠ 0 := fun h => by simpa [h] using cancel_phase a
  exact mul_eq_zero.trans (or_iff_right hn)

/-- Removing the phase from the wave yields its real signed amplitude. -/
theorem rotate_value (h : ℝ) (R S : Point → ℝ) (p : Point) :
    star (phase (S p / h)) * wave h R S p = (R p : ℂ) := by
  unfold wave amplitudeField
  rw [mul_left_comm, cancel_phase, mul_one]

/-- After rotation, the real part of the first derivative is the amplitude
derivative and its imaginary part is the amplitude times the scaled action derivative. -/
theorem rotate_first (h : ℝ) (hR : DifferentiableAt ℝ R p) (hS : DifferentiableAt ℝ S p)
    (v : Point) : star (phase (S p / h)) * D v (wave h R S) p =
      ((D v R p : ℝ) : ℂ) + Complex.I * ((R p * D v S p / h : ℝ) : ℂ) := by
  rw [directional h hR hS, MasterMetricAndCone.amplitudeTangent, ← mul_assoc, cancel_phase, one_mul]
  push_cast
  ring

/-- Real part of the rotated physical time derivative. -/
theorem rotate_time_re (h : ℝ) (hR : DifferentiableAt ℝ R p) (hS : DifferentiableAt ℝ S p) :
    (star (phase (S p / h)) * Dt (wave h R S) p).re = Dt R p := by
  unfold Dt
  rw [rotate_first h hR hS]
  simp

/-- Imaginary part of the rotated physical time derivative. -/
theorem rotate_time_im (h : ℝ) (hR : DifferentiableAt ℝ R p) (hS : DifferentiableAt ℝ S p) :
    (star (phase (S p / h)) * Dt (wave h R S) p).im = R p * Dt S p / h := by
  unfold Dt
  rw [rotate_first h hR hS]
  simp

/-- The actual second polar derivative at a C² point, before rotation by the unit phase. -/
theorem second (h : ℝ) (hR : ContDiffAt ℝ 2 R p) (hS : ContDiffAt ℝ 2 S p) (v : Point) :
    D v (D v (wave h R S)) p =
      PolarSecondJet.polarSecondTangent (R p) (S p / h) (D v R p) (D v S p / h)
        (D v (D v R) p) (D v (D v S) p / h) := by
  have hRn := PolarRegularity.eventually_differentiableAt_of_contDiffAt_two hR
  have hSn := PolarRegularity.eventually_differentiableAt_of_contDiffAt_two hS
  have hR2 := PolarRegularity.differentiableAt_directionalDerivative_of_contDiffAt_two hR v
  have hS2 := PolarRegularity.differentiableAt_directionalDerivative_of_contDiffAt_two hS v
  have hΦ : ∀ᶠ z in 𝓝 p, DifferentiableAt ℝ (fun w => S w / h) z := by
    filter_upwards [hSn] with z hz
    simpa only [div_eq_mul_inv, mul_comm] using hz.const_mul h⁻¹
  have hd := secondDirectionalDerivative_amplitudeField v hRn hΦ hR2
    (hasFDerivAt_directionalDerivative_div_const hSn h v hS2).differentiableAt
  rw [directionalDerivative_div_const hSn.self_of_nhds,
    secondDirectionalDerivative_div_const hSn h v hS2] at hd
  exact hd

/-- Rotating the genuine second derivative gives its real curvature and
imaginary transport terms in a single complex equality. -/
theorem rotate_second (h : ℝ) (hR : ContDiffAt ℝ 2 R p) (hS : ContDiffAt ℝ 2 S p) (v : Point) :
    star (phase (S p / h)) * D v (D v (wave h R S)) p =
      ((D v (D v R) p - R p * (D v S p / h) ^ 2 : ℝ) : ℂ) +
        Complex.I * (((2 * D v R p * D v S p + R p * D v (D v S) p) / h : ℝ) : ℂ) := by
  rw [second h hR hS, PolarSecondJet.polarSecondTangent, ← mul_assoc, cancel_phase, one_mul]
  push_cast
  ring

/-- The real part of the phase-rotated second derivative supplies the amplitude
curvature and the negative squared phase gradient. -/
theorem rotate_second_re (h : ℝ) (hR : ContDiffAt ℝ 2 R p) (hS : ContDiffAt ℝ 2 S p) (v : Point) :
    (star (phase (S p / h)) * D v (D v (wave h R S)) p).re =
      D v (D v R) p - R p * (D v S p / h) ^ 2 := by
  rw [rotate_second h hR hS]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
    Complex.ofReal_im, zero_mul, mul_zero, sub_zero, add_zero]

/-- The imaginary part of the phase-rotated second derivative yields the mixed
amplitude-action derivative and the action curvature. -/
theorem rotate_second_im (h : ℝ) (hR : ContDiffAt ℝ 2 R p) (hS : ContDiffAt ℝ 2 S p) (v : Point) :
    (star (phase (S p / h)) * D v (D v (wave h R S)) p).im =
      (2 * D v R p * D v S p + R p * D v (D v S) p) / h := by
  rw [rotate_second h hR hS]
  simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, zero_mul, one_mul, zero_add]

end FoliationQM.TwoBodyPolarSecondJet
