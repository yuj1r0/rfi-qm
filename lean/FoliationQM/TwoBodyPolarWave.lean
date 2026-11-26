module

public import FoliationQM.TwoBodyCoordinates
public import FoliationQM.PolarSecondDifferential

/-!
# Two-body amplitude and action variables

The wave in v13 `eq:2p_kahler_psi` is a real amplitude times the complex
phase of the action divided by Planck's constant. Its squared derivative
splits into amplitude and phase contributions. Its imaginary overlap with
the derivative gives the currents in `eq:2p_continuity` and the time term
in the action. The identities hold for signed amplitudes, including zeros.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.TwoBodyPolarWave

open TwoBodyCoordinates MasterMetricAndCone PolarSecondDifferential
open scoped ComplexConjugate

/-- The two-particle wave in signed amplitude and real action variables. -/
def wave (hbar : ℝ) (R S : Point → ℝ) (p : Point) : ℂ :=
  amplitudeField R (fun z => S z / hbar) p

variable {R S : Point → ℝ} {p : Point}

/-- The polar wave is differentiable wherever its amplitude and action are differentiable. -/
theorem differentiableAt_wave (hbar : ℝ) (hR : DifferentiableAt ℝ R p)
    (hS : DifferentiableAt ℝ S p) : DifferentiableAt ℝ (wave hbar R S) p := by
  unfold wave amplitudeField phase
  fun_prop

/-- The complex squared norm recovers the amplitude squared at every point. -/
theorem born (hbar : ℝ) (R S : Point → ℝ) (p : Point) :
    ‖wave hbar R S p‖ ^ 2 = (R p) ^ 2 := by
  simp only [wave, amplitudeField, phase, norm_mul, Complex.norm_exp_ofReal_mul_I,
    Complex.norm_real, Real.norm_eq_abs, mul_one, sq_abs]

/-- Directional derivative of the genuine wave along any two-particle spacetime direction. -/
theorem directional (hbar : ℝ) (hR : DifferentiableAt ℝ R p) (hS : DifferentiableAt ℝ S p)
    (v : Point) : D v (wave hbar R S) p =
      amplitudeTangent (R p) (S p / hbar) (D v R p) (D v S p / hbar) := by
  have hΦ : DifferentiableAt ℝ (fun z => S z / hbar) p := by
    simpa only [div_eq_mul_inv, mul_comm] using hS.const_mul hbar⁻¹
  have hd := directionalDerivative_amplitudeField hR hΦ v
  rw [directionalDerivative_div_const hS] at hd
  exact hd

/-- Squared derivative entering either spatial kinetic term of the two-particle action. -/
theorem kinetic (hbar : ℝ) (hR : DifferentiableAt ℝ R p) (hS : DifferentiableAt ℝ S p)
    (v : Point) : ‖D v (wave hbar R S) p‖ ^ 2 =
      (D v R p) ^ 2 + (R p) ^ 2 * (D v S p / hbar) ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq, directional hbar hR hS, amplitudeTangent_normSq]

private theorem phase_unit (a : ℝ) : star (phase a) * phase a = 1 := by
  rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
  simp [phase]

/-- Multiplying by the conjugate wave cancels the phase in its directional derivative. -/
theorem overlap (hbar : ℝ) (hR : DifferentiableAt ℝ R p) (hS : DifferentiableAt ℝ S p)
    (v : Point) : star (wave hbar R S p) * D v (wave hbar R S) p =
      (R p : ℂ) * (((D v R p : ℝ) : ℂ) + Complex.I * (R p : ℂ) * ((D v S p / hbar : ℝ) : ℂ)) := by
  rw [directional hbar hR hS]
  let a := S p / hbar
  let z := ((D v R p : ℝ) : ℂ) + Complex.I * (R p : ℂ) * ((D v S p / hbar : ℝ) : ℂ)
  change star ((R p : ℂ) * phase a) * (phase a * z) = (R p : ℂ) * z
  calc
    _ = (star (phase a) * phase a) * ((R p : ℂ) * z) := by
      simp only [star_mul, Complex.star_def, Complex.conj_ofReal]
      ring
    _ = _ := by rw [phase_unit, one_mul]

/-- The imaginary overlap isolates the action derivative, including when the amplitude vanishes. -/
theorem overlap_im (hbar : ℝ) (hR : DifferentiableAt ℝ R p) (hS : DifferentiableAt ℝ S p)
    (v : Point) : (star (wave hbar R S p) * D v (wave hbar R S) p).im =
      (R p) ^ 2 * D v S p / hbar := by
  rw [overlap hbar hR hS]
  simp only [Complex.mul_im, Complex.mul_re, Complex.add_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im]
  ring

/-- The time term in the real Schrödinger Lagrangian is minus density times action rate. -/
theorem time_term {hbar : ℝ} (hh : hbar ≠ 0) (hR : DifferentiableAt ℝ R p)
    (hS : DifferentiableAt ℝ S p) :
    -hbar * (star (wave hbar R S p) * Dt (wave hbar R S) p).im = -(R p) ^ 2 * Dt S p := by
  unfold Dt
  rw [overlap_im hbar hR hS]
  field_simp

/-- The same time identity in the antisymmetric complex form, with the
derivative taken on the conjugate field in the second term. -/
theorem antisymmetric_time_term {hbar : ℝ} (hh : hbar ≠ 0) (hR : DifferentiableAt ℝ R p)
    (hS : DifferentiableAt ℝ S p) :
    Complex.I * (hbar : ℂ) / 2 * (star (wave hbar R S p) * Dt (wave hbar R S) p -
      wave hbar R S p * Dt (fun z => star (wave hbar R S z)) p) =
      ((-(R p) ^ 2 * Dt S p : ℝ) : ℂ) := by
  let ψ := wave hbar R S
  let d := Dt ψ p
  have hd : Dt (fun z => star (ψ z)) p = star d :=
    ActionDensity.fderiv_conj_apply (differentiableAt_wave hbar hR hS) timeAxis
  have he : ψ p * star d = star (star (ψ p) * d) := by simp [mul_comm]
  change Complex.I * (hbar : ℂ) / 2 * (star (ψ p) * d - ψ p * Dt (fun z => star (ψ z)) p) = _
  rw [hd, he, ← time_term hh hR hS]
  change Complex.I * (hbar : ℂ) / 2 * (star (ψ p) * d - conj (star (ψ p) * d)) =
    ((-hbar * (star (ψ p) * d).im : ℝ) : ℂ)
  rw [Complex.sub_conj]
  push_cast
  ring_nf
  simp [Complex.I_sq]

/-- In either spatial sector the scalar-wave probability current equals the
Born density divided by mass times the action derivative. -/
theorem current_eq {hbar : ℝ} (hh : hbar ≠ 0) (m : ℝ) (hR : DifferentiableAt ℝ R p)
    (hS : DifferentiableAt ℝ S p) (v : Point) :
    (hbar / m) * (star (wave hbar R S p) * D v (wave hbar R S) p).im =
      ((R p) ^ 2 / m) * D v S p := by
  rw [overlap_im hbar hR hS]
  field_simp [hh]

end FoliationQM.TwoBodyPolarWave
