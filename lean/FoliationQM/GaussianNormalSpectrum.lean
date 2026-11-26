module

public import FoliationQM.GaussianMassShellMoments
public import FoliationQM.GaussianNormalOrientation

/-!
# The spectrum of the actual Gaussian normal datum

The derivative of the positive-frequency rest packet multiplies its initial
Gaussian spectrum by Ω(k). The windowed orientation test for v13 line 767
uses continuity, boundedness and integrability of this particular function.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.GaussianNormalSpectrum

open LorentzCoordinates GaussianKGMode GaussianSpatialFourier GaussianNormalOrientation MeasureTheory

/-- Real normal spectrum before dividing by the constant Gaussian mass. -/
def spectrum (μ σ : ℝ) (k : Spatial) : ℝ := rate μ k * weight (σ^2) k

/-- The normal Fourier multiplier is continuous in angular wave number. -/
theorem continuous_spectrum (μ σ : ℝ) : Continuous (spectrum μ σ) := by
  unfold spectrum rate weight speedSq spatialDot
  fun_prop

/-- The frequency-weighted positive-width Gaussian spectrum is integrable. -/
theorem integrable_spectrum (μ : ℝ) {σ : ℝ} (hσ : 0 < σ) : Integrable (spectrum μ σ) := by
  change Integrable (fun k => rate μ k * weight (σ^2) k)
  simpa using GaussianMassShellMoments.integrable_rate_pow_weight (sq_pos_of_pos hσ) μ 1

/-- The actual spectrum is even under reversal of the full spatial frequency. -/
theorem spectrum_neg (μ σ : ℝ) (k : Spatial) : spectrum μ σ (-k) = spectrum μ σ k := by
  rw [spectrum, GaussianMassShellMoments.rate_neg, GaussianMassShellMoments.weight_neg]
  rfl

/-- A uniform finite bound for the normal spectrum follows by completing the square
in Ω against Gaussian decay. It holds for every positive spatial width. -/
theorem bounded_spectrum (μ : ℝ) {σ : ℝ} (hσ : 0 < σ) :
    ∃ B : ℝ, ∀ k, |spectrum μ σ k| ≤ B := by
  let a := σ^2
  have ha : 0 < a := sq_pos_of_pos hσ
  refine ⟨Real.exp (a*μ^2 + 1/(4*a)), fun k => ?_⟩
  have hsq : speedSq k = (rate μ k)^2 - μ^2 := by linarith [rate_sq μ k]
  have hb : rate μ k - a*speedSq k - a*μ^2 ≤ 1/(4*a) := by
    apply (le_div_iff₀ (by positivity)).mpr
    rw [hsq]
    nlinarith only [sq_nonneg (2*a*rate μ k - 1)]
  change |rate μ k * Real.exp (-a*speedSq k)| ≤ _
  have hr : 0 ≤ rate μ k := Real.sqrt_nonneg _
  rw [abs_of_nonneg (mul_nonneg hr (Real.exp_pos _).le)]
  calc
    _ ≤ Real.exp (rate μ k) * Real.exp (-a*speedSq k) :=
      mul_le_mul_of_nonneg_right (by linarith [Real.add_one_le_exp (rate μ k)]) (Real.exp_pos _).le
    _ ≤ _ := by rw [← Real.exp_add, Real.exp_le_exp]; linarith

/-- The zero point on the chosen sampling axis is the origin of wave-number space. -/
theorem axis_zero : axis 0 = 0 := by simp [axis]

/-- Doubling a sampled frequency doubles its coordinate on the same laboratory axis. -/
theorem axis_two_smul (q : ℝ) : (2 : ℝ) • axis q = axis (2*q) := by
  ext i
  fin_cases i <;> simp [axis]

/-- Restricting the actual three-dimensional spectrum to the laboratory axis gives
the one-dimensional profile used in the three-frequency sign certificate. -/
theorem spectrum_axis (μ σ q : ℝ) :
    spectrum μ σ (axis q) = GaussianSpectralWitness.profile 1 μ σ q := by
  have hs : speedSq (axis q) = q^2 := by simp [speedSq_eq_sum, axis]
  simp [spectrum, GaussianSpectralWitness.profile, rate, weight, hs]

end FoliationQM.GaussianNormalSpectrum
