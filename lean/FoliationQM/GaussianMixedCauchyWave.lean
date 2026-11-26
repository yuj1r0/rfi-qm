module

public import FoliationQM.GaussianBranchMixing
public import FoliationQM.GaussianPositiveFrequencyPacket

/-!
# Free evolution of both Gaussian Cauchy data

At arbitrary Gaussian width, v13 `eq:dilatation_coercivity_bound` depends
on the normal Cauchy datum. The Fourier realisation below gives global free
solutions with normal derivative (K−iω)ψ and real Gaussian initial wave.
The two standing-time quadratures use Gaussian spectra differing by a factor
of the inverse mass-shell frequency.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.GaussianMixedCauchyWave

open GaussianSpatialFourier GaussianKGMode GaussianMassShellMoments GaussianBranchMixing
open LorentzCoordinates MeasureTheory OsmoticSliceFields PolarSecondDifferential
open scoped ContDiff

/-- Physical inverse Compton length of the wave. -/
def inverseLength (p : MassiveParameters) : ℝ := p.m * p.c / p.hbar

private theorem mass_positive (p : MassiveParameters) : 0 < inverseLength p :=
  div_pos (mul_pos p.m_pos p.c_pos) p.hbar_pos

/-- Gaussian spectrum divided by the shell rate, normalized to prescribe the velocity. -/
def velocitySpectrum (p : MassiveParameters) (σ : ℝ) (k : Spatial) : ℂ :=
  (((weight (σ^2) k / rate (inverseLength p) k) / mass (σ^2) : ℝ) : ℂ)

private theorem continuous_velocitySpectrum (p : MassiveParameters) (σ : ℝ) : Continuous (velocitySpectrum p σ) := by
  have hr : ∀ k, rate (inverseLength p) k ≠ 0 := fun k => ((mass_positive p).trans_le (mass_le_rate (mass_positive p) k)).ne'
  have hw : Continuous (weight (σ^2)) := by unfold weight speedSq spatialDot; fun_prop
  have hΩ : Continuous (rate (inverseLength p)) := by unfold rate speedSq spatialDot; fun_prop
  exact Complex.continuous_ofReal.comp ((hw.div hΩ hr).div_const _)

private theorem auxMoments (p : MassiveParameters) {σ : ℝ} (hσ : 0 < σ) :
    MassShellFourier.HasMoments (inverseLength p) (velocitySpectrum p σ) := by
  intro n
  have ha := sq_pos_of_pos hσ
  have hn (k : Spatial) : ‖velocitySpectrum p σ k‖ = (weight (σ^2) k / rate (inverseLength p) k) / mass (σ^2) := by
    rw [velocitySpectrum, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
    exact div_nonneg (div_nonneg (Real.exp_pos _).le (Real.sqrt_nonneg _)) (mass_pos ha).le
  simp_rw [MassShellFourier.shell, norm_shell, hn, ← mul_div_assoc]
  have h := (integrable_rate_pow_div_rate_weight ha (mass_positive p) n).div_const (mass (σ^2))
  simpa only [mul_div_assoc] using h

/-- The positive-frequency wave whose imaginary part provides the prescribed initial velocity. -/
def velocityWave (p : MassiveParameters) (σ : ℝ) : Covector → ℂ := MassShellFourier.wave (inverseLength p) (velocitySpectrum p σ)

private theorem aux_initial_im (p : MassiveParameters) {σ : ℝ} (hσ : 0 < σ) (y : Spatial) :
    (velocityWave p σ (slicePoint 0 y)).im = 0 := by
  rw [velocityWave, MassShellFourier.initial_value]
  have hi : Integrable (fun k => (weight (σ^2) k / rate (inverseLength p) k) / mass (σ^2)) := by
    simpa only [pow_zero,one_mul] using
      (integrable_rate_pow_div_rate_weight (sq_pos_of_pos hσ) (mass_positive p) 0).div_const (mass (σ^2))
  unfold velocitySpectrum
  rw [integral_character_of_even hi (fun k => by simp only [weight_neg,rate_neg]) y, Complex.ofReal_im]

private theorem aux_initial_normal (p : MassiveParameters) {σ : ℝ} (hσ : 0 < σ) (y : Spatial) :
    directionalDerivative (velocityWave p σ) (Madelung.coordinateVector 0) (slicePoint 0 y) =
      -Complex.I * GaussianCauchySlice.amplitude σ y := by
  rw [velocityWave, MassShellFourier.initial_normal (inverseLength p) (continuous_velocitySpectrum p σ) (auxMoments p hσ)]
  have he (k : Spatial) : character y k * ((rate (inverseLength p) k : ℝ) : ℂ) * velocitySpectrum p σ k =
      (character y k * (weight (σ^2) k : ℂ)) / (mass (σ^2) : ℂ) := by
    have hr : (rate (inverseLength p) k : ℂ) ≠ 0 := by exact_mod_cast ((mass_positive p).trans_le
      (mass_le_rate (mass_positive p) k)).ne'
    unfold velocitySpectrum
    push_cast
    field_simp
  simp_rw [he]
  rw [integral_div, reconstruct_amplitude hσ]

/-- Global free scalar wave with a specified real Gaussian initial amplitude and independent normal Cauchy rate. -/
def wave (p : MassiveParameters) (σ K freq : ℝ) (x : Covector) : ℂ :=
  combine ((K : ℂ) - Complex.I * freq) (GaussianPositiveFrequencyPacket.packet (inverseLength p) σ x, velocityWave p σ x)

/-- Combining the two smooth Fourier quadratures produces a smooth spacetime wave. -/
theorem smooth_wave (p : MassiveParameters) {σ : ℝ} (hσ : 0 < σ) (K freq : ℝ) :
    ContDiff ℝ ∞ (wave p σ K freq) :=
  (combine ((K : ℂ) - Complex.I * freq)).contDiff.comp
    ((GaussianPositiveFrequencyPacket.smooth_packet (inverseLength p) hσ).prodMk
      (MassShellFourier.smooth_wave (inverseLength p) (continuous_velocitySpectrum p σ) (auxMoments p hσ)))

/-- The mixed wave satisfies the massive free Klein–Gordon equation throughout spacetime. -/
theorem klein_gordon (p : MassiveParameters) {σ : ℝ} (hσ : 0 < σ) (K freq : ℝ) (x : Covector) :
    box (wave p σ K freq) Madelung.coordinateVector x + ((p.m^2*p.c^2/p.hbar^2 : ℝ) : ℂ) * wave p σ K freq x = 0 := by
  have hP := GaussianPositiveFrequencyPacket.smooth_packet (inverseLength p) hσ
  have hQ := MassShellFourier.smooth_wave (inverseLength p) (continuous_velocitySpectrum p σ) (auxMoments p hσ)
  have h := kg_combine ((K : ℂ) - Complex.I * freq) x (hP.of_le (by simp)) (hQ.of_le (by simp))
    (GaussianPositiveFrequencyPacket.klein_gordon (inverseLength p) hσ x)
    (MassShellFourier.klein_gordon (inverseLength p) (continuous_velocitySpectrum p σ) (auxMoments p hσ) x)
  rw [show p.m ^ 2 * p.c ^ 2 / p.hbar ^ 2 = (inverseLength p)^2 by
    simp only [inverseLength, div_pow, mul_pow]]
  exact h

/-- On the full initial slice the mixed field has exactly the real Gaussian amplitude of width σ. -/
theorem initial_value (p : MassiveParameters) {σ : ℝ} (hσ : 0 < σ) (K freq : ℝ) (y : Spatial) :
    wave p σ K freq (slicePoint 0 y) = (GaussianCauchySlice.amplitude σ y : ℂ) := by
  rw [wave, combine_apply, GaussianPositiveFrequencyPacket.initial_value (inverseLength p) hσ, aux_initial_im p hσ]
  simp

/-- Its actual normal derivative is the chosen complex multiple (K−iω)ψ of the initial datum. -/
theorem initial_normal (p : MassiveParameters) {σ : ℝ} (hσ : 0 < σ) (K freq : ℝ) (y : Spatial) :
    directionalDerivative (wave p σ K freq) (Madelung.coordinateVector 0) (slicePoint 0 y) =
      wave p σ K freq (slicePoint 0 y) * ((K : ℂ) - Complex.I * freq) := by
  rw [initial_value p hσ K freq y]
  have hQ : ContDiff ℝ ∞ (velocityWave p σ) :=
    MassShellFourier.smooth_wave (inverseLength p) (continuous_velocitySpectrum p σ) (auxMoments p hσ)
  unfold wave
  rw [directional_combine _ _ _ ((GaussianPositiveFrequencyPacket.smooth_packet (inverseLength p) hσ).differentiable
      (by simp) _) (hQ.differentiable (by simp) _), combine_apply, GaussianPositiveFrequencyPacket.initial_normal (inverseLength p) hσ, aux_initial_normal p hσ]
  simp [Complex.mul_re, Complex.mul_im, mul_comm]

end FoliationQM.GaussianMixedCauchyWave
