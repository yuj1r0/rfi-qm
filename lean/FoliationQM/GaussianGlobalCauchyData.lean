module

public import FoliationQM.GaussianMixedCauchyWave

/-!
# Global free evolution and the width clause for two Gaussian Cauchy data

The free-Gaussian statement following v13's dilatation inequality (line 767)
concerns the physical field. We use the regular logarithm chart along the
whole positive real initial profile to transfer spacetime solutions to that
inequality at their initial time.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.GaussianGlobalCauchyData

open LorentzCoordinates GaussianCauchySlice OsmoticSliceFields PolarSecondDifferential
open scoped ContDiff

/-- Actual squared modulus of a complex spacetime solution. -/
def density (ψ : Covector → ℂ) (x : Covector) : ℝ := Complex.normSq (ψ x)

/-- Real action from the logarithm chart centered at positive real values. -/
def action (p : MassiveParameters) (ψ : Covector → ℂ) (x : Covector) : ℝ :=
  PolarLocalInverse.localAction p 1 (ψ x)

/-- The polar field from these functions reconstructs the original wave pointwise. -/
theorem reconstruct (p : MassiveParameters) (ψ : Covector → ℂ) :
    ActionDensity.actionField p (density ψ) (action p ψ) = ψ :=
  funext fun x => PolarLocalInverse.localAction_reconstruction p one_ne_zero (ψ x)

/-- A smooth free spacetime solution with Gaussian value and prescribed complex
normal slope supplies regular polar data everywhere on the initial slice. -/
theorem sliceData_of_wave (p : MassiveParameters) {ψ : Covector → ℂ} {σ K freq : ℝ}
    (hσ : 0 < σ) (hfreq : 0 < freq) (hs : ContDiff ℝ ∞ ψ)
    (hval : ∀ y, ψ (slicePoint 0 y) = (amplitude σ y : ℂ))
    (hn : ∀ y, directionalDerivative ψ (Madelung.coordinateVector 0) (slicePoint 0 y) =
      ψ (slicePoint 0 y) * ((K : ℂ) - Complex.I * freq))
    (hkg : ∀ x, box ψ Madelung.coordinateVector x + ((p.m^2*p.c^2/p.hbar^2 : ℝ) : ℂ)*ψ x = 0) :
    GaussianSliceCoercivity.SliceData p (density ψ) (action p ψ) σ K freq := by
  have hr : ContDiff ℝ ∞ (density ψ) := (PolarLocalInverse.contDiff_normSq _).comp hs
  refine ⟨hσ, hfreq, fun _ => hr.contDiffAt.of_le (by simp), ?_, ?_, ?_, ?_, ?_⟩
  · intro y
    have hmem : ψ (slicePoint 0 y) ∈ PolarLocalInverse.chartDomain 1 := by
      rw [hval]
      simpa [PolarLocalInverse.chartDomain] using Complex.ofReal_mem_slitPlane.mpr (amplitude_pos σ y)
    exact ((PolarLocalInverse.contDiffAt_localAction p hmem ∞).comp _ hs.contDiffAt).of_le (by simp)
  · intro y
    rw [density, hval, Complex.normSq_ofReal]
    exact mul_pos (amplitude_pos σ y) (amplitude_pos σ y)
  · simpa only [reconstruct] using hval
  · simpa only [reconstruct] using hn
  · simpa only [reconstruct] using fun y => hkg (slicePoint 0 y)

/-- The global two-branch Fourier solution realizes the regular Gaussian slice data
for every positive width and phase frequency, and every real amplitude rate. -/
theorem realized (p : MassiveParameters) {σ freq : ℝ} (hσ : 0 < σ) (hfreq : 0 < freq) (K : ℝ) :
    let ψ := GaussianMixedCauchyWave.wave p σ K freq
    GaussianSliceCoercivity.SliceData p (density ψ) (action p ψ) σ K freq :=
  sliceData_of_wave p hσ hfreq (GaussianMixedCauchyWave.smooth_wave p hσ K freq)
    (GaussianMixedCauchyWave.initial_value p hσ K freq)
    (GaussianMixedCauchyWave.initial_normal p hσ K freq)
    (GaussianMixedCauchyWave.klein_gordon p hσ K freq)

/-- For a globally free field at one Compton width, a normal amplitude rate 1/σ
gives a future-timelike, zero-drift initial slice where the strict bound fails
and the integrated osmotic square is positive. -/
theorem compton_width_failure (p : MassiveParameters) {freq : ℝ} (hf : 0 < freq) :
    let σ := p.ellC
    let ψ := GaussianMixedCauchyWave.wave p σ (1/σ) freq
    let S := action p ψ
    p.ellC / Real.sqrt 2 < σ ∧
      (∀ y, 0 < ObserverFluxDensity.normalMomentum S (slicePoint 0 y) ∧
        0 < minkowski (DressedMassDensityVariation.phaseDifferential S (slicePoint 0 y))
          (DressedMassDensityVariation.phaseDifferential S (slicePoint 0 y))) ∧
      (∀ y, ObserverFluxDensity.phaseDrift p.c S (slicePoint 0 y) = 0) ∧
      ¬ GaussianSliceCoercivity.DilatationBound p (density ψ) S 0 ∧
      0 < GaussianSliceCoercivity.signedIntegral p (density ψ) := by
  have hσ := ClockScales.ellC_pos p
  have h := realized p hσ hf (1/p.ellC)
  have htwo : 1 < Real.sqrt 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : 0 ≤ (2 : ℝ)), Real.sqrt_nonneg 2]
  refine ⟨(div_lt_iff₀ (by positivity)).mpr ?_, GaussianSliceCoercivity.future_timelike h,
    fun y => (GaussianSliceCoercivity.slice_values h y).1, GaussianSliceCoercivity.inverse_width_datum h⟩
  simpa using mul_lt_mul_of_pos_left htwo hσ

/-- At the identical width and phase frequency, zero normal amplitude rate gives
a globally free field satisfying the strict inequality on the initial slice. -/
theorem compton_width_success (p : MassiveParameters) {freq : ℝ} (hf : 0 < freq) :
    let ψ := GaussianMixedCauchyWave.wave p p.ellC 0 freq
    GaussianSliceCoercivity.DilatationBound p (density ψ) (action p ψ) 0 ∧
      GaussianSliceCoercivity.signedIntegral p (density ψ) < 0 :=
  GaussianSliceCoercivity.pure_imaginary_datum (realized p (ClockScales.ellC_pos p) hf 0)

end FoliationQM.GaussianGlobalCauchyData
