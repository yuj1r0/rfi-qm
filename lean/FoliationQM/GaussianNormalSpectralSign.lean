module

public import FoliationQM.GaussianPositiveFrequencyPacket
public import FoliationQM.GaussianNormalSpectrum
public import FoliationQM.GaussianSpectralApproximation
public import FoliationQM.GaussianSpectralPairing
public import FoliationQM.GaussianSpectralWidth

/-!
# Sign of the actual positive-frequency Gaussian normal coefficient

The free rest-packet clause at v13 line 767 concerns future orientation
throughout the initial slice. The imaginary part of the positive-frequency
packet's actual normal derivative is the negative of a real cosine integral.
Applying the nonnegative trigonometric test with an integrable spatial Gaussian
window, then letting its width tend to infinity, tests this integral without
a decay hypothesis on the inverse transform. Below the necessary spectral width
the coefficient is negative on a set of positive spatial volume.
-/

@[expose] public section
noncomputable section

namespace FoliationQM.GaussianNormalSpectralSign

open Filter LorentzCoordinates MeasureTheory GaussianSpectralApproximation GaussianSpectralPairing
open GaussianNormalSpectrum
open scoped Topology

/-- A nonnegative inverse cosine integral gives a nonnegative three-frequency difference
of its original integrable, even, bounded, continuous spectrum. -/
theorem spectral_difference_nonneg {F : Spatial → ℝ} (hi : Integrable F)
    (hc : Continuous F) {B : ℝ} (hb : ∀ k, |F k| ≤ B) (he : ∀ k, F (-k) = F k)
    (hp : ∀ᵐ y ∂volume, 0 ≤ inverseCosine F y) (u : Spatial) :
    0 ≤ 3 * F 0 - 4 * F u + F ((2 : ℝ) • u) := by
  have ht (v : Spatial) := tendsto_smoothed F hc hb v
  have hlim : Tendsto
      (fun R : ℝ => 3 * smoothed F 0 R - 4 * smoothed F u R + smoothed F ((2 : ℝ) • u) R)
      atTop (𝓝 (3 * F 0 - 4 * F u + F ((2 : ℝ) • u))) :=
    (((ht 0).const_mul 3).sub ((ht u).const_mul 4)).add (ht ((2 : ℝ) • u))
  apply ge_of_tendsto hlim
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
  exact smoothed_difference_nonneg hi he hp hR u

/-- The normalized normal coefficient on the initial slice is the inverse cosine integral
of the mass-shell spectrum divided by its positive Gaussian normalization. -/
theorem coefficient_eq (μ σ : ℝ) (y : Spatial) :
    GaussianPositiveFrequencyPacket.normalCoefficient μ σ y =
      inverseCosine (spectrum μ σ) y / GaussianSpatialFourier.mass (σ ^ 2) := rfl

private theorem axis_difference_nonneg {μ σ : ℝ} (hσ : 0 < σ)
    (hp : ∀ᵐ y ∂volume, 0 ≤ GaussianPositiveFrequencyPacket.normalCoefficient μ σ y)
    (q : ℝ) :
    0 ≤ 3 * GaussianSpectralWitness.profile 1 μ σ 0 - 4 * GaussianSpectralWitness.profile 1 μ σ q +
      GaussianSpectralWitness.profile 1 μ σ (2*q) := by
  obtain ⟨B,hB⟩ := bounded_spectrum μ hσ
  have hpos : ∀ᵐ y ∂volume, 0 ≤ inverseCosine (spectrum μ σ) y := by
    filter_upwards [hp] with y hy
    rw [coefficient_eq] at hy
    simpa only [zero_mul] using (le_div_iff₀ (GaussianSpatialFourier.mass_pos (sq_pos_of_pos hσ))).mp hy
  have h := spectral_difference_nonneg (integrable_spectrum μ hσ) (continuous_spectrum μ σ) hB
    (spectrum_neg μ σ) hpos (GaussianNormalOrientation.axis q)
  rw [axis_two_smul, ← axis_zero, spectrum_axis, spectrum_axis, spectrum_axis] at h
  exact h

/-- Nonnegativity almost everywhere of the packet's actual normal coefficient forces
the squared-width bound σ²μ² ≥ (1+√2)/2. -/
theorem necessary_width {μ σ : ℝ} (hμ : 0 < μ) (hσ : 0 < σ)
    (hp : ∀ᵐ y ∂volume, 0 ≤ GaussianPositiveFrequencyPacket.normalCoefficient μ σ y) :
    (1 + Real.sqrt 2) / 2 ≤ σ^2 * μ^2 :=
  GaussianSpectralWidth.physical_width_bound (C := 1) zero_lt_one hμ
    (fun q _ => axis_difference_nonneg hσ hp q)

private theorem coefficient_ae_nonneg_of_null {μ σ : ℝ}
    (h : volume {y : Spatial | GaussianPositiveFrequencyPacket.normalCoefficient μ σ y < 0} = 0) :
    ∀ᵐ y ∂volume, 0 ≤ GaussianPositiveFrequencyPacket.normalCoefficient μ σ y := by
  rw [ae_iff]
  simpa only [not_le] using h

/-- Below the necessary squared width, the packet's actual normal coefficient is negative
on a set of strictly positive three-dimensional Lebesgue measure. -/
theorem negative_volume_below_width {μ σ : ℝ} (hμ : 0 < μ) (hσ : 0 < σ)
    (hnarrow : σ^2 * μ^2 < (1 + Real.sqrt 2) / 2) :
    0 < volume {y : Spatial | GaussianPositiveFrequencyPacket.normalCoefficient μ σ y < 0} := by
  apply pos_iff_ne_zero.mpr
  intro hz
  exact hnarrow.not_ge (necessary_width hμ hσ (coefficient_ae_nonneg_of_null hz))

/-- At exactly one reduced Compton length, the frequencies 0, μ/4, and μ/2 alone
certify a positive-volume region with negative normal coefficient. -/
theorem negative_volume_at_compton {μ σ : ℝ} (hμ : 0 < μ) (hσ : 0 < σ) (hσμ : σ * μ = 1) :
    0 < volume {y : Spatial | GaussianPositiveFrequencyPacket.normalCoefficient μ σ y < 0} := by
  apply pos_iff_ne_zero.mpr
  intro hz
  exact (GaussianSpectralWitness.compton_difference_neg (C := 1) zero_lt_one hμ hσμ).not_ge
    (axis_difference_nonneg hσ (coefficient_ae_nonneg_of_null hz) (μ / 4))

end FoliationQM.GaussianNormalSpectralSign
