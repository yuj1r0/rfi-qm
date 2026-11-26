module

public import FoliationQM.GaussianPositiveFrequencyPacket
public import FoliationQM.PolynomialSpectralMoments

/-!
# Actual polynomial moments and normalization of the Gaussian spectrum

Source: v13 `cor:schrodinger`, component kinds C and D. One fixed positive
width supplies continuous spectral data with all actual spatial polynomial
moments. The normalization is spectral L¹ mass and initial central amplitude;
it is not a claim of unit spatial L² mass or probability normalization.
-/

@[expose] public section
noncomputable section

namespace FoliationQM.GaussianSpectralMoments

open MeasureTheory LorentzCoordinates GaussianSpatialFourier GaussianKGMode
open GaussianPositiveFrequencyPacket PolynomialSpectralMoments

private theorem norm_spectrum {σ : ℝ} (hσ : 0 < σ) (k : Spatial) :
    ‖spectrum σ k‖ = weight (σ ^ 2) k / mass (σ ^ 2) := by
  have hw : 0 < weight (σ ^ 2) k := Real.exp_pos _
  rw [GaussianPositiveFrequencyPacket.spectrum, norm_div, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hw,
    abs_of_pos (mass_pos (sq_pos_of_pos hσ))]

/-- A single positive-width Gaussian spectrum is continuous and has every genuine spatial polynomial moment. -/
theorem spectrum_data {σ : ℝ} (hσ : 0 < σ) :
    Continuous (spectrum σ) ∧ PolynomialMoments (spectrum σ) := by
  constructor
  · unfold GaussianPositiveFrequencyPacket.spectrum weight speedSq spatialDot
    fun_prop
  · intro n
    have h := GaussianMassShellMoments.integrable_rate_pow_weight
      (sq_pos_of_pos hσ) 0 (2 * n)
    have hp (k : Spatial) : rate 0 k ^ (2 * n) = speedSq k ^ n := by
      rw [pow_mul, rate_sq]
      simp
    simp_rw [hp] at h
    simpa only [norm_spectrum hσ, ← mul_div_assoc] using h.div_const (mass (σ ^ 2))

/-- The actual spectrum and its norm are integrable, with both integrals equal to one; this is spectral L¹ normalization. -/
theorem spectrum_normalization {σ : ℝ} (hσ : 0 < σ) :
    Integrable (spectrum σ) ∧ Integrable (fun k => ‖spectrum σ k‖) ∧
      (∫ k, ‖spectrum σ k‖) = 1 ∧ (∫ k, spectrum σ k) = (1 : ℂ) := by
  have ha := sq_pos_of_pos hσ
  have hi : Integrable (fun k => weight (σ ^ 2) k / mass (σ ^ 2)) :=
    (integrable_weight ha).div_const _
  have hs : spectrum σ = fun k => ((weight (σ ^ 2) k / mass (σ ^ 2) : ℝ) : ℂ) := by
    funext k
    simp only [GaussianPositiveFrequencyPacket.spectrum, Complex.ofReal_div]
  have hcomplex : Integrable (spectrum σ) := by
    rw [hs]
    exact hi.ofReal
  have hnorm : Integrable (fun k => ‖spectrum σ k‖) := by
    simpa only [norm_spectrum hσ] using hi
  have hz : (∫ k, weight (σ ^ 2) k / mass (σ ^ 2)) = 1 := by
    rw [integral_div, integral_weight ha, div_self (mass_pos ha).ne']
  refine ⟨hcomplex, hnorm, ?_, ?_⟩
  · simpa only [norm_spectrum hσ] using hz
  · rw [hs, integral_complex_ofReal, hz]
    rfl

end FoliationQM.GaussianSpectralMoments
