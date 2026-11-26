module

public import FoliationQM.MassShellFourier
public import FoliationQM.GaussianMassShellMoments
public import FoliationQM.SpatialFisherEnergy

/-!
# The normalized positive-frequency Gaussian packet

For the free example in v13, lines 752–767, the positive-energy branch of
the mass shell evolves the spatial Gaussian spectrum with the phase
exp(i k·y − i Ω x⁰), where x⁰ = ct. The same spacetime field solves
Klein–Gordon and realizes both initial data. Its real normal coefficient is
the inverse cosine transform of the rate-weighted spectrum.
-/

@[expose] public section
noncomputable section

namespace FoliationQM.GaussianPositiveFrequencyPacket

open LorentzCoordinates GaussianSpatialFourier GaussianKGMode MeasureTheory
open OsmoticSliceFields PolarSecondDifferential
open scoped ContDiff Topology

/-- The Gaussian angular spectrum divided by its total spectral mass. -/
def spectrum (σ : ℝ) (k : Spatial) : ℂ :=
  (weight (σ ^ 2) k : ℂ) / (mass (σ ^ 2) : ℂ)

/-- The spacetime packet on the branch with time factor exp(−i Ω x⁰). -/
def packet (μ σ : ℝ) : Covector → ℂ := MassShellFourier.wave μ (spectrum σ)

/-- Real coefficient of the initial normal derivative, in x⁰ coordinates. -/
def normalCoefficient (μ σ : ℝ) (y : Spatial) : ℝ :=
  (∫ k, Real.cos (spatialDot k y) * (rate μ k * weight (σ ^ 2) k)) / mass (σ ^ 2)

private theorem continuous_spectrum (σ : ℝ) : Continuous (spectrum σ) := by
  unfold spectrum weight speedSq spatialDot
  fun_prop

private theorem spectrum_moments (μ : ℝ) {σ : ℝ} (hσ : 0 < σ) :
    MassShellFourier.HasMoments μ (spectrum σ) := by
  intro n
  have ha := sq_pos_of_pos hσ
  have hn (k : Spatial) : ‖spectrum σ k‖ = weight (σ ^ 2) k / mass (σ ^ 2) := by
    have hw : 0 < weight (σ ^ 2) k := Real.exp_pos _
    rw [spectrum, norm_div, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (mass_pos ha), abs_of_pos hw]
  simp_rw [MassShellFourier.shell, GaussianMassShellMoments.norm_shell, hn, ← mul_div_assoc]
  exact (GaussianMassShellMoments.integrable_rate_pow_weight ha μ n).div_const _

/-- Every positive-width packet is smooth on all of spacetime. -/
theorem smooth_packet (μ : ℝ) {σ : ℝ} (hσ : 0 < σ) : ContDiff ℝ ∞ (packet μ σ) :=
  MassShellFourier.smooth_wave μ (continuous_spectrum σ) (spectrum_moments μ hσ)

/-- The integrated packet satisfies the flat (+---) Klein–Gordon equation. -/
theorem klein_gordon (μ : ℝ) {σ : ℝ} (hσ : 0 < σ) (x : Covector) :
    box (packet μ σ) Madelung.coordinateVector x + ((μ ^ 2 : ℝ) : ℂ) * packet μ σ x = 0 :=
  MassShellFourier.klein_gordon μ (continuous_spectrum σ) (spectrum_moments μ hσ) x

/-- For inverse Compton length μ = mc/ℏ, the coefficient of the physical
Klein–Gordon equation is m²c²/ℏ². -/
theorem massive_klein_gordon (p : MassiveParameters) {σ : ℝ} (hσ : 0 < σ) (x : Covector) :
    box (packet (p.m * p.c / p.hbar) σ) Madelung.coordinateVector x +
      ((p.m ^ 2 * p.c ^ 2 / p.hbar ^ 2 : ℝ) : ℂ) * packet (p.m * p.c / p.hbar) σ x = 0 := by
  simpa only [div_pow, mul_pow] using klein_gordon (p.m * p.c / p.hbar) hσ x

/-- The actual wave on the initial observer slice equals the spatial Gaussian. -/
theorem initial_value (μ : ℝ) {σ : ℝ} (hσ : 0 < σ) (y : Spatial) :
    packet μ σ (slicePoint 0 y) = (GaussianCauchySlice.amplitude σ y : ℂ) := by
  rw [packet, MassShellFourier.initial_value]
  simp_rw [spectrum, ← mul_div_assoc]
  rw [integral_div]
  exact reconstruct_amplitude hσ y

/-- At each initial point the normal derivative is −i times the real cosine
transform of the normalized rate-weighted spectrum. -/
theorem initial_normal (μ : ℝ) {σ : ℝ} (hσ : 0 < σ) (y : Spatial) :
    directionalDerivative (packet μ σ) (Madelung.coordinateVector 0) (slicePoint 0 y) =
      -Complex.I * (normalCoefficient μ σ y : ℂ) := by
  rw [packet, MassShellFourier.initial_normal μ (continuous_spectrum σ) (spectrum_moments μ hσ)]
  simp_rw [spectrum, ← mul_div_assoc, mul_assoc (character y _), ← Complex.ofReal_mul]
  rw [integral_div, GaussianMassShellMoments.integral_character_rate_weight_real (sq_pos_of_pos hσ),
    normalCoefficient, Complex.ofReal_div]

/-- The real normal coefficient is smooth on the spatial slice because it is
the negative imaginary part of the normal derivative of the smooth packet. -/
theorem smooth_normalCoefficient (μ : ℝ) {σ : ℝ} (hσ : 0 < σ) :
    ContDiff ℝ ∞ (normalCoefficient μ σ) := by
  let d := directionalDerivative (packet μ σ) (Madelung.coordinateVector 0)
  have hd : ContDiff ℝ ∞ d :=
    ((smooth_packet μ hσ).fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  have hs : ContDiff ℝ ∞ (fun y => -(d (slicePoint 0 y)).im) :=
    (Complex.imCLM.contDiff.comp (hd.comp (SpatialFisherEnergy.contDiff_slicePoint 0 ∞))).neg
  have he (y : Spatial) : -(d (slicePoint 0 y)).im = normalCoefficient μ σ y := by
    dsimp only [d]
    rw [initial_normal μ hσ y]
    simp [Complex.mul_im]
  simpa only [he] using hs

/-- The central normal coefficient is bounded below by the positive rest
rate, since every mass-shell frequency is at least the rest rate. -/
theorem mass_le_normal_center {μ σ : ℝ} (hμ : 0 < μ) (hσ : 0 < σ) :
    μ ≤ normalCoefficient μ σ 0 := by
  have ha := sq_pos_of_pos hσ
  simp only [normalCoefficient, spatialDot, Pi.zero_apply, mul_zero, add_zero, Real.cos_zero, one_mul]
  apply (le_div_iff₀ (mass_pos ha)).mpr
  calc
    μ * mass (σ ^ 2) = ∫ k, μ * weight (σ ^ 2) k := by rw [integral_const_mul, integral_weight ha]
    _ ≤ ∫ k, rate μ k * weight (σ ^ 2) k := by
      apply integral_mono ((integrable_weight ha).const_mul μ)
      · simpa only [pow_one] using GaussianMassShellMoments.integrable_rate_pow_weight ha μ 1
      · exact fun k => mul_le_mul_of_nonneg_right (mass_le_rate hμ k) (Real.exp_pos _).le

/-- A massive positive-frequency packet has a strictly positive normal
coefficient at its spatial center. -/
theorem normal_center_pos {μ σ : ℝ} (hμ : 0 < μ) (hσ : 0 < σ) :
    0 < normalCoefficient μ σ 0 := hμ.trans_le (mass_le_normal_center hμ hσ)

/-- Strict positivity of the massive normal coefficient holds throughout
some spatial neighborhood of the packet center. -/
theorem eventually_normal_pos {μ σ : ℝ} (hμ : 0 < μ) (hσ : 0 < σ) :
    ∀ᶠ y in 𝓝 (0 : Spatial), 0 < normalCoefficient μ σ y :=
  (smooth_normalCoefficient μ hσ).continuous.continuousAt.eventually
    (Ioi_mem_nhds (normal_center_pos hμ hσ))

end FoliationQM.GaussianPositiveFrequencyPacket
