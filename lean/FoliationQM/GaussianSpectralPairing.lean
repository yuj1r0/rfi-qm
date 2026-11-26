module

public import FoliationQM.GaussianCosineTest
public import FoliationQM.GaussianSpectralApproximation
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Gaussian pairing for an inverse angular cosine transform on ℝ³

For the free Gaussian clause of v13, line 767, a positive spatial window
allows the sign of an actual normal coefficient to be tested by three
frequency samples. Fubini's theorem and the Gaussian Fourier integral
identify each windowed spatial sample with a smoothed spectral value.
-/

@[expose] public section
noncomputable section

namespace FoliationQM.GaussianSpectralPairing

open LorentzCoordinates GaussianSpatialFourier GaussianCosineTest MeasureTheory

/-- Inverse spatial cosine integral for an angular wave-number spectrum. -/
def inverseCosine (F : Spatial → ℝ) (y : Spatial) : ℝ :=
  ∫ k, Real.cos (spatialDot k y) * F k

private theorem sine_integral_zero {F : Spatial → ℝ} (he : ∀ k, F (-k) = F k) (y : Spatial) :
    (∫ k, Real.sin (spatialDot k y) * F k) = 0 := by
  let s := fun k : Spatial => Real.sin (spatialDot k y) * F k
  have h (k : Spatial) : s (-k) = -s k := by
    have hd : spatialDot (-k) y = -spatialDot k y := by simp [spatialDot]; ring
    simp only [s, hd, Real.sin_neg, he, neg_mul]
  have hi := integral_neg_eq_self (μ := (volume : Measure Spatial)) s
  have hn : (∫ k, s (-k)) = -(∫ k, s k) := by simp_rw [h]; exact integral_neg _
  change (∫ k, s k) = 0
  linarith

private theorem modulate {F : Spatial → ℝ} (hF : Integrable F) (he : ∀ k, F (-k) = F k)
    (u y : Spatial) :
    (∫ k, Real.cos (spatialDot (k-u) y) * F k) = Real.cos (spatialDot y u) * inverseCosine F y := by
  have hd (k : Spatial) : spatialDot (k-u) y = spatialDot k y - spatialDot u y := by
    simp [spatialDot]; ring
  have hp (k : Spatial) : Real.cos (spatialDot (k-u) y) * F k =
      Real.cos (spatialDot u y) * (Real.cos (spatialDot k y) * F k) +
      Real.sin (spatialDot u y) * (Real.sin (spatialDot k y) * F k) := by
    rw [hd, Real.cos_sub]
    ring
  have hc : Integrable (fun k => Real.cos (spatialDot k y) * F k) :=
    hF.bdd_mul (by unfold spatialDot; fun_prop) (ae_of_all _ fun k => Real.abs_cos_le_one _)
  have hs : Integrable (fun k => Real.sin (spatialDot k y) * F k) :=
    hF.bdd_mul (by unfold spatialDot; fun_prop) (ae_of_all _ fun k => Real.abs_sin_le_one _)
  rw [funext hp, integral_add (hc.const_mul _) (hs.const_mul _), integral_const_mul, integral_const_mul,
    sine_integral_zero he, mul_zero, add_zero, spatialDot_comm u y, inverseCosine]

private def pairingIntegrand (F : Spatial → ℝ) (a : ℝ) (u y k : Spatial) : ℝ :=
  (weight a y * F k) * Real.cos (spatialDot y (k-u))

private theorem integrable_pairing {F : Spatial → ℝ} (hF : Integrable F) {a : ℝ} (ha : 0 < a)
    (u : Spatial) : Integrable (Function.uncurry (pairingIntegrand F a u)) (volume.prod volume) := by
  exact ((integrable_weight ha).mul_prod hF).mul_bdd
    (by dsimp [Function.uncurry, pairingIntegrand, spatialDot]; fun_prop)
    (ae_of_all _ fun z => Real.abs_cos_le_one (spatialDot z.1 (z.2-u)))

private theorem integrate_frequency (F : Spatial → ℝ) (a : ℝ) (u y : Spatial) :
    (∫ k, pairingIntegrand F a u y k) = weight a y * ∫ k, Real.cos (spatialDot (k-u) y) * F k := by
  rw [← integral_const_mul]
  exact integral_congr_ae (ae_of_all _ fun k => by
    rw [pairingIntegrand, spatialDot_comm y]; ring)

/-- Every positive Gaussian window makes the inverse cosine transform of an
integrable spectrum integrable on the full spatial slice. -/
theorem integrable_window {F : Spatial → ℝ} (hF : Integrable F) {a : ℝ} (ha : 0 < a) :
    Integrable (fun y => weight a y * inverseCosine F y) := by
  have h := (integrable_pairing hF ha 0).integral_prod_left
  change Integrable (fun y => ∫ k, pairingIntegrand F a 0 y k) at h
  simpa only [integrate_frequency, sub_zero, inverseCosine] using h

private theorem integrate_space (F : Spatial → ℝ) {a : ℝ} (ha : 0 < a) (u k : Spatial) :
    (∫ y, pairingIntegrand F a u y k) = mass a * (F k * weight (1/(4*a)) (k-u)) := by
  calc
    _ = F k * ∫ y, Real.cos (spatialDot y (k-u)) * weight a y := by
      rw [← integral_const_mul]
      exact integral_congr_ae (ae_of_all _ fun y => by unfold pairingIntegrand; ring)
    _ = _ := by
      rw [integral_cosine_weight ha]
      have hw : Real.exp (-speedSq (k-u)/(4*a)) = weight (1/(4*a)) (k-u) := by
        unfold weight
        congr 1
        ring
      rw [hw]
      ring

/-- The cosine transform of the Gaussian-windowed inverse of an even
integrable spectrum is its convolution with the dual Gaussian, multiplied
by the spatial Gaussian mass. -/
theorem gaussian_pairing {F : Spatial → ℝ} (hF : Integrable F) (he : ∀ k, F (-k) = F k)
    {a : ℝ} (ha : 0 < a) (u : Spatial) :
    cosineTransform (fun y => weight a y * inverseCosine F y) u =
      mass a * ∫ k, F k * weight (1/(4*a)) (k-u) := by
  have hx (y : Spatial) : (∫ k, pairingIntegrand F a u y k) =
      weight a y * inverseCosine F y * Real.cos (spatialDot y u) := by
    rw [integrate_frequency, modulate hF he]; ring
  rw [cosineTransform, ← funext hx, integral_integral_swap (integrable_pairing hF ha u)]
  simp_rw [integrate_space F ha u, integral_const_mul]

open GaussianSpectralApproximation

/-- Each normalized Gaussian spectral average is a positive scalar multiple
of the spatial cosine test with the reciprocal Gaussian window. -/
theorem smoothed_eq_window {F : Spatial → ℝ} (hF : Integrable F) (he : ∀ k, F (-k) = F k)
    {R : ℝ} (hR : 0 < R) (u : Spatial) :
    smoothed F u R = (R ^ 3 / mass 1 / mass (1/(4*R^2))) *
      cosineTransform (fun y => weight (1/(4*R^2)) y * inverseCosine F y) u := by
  have ha : 0 < 1/(4*R^2) := by positivity
  rw [gaussian_pairing hF he ha, smoothed]
  rw [show 1/(4*(1/(4*R^2))) = R^2 by field_simp [hR.ne']]
  rw [← mul_assoc, div_mul_cancel₀ _ (mass_pos ha).ne']

/-- Nonnegativity almost everywhere of the actual inverse cosine integral
forces a nonnegative three-frequency difference at every positive smoothing
scale. Only the spectral amplitude is required to be integrable. -/
theorem smoothed_difference_nonneg {F : Spatial → ℝ} (hF : Integrable F) (he : ∀ k, F (-k) = F k)
    (hp : ∀ᵐ y ∂volume, 0 ≤ inverseCosine F y) {R : ℝ} (hR : 0 < R) (u : Spatial) :
    0 ≤ 3*smoothed F 0 R - 4*smoothed F u R + smoothed F ((2 : ℝ) • u) R := by
  let a : ℝ := 1/(4*R^2)
  have ha : 0 < a := by dsimp only [a]; positivity
  have h := difference_nonneg (integrable_window hF ha)
    (hp.mono fun y hy => mul_nonneg (Real.exp_pos _ : 0 < weight a y).le hy) u
  have hc : 0 ≤ R^3 / mass 1 / mass a :=
    div_nonneg (div_nonneg (pow_nonneg hR.le _) (mass_pos zero_lt_one).le) (mass_pos ha).le
  unfold difference at h
  simp_rw [smoothed_eq_window hF he hR]
  dsimp only [a] at h hc
  linarith only [mul_nonneg hc h]

end FoliationQM.GaussianSpectralPairing
