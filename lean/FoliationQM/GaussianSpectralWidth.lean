module

public import FoliationQM.GaussianSpectralWitness
public import FoliationQM.GaussianCosineTest
public import Mathlib.Analysis.Calculus.DerivativeTest

/-!
# A necessary width for the positive-frequency Gaussian cosine test

The positive-frequency normal multiplier of a rest Gaussian, sampled on a
spectral axis, is proportional to √(μ²+k²) exp(−σ²k²). For the
whole-slice future orientation relevant to v13 lines 752–767, a nonnegative
integrable normal coefficient must give a nonnegative three-frequency
cosine test. Write s = (k/μ)² and a = σ²μ². The curvature of that test at
zero gives a necessary lower bound on the width parameter.
-/

@[expose] public section
noncomputable section

namespace FoliationQM.GaussianSpectralWidth
open Filter Set
open scoped Topology

/-- Positive-frequency normal multiplier divided by its central value, as a
function of squared wave number in inverse-Compton units. -/
def profile (a s : ℝ) : ℝ := Real.sqrt (1+s) * Real.exp (-a*s)

/-- The spectral pairing with the nonnegative kernel 2(1−cos θ)². Doubling
the angular wave number multiplies the squared wave number by four. -/
def difference (a s : ℝ) : ℝ := 3 - 4*profile a s + profile a (4*s)

private def slope (a s : ℝ) : ℝ :=
  (1/(2*Real.sqrt (1+s)) - a*Real.sqrt (1+s)) * Real.exp (-a*s)

private theorem sqrt_deriv (s : ℝ) (hs : 0 < 1+s) :
    HasDerivAt (fun x : ℝ => Real.sqrt (1+x)) (1/(2*Real.sqrt (1+s))) s := by
  simpa using ((hasDerivAt_id s).const_add 1).sqrt hs.ne'

private theorem exp_deriv (a s : ℝ) :
    HasDerivAt (fun x : ℝ => Real.exp (-a*x)) (-a*Real.exp (-a*s)) s := by
  simpa [mul_comm] using ((hasDerivAt_id s).const_mul (-a)).exp

private theorem profile_deriv (a s : ℝ) (hs : 0 < 1+s) :
    HasDerivAt (profile a) (slope a s) s := by
  convert (sqrt_deriv s hs).fun_mul (exp_deriv a s) using 1
  · rfl
  unfold slope
  ring

private theorem slope_deriv_zero (a : ℝ) :
    HasDerivAt (slope a) (a^2-a-1/4) 0 := by
  have h := sqrt_deriv 0 (by norm_num)
  have hfac := ((h.const_mul 2).inv (by norm_num)).sub (h.const_mul a)
  have hprod := hfac.mul (exp_deriv a 0)
  convert hprod using 1
  · ext s
    simp [slope, one_div]
  · norm_num
    ring

private theorem diff_deriv (a s : ℝ) (hs : 0 < 1+s) (ht : 0 < 1+4*s) :
    HasDerivAt (difference a) (-(4*slope a s) + 4*slope a (4*s)) s := by
  have h := profile_deriv a s hs
  have h₄ := (profile_deriv a (4*s) ht).comp s ((hasDerivAt_id s).const_mul 4)
  convert ((h.const_mul 4).const_sub 3).add h₄ using 1
  · rfl
  · simp [mul_comm]

/-- At zero frequency the three terms cancel. -/
theorem difference_zero (a : ℝ) : difference a 0 = 0 := by
  simp [difference, profile]
  norm_num

/-- At zero squared frequency the first derivative cancels for every width. -/
theorem deriv_zero (a : ℝ) : deriv (difference a) 0 = 0 := by
  simpa using (diff_deriv a 0 (by norm_num) (by norm_num)).deriv

/-- The actual second derivative at the origin is 12(a²−a−1/4). -/
theorem second_deriv_zero (a : ℝ) :
    deriv (deriv (difference a)) 0 = 12*(a^2-a-1/4) := by
  have he : deriv (difference a) =ᶠ[𝓝 0] fun s => -(4*slope a s) + 4*slope a (4*s) := by
    filter_upwards [lt_mem_nhds (show -(1/4 : ℝ) < 0 by norm_num)] with s hs
    exact (diff_deriv a s (by linarith) (by linarith)).deriv
  have h₄ : HasDerivAt (fun s : ℝ => slope a (4*s)) ((a^2-a-1/4)*4) 0 := by
    have hs : HasDerivAt (fun s : ℝ => 4*s) 4 0 := by simpa using (hasDerivAt_id (0 : ℝ)).const_mul 4
    have h : HasDerivAt (slope a) (a^2-a-1/4) (4*0) := by simpa using slope_deriv_zero a
    exact h.comp 0 hs
  rw [he.deriv_eq]
  convert (((slope_deriv_zero a).const_mul 4).neg.add (h₄.const_mul 4)).deriv using 1
  ring

/-- If the dimensionless curvature is negative, the normalized cosine test is
strictly negative throughout an interval of positive squared frequencies. -/
theorem negative_near_zero {a : ℝ} (ha : a^2-a-1/4 < 0) :
    ∀ᶠ s in 𝓝[>] (0 : ℝ), difference a s < 0 := by
  have hd : deriv (deriv (difference a)) 0 < 0 := by
    rw [second_deriv_zero]; linarith
  have hsign := eventually_nhdsWithin_sign_eq_of_deriv_neg hd (deriv_zero a)
  have hdneg := deriv_neg_right_of_sign_deriv (hsign.filter_mono nhdsWithin_le_nhds)
  obtain ⟨b, hb, hneg⟩ := (nhdsGT_basis (0 : ℝ)).eventually_iff.mp hdneg
  apply (nhdsGT_basis (0 : ℝ)).eventually_iff.mpr
  refine ⟨b, hb, ?_⟩
  intro s hs
  have hcont : Continuous (difference a) := by unfold difference profile; fun_prop
  have hdiff : DifferentiableOn ℝ (difference a) (Ioo 0 s) := by
    intro x hx
    exact (diff_deriv a x (by linarith [hx.1]) (by linarith [hx.1])).differentiableAt.differentiableWithinAt
  obtain ⟨t, ht, he⟩ := exists_deriv_eq_slope (difference a) hs.1 hcont.continuousOn hdiff
  have ht' := hneg (show t ∈ Ioo 0 b from ⟨ht.1, ht.2.trans hs.2⟩)
  rw [he, difference_zero, sub_zero, sub_zero] at ht'
  simpa using (div_lt_iff₀ hs.1).mp ht'

/-- A nonnegative spectral test at all sufficiently small positive squared
frequencies requires a ≥ (1+√2)/2 for a nonnegative width parameter. -/
theorem necessary_width {a : ℝ} (ha : 0 ≤ a)
    (htest : ∀ᶠ s in 𝓝[>] (0 : ℝ), 0 ≤ difference a s) :
    (1+Real.sqrt 2)/2 ≤ a := by
  have hc : 0 ≤ a^2-a-1/4 := by
    by_contra! h
    obtain ⟨s, hs, hn⟩ := (htest.and (negative_near_zero h)).exists
    exact hn.not_ge hs
  have ht : 1 < Real.sqrt 2 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
  by_contra! h
  have hp := mul_neg_of_neg_of_pos (show 2*a-1-Real.sqrt 2 < 0 by linarith)
    (show 0 < 2*a-1+Real.sqrt 2 by linarith)
  nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]

/-- Rescaling k=μu writes the physical Fourier profile at any Gaussian width
as its positive central scale times the dimensionless profile with argument u². -/
theorem rescale_profile (C σ : ℝ) {μ : ℝ} (hμ : 0 < μ) (u : ℝ) :
    GaussianSpectralWitness.profile C μ σ (μ*u) = C*μ * profile (σ^2*μ^2) (u^2) := by
  unfold GaussianSpectralWitness.profile profile
  rw [show μ^2 + (μ*u)^2 = μ^2*(1+u^2) by ring,
    Real.sqrt_mul (sq_nonneg μ), Real.sqrt_sq hμ.le,
    show -(σ^2*(μ*u)^2) = -(σ^2*μ^2)*u^2 by ring]
  ring

/-- The three-frequency test on the physical axis is the dimensionless
difference multiplied by its central scale, at every real u=k/μ. -/
theorem rescale_difference (C σ : ℝ) {μ : ℝ} (hμ : 0 < μ) (u : ℝ) :
    3*GaussianSpectralWitness.profile C μ σ 0 -
      4*GaussianSpectralWitness.profile C μ σ (μ*u) +
      GaussianSpectralWitness.profile C μ σ (2*(μ*u)) =
        C*μ * difference (σ^2*μ^2) (u^2) := by
  rw [GaussianSpectralWitness.profile_zero C hμ σ, rescale_profile C σ hμ,
    show 2*(μ*u) = μ*(2*u) by ring, rescale_profile C σ hμ,
    show (2*u)^2 = 4*u^2 by ring, difference]
  ring

/-- For the physical multiplier C√(μ²+k²)exp(−σ²k²), nonnegativity of the
cosine test at all positive angular wave numbers forces
σ²μ² ≥ (1+√2)/2. -/
theorem physical_width_bound {C μ σ : ℝ} (hC : 0 < C) (hμ : 0 < μ)
    (htest : ∀ k : ℝ, 0 < k →
      0 ≤ 3*GaussianSpectralWitness.profile C μ σ 0 -
        4*GaussianSpectralWitness.profile C μ σ k +
        GaussianSpectralWitness.profile C μ σ (2*k)) :
    (1+Real.sqrt 2)/2 ≤ σ^2*μ^2 := by
  apply necessary_width (mul_nonneg (sq_nonneg σ) (sq_nonneg μ))
  filter_upwards [self_mem_nhdsWithin] with s (hs : 0 < s)
  have h := htest (μ*Real.sqrt s) (mul_pos hμ (Real.sqrt_pos_of_pos hs))
  rw [rescale_difference C σ hμ, Real.sq_sqrt hs.le] at h
  exact (mul_nonneg_iff_of_pos_left (mul_pos hC hμ)).mp h

open LorentzCoordinates MeasureTheory

/-- A real integrable normal coefficient that is nonnegative almost everywhere
and has the Gaussian normal spectrum along a laboratory direction must meet
the strengthened squared-width bound. -/
theorem spatial_width_bound {H : Spatial → ℝ} {C μ σ : ℝ} (e : Spatial)
    (hH : Integrable H) (hp : ∀ᵐ y ∂volume, 0 ≤ H y) (hC : 0 < C) (hμ : 0 < μ)
    (hspec : ∀ q : ℝ, GaussianCosineTest.cosineTransform H (q • e) =
      GaussianSpectralWitness.profile C μ σ q) :
    (1+Real.sqrt 2)/2 ≤ σ^2*μ^2 := by
  apply physical_width_bound hC hμ
  intro k _
  have h := GaussianCosineTest.difference_nonneg hH hp (k • e)
  rw [GaussianCosineTest.difference, ← zero_smul ℝ e, smul_smul, hspec, hspec, hspec] at h
  exact h

/-- Below the necessary squared-width threshold, any integrable real normal
coefficient with the stated axis spectrum is negative on a set of positive
three-dimensional Lebesgue measure. -/
theorem negative_volume_below_width {H : Spatial → ℝ} {C μ σ : ℝ} (e : Spatial)
    (hH : Integrable H) (hC : 0 < C) (hμ : 0 < μ)
    (hspec : ∀ q : ℝ, GaussianCosineTest.cosineTransform H (q • e) =
      GaussianSpectralWitness.profile C μ σ q)
    (hnarrow : σ^2*μ^2 < (1+Real.sqrt 2)/2) :
    0 < volume {y : Spatial | H y < 0} := by
  apply pos_iff_ne_zero.mpr
  intro hz
  have hp : ∀ᵐ y ∂volume, 0 ≤ H y := by
    rw [ae_iff]
    simpa only [not_le] using hz
  exact hnarrow.not_ge (spatial_width_bound e hH hp hC hμ hspec)

end FoliationQM.GaussianSpectralWidth
