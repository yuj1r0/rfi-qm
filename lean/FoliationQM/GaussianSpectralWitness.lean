module

public import FoliationQM.GaussianKGMode

/-!
# A finite Fourier test of the positive-frequency Gaussian normal datum

Source: v13 `eq:dilatation_coercivity_bound` and the width claim in
`thm:adm_positivity`, lines 762–767. On a wave-number axis the
positive-frequency normal coefficient is proportional to
√(μ²+k²) exp(−σ²k²), where μ is the inverse reduced Compton length.
At σμ=1 the values at 0, μ/4 and μ/2 violate a necessary cosine-moment
inequality for nonnegative inverse Fourier data. The proof uses bounds
from the exponential series with a certified remainder.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.GaussianSpectralWitness

/-- Axis profile of the normal coefficient, including an arbitrary spectral prefactor. -/
def profile (C μ σ k : ℝ) : ℝ :=
  C * Real.sqrt (μ^2 + k^2) * Real.exp (-(σ^2 * k^2))

/-- Profile as a function of dimensionless wave number u=k/μ at one Compton width. -/
def shape (u : ℝ) : ℝ := Real.sqrt (1 + u^2) * Real.exp (-(u^2))

/-- At one Compton width the physical profile factors into its zero-mode scale
and a dimensionless shape throughout the wave-number axis. -/
theorem scale_profile (C : ℝ) {μ σ : ℝ} (hμ : 0 < μ) (hσμ : σ*μ = 1) (u : ℝ) :
    profile C μ σ (μ*u) = (C*μ) * shape u := by
  have h₁ : μ^2 + (μ*u)^2 = μ^2 * (1+u^2) := by ring
  have h₂ : σ^2 * (μ*u)^2 = u^2 := by
    calc
      _ = (σ*μ)^2 * u^2 := by ring
      _ = _ := by rw [hσμ]; ring
  rw [profile, h₁, h₂, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hμ.le, shape]
  ring

/-- The spectral scale is the value at zero wave number. -/
theorem profile_zero (C : ℝ) {μ : ℝ} (hμ : 0 < μ) (σ : ℝ) :
    profile C μ σ 0 = C*μ := by simp [profile, Real.sqrt_sq hμ.le]

private theorem exp_first_lower : (9394:ℝ)/10000 < Real.exp (-(1/16:ℝ)) := by
  have h := Real.exp_bound (x := -(1/16:ℝ)) (by norm_num) (n := 5) (by decide)
  rw [abs_le] at h
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  linarith

private theorem exp_second_upper : Real.exp (-(1/4:ℝ)) < (779:ℝ)/1000 := by
  have h := Real.exp_bound (x := -(1/4:ℝ)) (by norm_num) (n := 5) (by decide)
  rw [abs_le] at h
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  linarith

/-- The exact three-frequency difference at one Compton width is strictly negative,
with a rational upper bound independent of the mass and speed scales. -/
theorem shape_witness :
    3 * shape 0 - 4 * shape (1/4) + shape (1/2) < -(1/1000:ℝ) := by
  have hr₁ : (10307:ℝ)/10000 ≤ Real.sqrt (17/16) :=
    Real.le_sqrt_of_sq_le (by norm_num)
  have hr₂ : Real.sqrt (5/4) ≤ (11181:ℝ)/10000 :=
    (Real.sqrt_le_left (by norm_num)).mpr (by norm_num)
  have h₁ := mul_le_mul hr₁ exp_first_lower.le (by norm_num) (Real.sqrt_nonneg _)
  have h₂ := mul_le_mul hr₂ exp_second_upper.le (Real.exp_pos _).le (by norm_num)
  norm_num [shape] at h₁ h₂ ⊢
  linarith

/-- For any positive prefactor and mass scale, σμ=1 yields a strict violation of
the nonnegative cosine-moment condition at the explicit physical frequency μ/4. -/
theorem compton_difference_neg {C μ σ : ℝ} (hC : 0 < C) (hμ : 0 < μ) (hσμ : σ*μ = 1) :
    3 * profile C μ σ 0 - 4 * profile C μ σ (μ/4) + profile C μ σ (2*(μ/4)) < 0 := by
  have hz := scale_profile C hμ hσμ 0
  have h₁ := scale_profile C hμ hσμ (1/4)
  have h₂ := scale_profile C hμ hσμ (1/2)
  rw [mul_zero] at hz
  rw [show μ/4 = μ*(1/4) by ring, show 2*(μ*(1/4)) = μ*(1/2) by ring, hz, h₁, h₂]
  calc
    _ = (C*μ) * (3*shape 0 - 4*shape (1/4) + shape (1/2)) := by ring
    _ < 0 := mul_neg_of_pos_of_neg (mul_pos hC hμ) (shape_witness.trans (by norm_num))

end FoliationQM.GaussianSpectralWitness
