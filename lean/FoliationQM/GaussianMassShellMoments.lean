module

public import FoliationQM.GaussianKGMode
public import FoliationQM.GaussianSpatialFourier

/-!
# Gaussian moments on the massive frequency shell

For the positive-frequency Gaussian in the discussion of v13
`eq:dilatation_coercivity_bound`, differentiation of the spacetime Fourier
integral requires absolute moments of the four-dimensional on-shell
covector. On the normal coordinate ct the temporal frequency Ω is precisely
its supremum norm. Gaussian decay gives all the required moment bounds.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.GaussianMassShellMoments
open MeasureTheory LorentzCoordinates GaussianKGMode GaussianSpatialFourier

/-- Reversing the spatial wave vector preserves the positive mass-shell frequency. -/
theorem rate_neg (μ : ℝ) (k : Spatial) : rate μ (-k) = rate μ k := by
  simp [rate, speedSq_eq_sum]

/-- The centered Gaussian is even on the spatial wave-number space. -/
theorem weight_neg (a : ℝ) (k : Spatial) : weight a (-k) = weight a k := by
  simp [weight, speedSq_eq_sum]

/-- Every spatial component of the on-shell wave vector is bounded by its frequency. -/
theorem abs_component_le_rate (μ : ℝ) (k : Spatial) (i : Fin 3) : |k i| ≤ rate μ k := by
  apply Real.abs_le_sqrt
  rw [speedSq_eq_sum]
  fin_cases i <;> dsimp <;> nlinarith [sq_nonneg μ, sq_nonneg (k 0), sq_nonneg (k 1), sq_nonneg (k 2)]

/-- For the laboratory supremum norm the full covector (Ω,−k) has norm exactly Ω. -/
theorem norm_shell (μ : ℝ) (k : Spatial) : ‖assemble (rate μ k) (-k)‖ = rate μ k := by
  have hr : 0 ≤ rate μ k := Real.sqrt_nonneg _
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg hr).mpr
    intro i
    fin_cases i
    · simp [assemble, Real.norm_eq_abs, abs_of_nonneg hr]
    · simpa [assemble, Real.norm_eq_abs] using abs_component_le_rate μ k 0
    · simpa [assemble, Real.norm_eq_abs] using abs_component_le_rate μ k 1
    · simpa [assemble, Real.norm_eq_abs] using abs_component_le_rate μ k 2
  · simpa [assemble, Real.norm_eq_abs, abs_of_nonneg hr] using
      norm_le_pi_norm (assemble (rate μ k) (-k)) 0

private theorem rate_exp_bound {a : ℝ} (ha : 0 < a) (μ : ℝ) (k : Spatial) :
    rate μ k - a * speedSq k ≤ (a*μ^2/2 + 1/(2*a)) - (a/2) * speedSq k := by
  have hq := sq_nonneg (a * rate μ k - 1)
  have he := rate_sq μ k
  have hh : rate μ k ≤ (a^2 * (μ^2+speedSq k) + 1)/(2*a) := by
    apply (le_div_iff₀ (by positivity)).mpr
    nlinarith only [hq, congrArg (fun t : ℝ => a^2*t) he]
  have hsplit : (a^2 * (μ^2+speedSq k)+1)/(2*a) =
      a*(μ^2+speedSq k)/2 + 1/(2*a) := by field_simp
  rw [hsplit] at hh
  linarith

/-- Every natural moment of the temporal frequency is integrable with the Gaussian spectrum. -/
theorem integrable_rate_pow_weight {a : ℝ} (ha : 0 < a) (μ : ℝ) (n : ℕ) :
    Integrable (fun k : Spatial => rate μ k ^ n * weight a k) := by
  let C : ℝ := (n.factorial : ℝ) * Real.exp (a*μ^2/2 + 1/(2*a))
  apply ((integrable_weight (half_pos ha)).const_mul C).mono'
    (by unfold rate weight speedSq spatialDot; fun_prop)
  refine ae_of_all _ fun k => ?_
  have hr : 0 ≤ rate μ k := Real.sqrt_nonneg _
  have hw : 0 ≤ weight a k := (Real.exp_pos _).le
  have hf : rate μ k ^ n ≤ (n.factorial : ℝ) * Real.exp (rate μ k) := by
    have h := (div_le_iff₀ (by positivity : 0 < (n.factorial : ℝ))).mp
      (Real.pow_div_factorial_le_exp (rate μ k) hr n)
    linarith
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (pow_nonneg hr _) hw)]
  calc
    _ ≤ ((n.factorial : ℝ) * Real.exp (rate μ k)) * weight a k :=
      mul_le_mul_of_nonneg_right hf hw
    _ = (n.factorial : ℝ) * Real.exp (rate μ k - a * speedSq k) := by
      rw [weight, mul_assoc, ← Real.exp_add]
      ring_nf
    _ ≤ (n.factorial : ℝ) * Real.exp ((a*μ^2/2 + 1/(2*a)) - (a/2) * speedSq k) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (rate_exp_bound ha μ k)) (by positivity)
    _ = C * weight (a / 2) k := by
      dsimp only [C, weight]; rw [mul_assoc, ← Real.exp_add]; ring_nf

/-- The inverse-frequency Gaussian also has every natural mass-shell moment at positive mass. -/
theorem integrable_rate_pow_div_rate_weight {a μ : ℝ} (ha : 0 < a) (hμ : 0 < μ) (n : ℕ) :
    Integrable (fun k : Spatial => rate μ k ^ n * (weight a k / rate μ k)) := by
  apply ((integrable_rate_pow_weight ha μ n).div_const μ).mono'
    (by unfold rate weight speedSq spatialDot; fun_prop)
  refine ae_of_all _ fun k => ?_
  have hr := mass_le_rate hμ k
  have hw : 0 ≤ weight a k := (Real.exp_pos _).le
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (pow_nonneg (hμ.trans_le hr).le _) (div_nonneg hw (hμ.trans_le hr).le)),
    ← mul_div_assoc]
  exact div_le_div_of_nonneg_left (mul_nonneg (pow_nonneg (hμ.trans_le hr).le _) hw) hμ hr

/-- Multiplying an integrable real coefficient by the complex angular character gives an integrable wave. -/
theorem integrable_character {H : Spatial → ℝ} (hf : Integrable H) (y : Spatial) :
    Integrable (fun k => character y k * (H k : ℂ)) := by
  apply hf.ofReal.bdd_mul (c := 1) (by unfold character spatialDot; fun_prop)
  refine ae_of_all _ fun k => ?_
  simp [character, mul_comm Complex.I, Complex.norm_exp_ofReal_mul_I]

/-- For a real even integrable spectrum the angular Fourier integral equals its real cosine integral.
The imaginary sine contribution cancels under reversal of all three wave-number coordinates. -/
theorem integral_character_of_even {H : Spatial → ℝ} (hf : Integrable H)
    (hev : ∀ k, H (-k) = H k) (y : Spatial) :
    (∫ k, character y k * (H k : ℂ)) = ((∫ k, Real.cos (spatialDot k y) * H k : ℝ) : ℂ) := by
  let s := fun k : Spatial => Real.sin (spatialDot k y) * H k
  have hs (k : Spatial) : s (-k) = -s k := by
    dsimp only [s]
    have hd : spatialDot (-k) y = -spatialDot k y := by simp [spatialDot]; ring
    rw [hd, Real.sin_neg, hev, neg_mul]
  have hz : (∫ k, s k) = 0 := by
    have h := integral_neg_eq_self (μ := (volume : Measure Spatial)) s
    have hn : (∫ k, s (-k)) = -(∫ k, s k) := by simp_rw [hs]; exact integral_neg _
    linarith
  apply Complex.ext
  · have h := integral_re (integrable_character hf y)
    simpa only [RCLike.re_eq_complex_re, character, mul_comm Complex.I, Complex.mul_re,
      Complex.exp_ofReal_mul_I_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero] using h.symm
  · have h := integral_im (integrable_character hf y)
    simp only [RCLike.im_eq_complex_im, character, mul_comm Complex.I, Complex.mul_im,
      Complex.exp_ofReal_mul_I_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_add] at h
    simpa only [character, mul_comm Complex.I, Complex.ofReal_im] using h.symm.trans hz

/-- The normal Fourier coefficient of the Gaussian is a real cosine transform of Ω times the Gaussian. -/
theorem integral_character_rate_weight_real {a : ℝ} (ha : 0 < a) (μ : ℝ) (y : Spatial) :
    (∫ k, character y k * ((rate μ k * weight a k : ℝ) : ℂ)) =
    ((∫ k, Real.cos (spatialDot k y) * (rate μ k * weight a k) : ℝ) : ℂ) := by
  apply integral_character_of_even
  · simpa using integrable_rate_pow_weight ha μ 1
  · intro k; rw [rate_neg, weight_neg]

end FoliationQM.GaussianMassShellMoments
