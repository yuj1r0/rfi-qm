module

public import FoliationQM.GaussianPositiveFrequencyPacket

/-!
# Normal-time curvature of Gaussian modulus density at its center

For the positive-frequency rest packet in the v13 Gaussian width clause, the
unit-peak initial modulus has zero first normal derivative at its center.
The second normal derivative there measures the spread of the full massive
frequency spectrum. All time derivatives below use s=x⁰=ct.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.GaussianCenterFrequencyVariance

open LorentzCoordinates GaussianSpatialFourier GaussianKGMode GaussianPositiveFrequencyPacket
open MeasureTheory OsmoticSliceFields PolarSecondDifferential
open scoped ContDiff

/-- The nth frequency moment under the normalized spatial Gaussian spectrum. -/
def moment (μ σ : ℝ) (n : ℕ) : ℝ :=
  (∫ k, (rate μ k)^n * weight (σ^2) k) / mass (σ^2)

/-- Variance of the rest packet's massive frequency with its spectral weight. -/
def variance (μ σ : ℝ) : ℝ := moment μ σ 2 - (moment μ σ 1)^2

/-- Normal-time trace of the actual spacetime packet at the spatial origin. -/
def centerWave (μ σ s : ℝ) : ℂ := packet μ σ (slicePoint s 0)

/-- Squared modulus of that center trace. -/
def centerDensity (μ σ s : ℝ) : ℝ := Complex.normSq (centerWave μ σ s)

private def amplitudeN (μ σ : ℝ) (n : ℕ) (k : Spatial) : ℂ :=
  ((rate μ k ^ n * weight (σ^2) k / mass (σ^2) : ℝ) : ℂ)

private def traceN (μ σ : ℝ) (n : ℕ) (s : ℝ) : ℂ :=
  MassShellFourier.wave μ (amplitudeN μ σ n) (slicePoint s 0)

private theorem continuous_amplitudeN (μ σ : ℝ) (n : ℕ) : Continuous (amplitudeN μ σ n) := by
  unfold amplitudeN rate weight speedSq spatialDot
  fun_prop

private theorem amplitudeN_moments (μ : ℝ) {σ : ℝ} (hσ : 0 < σ) (n : ℕ) :
    MassShellFourier.HasMoments μ (amplitudeN μ σ n) := by
  intro m
  have ha := sq_pos_of_pos hσ
  have h (k : Spatial) : ‖MassShellFourier.shell μ k‖^m * ‖amplitudeN μ σ n k‖ =
      (rate μ k)^(m+n) * weight (σ^2) k / mass (σ^2) := by
    have hr : 0 ≤ rate μ k := Real.sqrt_nonneg _
    have hw : 0 < weight (σ^2) k := Real.exp_pos _
    rw [MassShellFourier.shell, GaussianMassShellMoments.norm_shell, amplitudeN, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (div_nonneg (mul_nonneg (pow_nonneg hr _) hw.le) (mass_pos ha).le),
      pow_add]
    ring
  simp_rw [h]
  exact (GaussianMassShellMoments.integrable_rate_pow_weight ha μ _).div_const _

private theorem hasDerivAt_centerLine (s : ℝ) :
    HasDerivAt (fun r : ℝ => slicePoint r 0) (Madelung.coordinateVector 0) s := by
  have h : (fun r : ℝ => slicePoint r 0) = fun r : ℝ => r • Madelung.coordinateVector 0 := by
    funext r
    ext i
    fin_cases i <;> simp [slicePoint, assemble, Madelung.coordinateVector]
  rw [h]
  simpa using (hasDerivAt_id s).smul_const (Madelung.coordinateVector 0)

private theorem hasDerivAt_traceN (μ : ℝ) {σ : ℝ} (hσ : 0 < σ) (n : ℕ) (s : ℝ) :
    HasDerivAt (traceN μ σ n) (-Complex.I * traceN μ σ (n+1) s) s := by
  let A := amplitudeN μ σ n
  let x := slicePoint s 0
  have hc := continuous_amplitudeN μ σ n
  have hm := amplitudeN_moments μ hσ n
  have h := ((MassShellFourier.smooth_wave μ hc hm).differentiable (by simp) x).hasFDerivAt.comp_hasDerivAt s
    (hasDerivAt_centerLine s)
  change HasDerivAt (traceN μ σ n)
    (directionalDerivative (MassShellFourier.wave μ A) (Madelung.coordinateVector 0) x) s at h
  rw [MassShellFourier.first_coordinate μ hc hm] at h
  convert h using 1
  change -Complex.I * (∫ k, MassShellFourier.mode μ k x * amplitudeN μ σ (n+1) k) = _
  rw [← integral_const_mul]
  apply integral_congr_ae
  exact ae_of_all _ fun k => by
    simp only [MassShellFourier.differentiated, MassShellFourier.shell,
      show assemble (rate μ k) (-k) 0 = rate μ k from rfl, amplitudeN, pow_succ,
      Complex.ofReal_div, Complex.ofReal_mul]
    ring

private theorem traceN_initial (μ σ : ℝ) (n : ℕ) : traceN μ σ n 0 = (moment μ σ n : ℂ) := by
  rw [traceN, MassShellFourier.initial_value]
  simp only [character, spatialDot, Pi.zero_apply, mul_zero, add_zero, Complex.ofReal_zero,
    Complex.exp_zero, one_mul, amplitudeN, integral_complex_ofReal, integral_div, moment]

private theorem trace_zero_eq (μ σ : ℝ) : traceN μ σ 0 = centerWave μ σ := by
  have h : amplitudeN μ σ 0 = GaussianPositiveFrequencyPacket.spectrum σ := by
    funext k
    simp [amplitudeN, GaussianPositiveFrequencyPacket.spectrum]
  funext s
  simp only [traceN, h, centerWave, packet]

/-- The normalization gives center value one at initial time. -/
theorem centerWave_zero (μ : ℝ) {σ : ℝ} (hσ : 0 < σ) : centerWave μ σ 0 = 1 := by
  rw [centerWave, initial_value μ hσ]
  simp [GaussianCauchySlice.amplitude, speedSq, spatialDot]

/-- The center wave's first normal derivative is minus i times the first
frequency moment of the actual Gaussian spectrum. -/
theorem hasDerivAt_centerWave_zero (μ : ℝ) {σ : ℝ} (hσ : 0 < σ) :
    HasDerivAt (centerWave μ σ) (-Complex.I * (moment μ σ 1 : ℂ)) 0 := by
  simpa only [trace_zero_eq, traceN_initial] using hasDerivAt_traceN μ hσ 0 0

private theorem deriv_centerWave (μ : ℝ) {σ : ℝ} (hσ : 0 < σ) :
    deriv (centerWave μ σ) = fun t => -Complex.I * traceN μ σ 1 t := by
  funext t
  rw [← trace_zero_eq]
  exact (hasDerivAt_traceN μ hσ 0 t).deriv

/-- The second normal derivative at the center is the negative second
frequency moment. -/
theorem hasDerivAt_deriv_centerWave_zero (μ : ℝ) {σ : ℝ} (hσ : 0 < σ) :
    HasDerivAt (deriv (centerWave μ σ)) (-(moment μ σ 2 : ℂ)) 0 := by
  rw [deriv_centerWave μ hσ]
  have h := (hasDerivAt_traceN μ hσ 1 0).const_mul (-Complex.I)
  convert h using 1
  rw [traceN_initial]
  simp [← mul_assoc]

/-- The centered second spectral moment is finite and equals the Gaussian
spectral mass times the variance defined by the raw first two moments. -/
theorem centered_square (μ : ℝ) {σ : ℝ} (hσ : 0 < σ) :
    Integrable (fun k => (rate μ k - moment μ σ 1)^2 * weight (σ^2) k) ∧
    (∫ k, (rate μ k - moment μ σ 1)^2 * weight (σ^2) k) =
      variance μ σ * mass (σ^2) := by
  let m := moment μ σ 1
  let a := σ^2
  have ha : 0 < a := sq_pos_of_pos hσ
  have h1 : Integrable (fun k => rate μ k * weight a k) := by
    simpa using GaussianMassShellMoments.integrable_rate_pow_weight ha μ 1
  have h2 := GaussianMassShellMoments.integrable_rate_pow_weight ha μ 2
  have hlin := h1.const_mul (2*m)
  have hconst := (integrable_weight ha).const_mul (m^2)
  have expand (k : Spatial) : (rate μ k - m)^2 * weight a k =
      rate μ k ^ 2 * weight a k - (2*m)*(rate μ k * weight a k) + m^2 * weight a k := by ring
  have hsub : Integrable (fun k => rate μ k^2 * weight a k - 2*m*(rate μ k*weight a k)) := h2.sub hlin
  constructor
  · change Integrable (fun k => (rate μ k - m)^2 * weight a k)
    simp_rw [expand]
    exact hsub.add hconst
  change (∫ k, (rate μ k-m)^2 * weight a k) = _
  simp_rw [expand]
  rw [integral_add hsub hconst, integral_sub h2 hlin, integral_const_mul, integral_const_mul,
    integral_weight ha]
  have hz : mass a ≠ 0 := (mass_pos ha).ne'
  change _ = ((∫ k, rate μ k ^ 2 * weight a k)/mass a - m^2) * mass a
  have he : m * mass a = ∫ k, rate μ k * weight a k := by
    simp [m, moment, a, (mass_pos (sq_pos_of_pos hσ)).ne']
  rw [← he]
  field_simp [hz]
  ring

/-- The actual frequency variance is strictly positive at every positive Gaussian
width. A nonzero centered square occurs on an open spatial frequency set. -/
theorem variance_pos (μ : ℝ) {σ : ℝ} (hσ : 0 < σ) : 0 < variance μ σ := by
  let m := moment μ σ 1
  let a := σ^2
  let f := fun k : Spatial => (rate μ k - m)^2 * weight a k
  have ha : 0 < a := sq_pos_of_pos hσ
  have hi : Integrable f := (centered_square μ hσ).1
  have hc : Continuous f := by unfold f rate weight speedSq spatialDot; fun_prop
  have hn (k : Spatial) : 0 ≤ f k := mul_nonneg (sq_nonneg _) (Real.exp_pos _).le
  let k : Spatial := Pi.single 0 (m+1)
  have hk : m < rate μ k := by
    have hab := GaussianMassShellMoments.abs_component_le_rate μ k 0
    have hcoord : k 0 = m+1 := by simp [k]
    linarith [hcoord ▸ ((le_abs_self (k 0)).trans hab)]
  have hpos := integral_pos_of_integrable_nonneg_nonzero hc hi hn
    (x := k) (mul_pos (sq_pos_of_pos (sub_pos.mpr hk)) (Real.exp_pos _)).ne'
  change 0 < ∫ k, (rate μ k - moment μ σ 1)^2 * weight (σ^2) k at hpos
  rw [(centered_square μ hσ).2] at hpos
  exact (mul_pos_iff_of_pos_right (mass_pos ha)).mp hpos

private theorem normSq_derivative {f : ℝ → ℂ} {v : ℂ} {s : ℝ} (h : HasDerivAt f v s) :
    HasDerivAt (fun t => Complex.normSq (f t)) (2 * (f s).re * v.re + 2 * (f s).im * v.im) s := by
  have hr := Complex.reCLM.hasFDerivAt.comp_hasDerivAt s h
  have hi := Complex.imCLM.hasFDerivAt.comp_hasDerivAt s h
  convert (hr.mul hr).add (hi.mul hi) using 1
  · rfl
  · change _ = v.re * (f s).re + (f s).re * v.re + (v.im * (f s).im + (f s).im * v.im)
    ring

/-- The initial center squared modulus has zero normal derivative. -/
theorem hasDerivAt_centerDensity_zero (μ : ℝ) {σ : ℝ} (hσ : 0 < σ) :
    HasDerivAt (centerDensity μ σ) 0 0 := by
  have h := normSq_derivative (hasDerivAt_centerWave_zero μ hσ)
  change HasDerivAt (fun t => Complex.normSq (centerWave μ σ t)) 0 0
  simpa [centerWave_zero μ hσ, Complex.mul_re, Complex.mul_im] using h

/-- The derivative of the actual center squared modulus has initial slope
−2 times the massive spectral variance. -/
theorem hasDerivAt_deriv_centerDensity_zero (μ : ℝ) {σ : ℝ} (hσ : 0 < σ) :
    HasDerivAt (deriv (centerDensity μ σ)) (-2 * variance μ σ) 0 := by
  let f := centerWave μ σ
  have hf (s : ℝ) : DifferentiableAt ℝ f s := by
    rw [show f = traceN μ σ 0 from (trace_zero_eq _ _).symm]
    exact (hasDerivAt_traceN μ hσ 0 s).differentiableAt
  have hd : deriv (centerDensity μ σ) = fun s =>
      2 * (f s).re * (deriv f s).re + 2 * (f s).im * (deriv f s).im :=
    funext fun s => (normSq_derivative (hf s).hasDerivAt).deriv
  rw [hd]
  have h1 := hasDerivAt_centerWave_zero μ hσ
  have h2 := hasDerivAt_deriv_centerWave_zero μ hσ
  have h1r := Complex.reCLM.hasFDerivAt.comp_hasDerivAt 0 h1
  have h1i := Complex.imCLM.hasFDerivAt.comp_hasDerivAt 0 h1
  have h2r := Complex.reCLM.hasFDerivAt.comp_hasDerivAt 0 h2
  have h2i := Complex.imCLM.hasFDerivAt.comp_hasDerivAt 0 h2
  convert ((h1r.const_mul 2).mul h2r).add ((h1i.const_mul 2).mul h2i) using 1
  · rfl
  · simp [variance, centerWave_zero μ hσ, h1.deriv, Complex.mul_re, Complex.mul_im]
    ring

/-- The spacetime packet has strictly negative initial squared-modulus
curvature in the normal direction at its center. -/
theorem centerDensity_curvature_neg (μ : ℝ) {σ : ℝ} (hσ : 0 < σ) :
    deriv (deriv (centerDensity μ σ)) 0 < 0 := by
  rw [(hasDerivAt_deriv_centerDensity_zero μ hσ).deriv]
  exact mul_neg_of_neg_of_pos (by norm_num) (variance_pos μ hσ)

end FoliationQM.GaussianCenterFrequencyVariance
