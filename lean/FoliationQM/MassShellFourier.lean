module

public import FoliationQM.GaussianKGMode
public import FoliationQM.GaussianSpatialFourier
public import Mathlib.Analysis.Fourier.FourierTransformDeriv

/-!
# Positive-frequency spacetime Fourier superposition

For the free Gaussian clause of v13 `thm:adm_positivity` and
`eq:dilatation_coercivity_bound`, an angular spatial spectrum determines
a spacetime wave after selecting the positive mass shell. The observer
coordinate is x⁰=ct. All-order spectral moments justify differentiation
of the integral and give the free massive equation at every point.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.MassShellFourier
open MeasureTheory LorentzCoordinates GaussianKGMode OsmoticSliceFields PolarSecondDifferential
open scoped ContDiff FourierTransform Real

/-- Normal and negative spatial wave numbers of the positive-frequency branch. -/
def shell (μ : ℝ) (k : Spatial) : Covector := assemble (rate μ k) (-k)

/-- Angular plane wave exp(i(k·x−Ωx⁰)) on the positive mass shell. -/
def mode (μ : ℝ) (k : Spatial) (x : Covector) : ℂ :=
  Complex.exp (Complex.I * (spatialDot k (fun i => x i.succ) - rate μ k * x 0 : ℝ))

/-- Spacetime wave with continuous angular spectrum A. -/
def wave (μ : ℝ) (A : Spatial → ℂ) (x : Covector) : ℂ := ∫ k, mode μ k x * A k

/-- Finite moments of the amplitude with the true spacetime Fourier frequency on shell. -/
def HasMoments (μ : ℝ) (A : Spatial → ℂ) : Prop :=
  ∀ n : ℕ, Integrable (fun k => ‖shell μ k‖^n * ‖A k‖)

private theorem shell_continuous (μ : ℝ) : Continuous (shell μ) := by
  apply continuous_pi
  intro i
  fin_cases i <;> simp [shell, assemble, rate, speedSq, spatialDot] <;> fun_prop

private def frequencyPart (v : Covector) : Spatial := fun i => -v i.succ

private theorem recovered (μ : ℝ) (k : Spatial) : frequencyPart (shell μ k) = k := by
  ext i
  fin_cases i <;> simp [frequencyPart, shell, assemble]

private def angularPair : Covector →L[ℝ] Covector →L[ℝ] ℝ :=
  (2 * Real.pi)⁻¹ • ∑ i : Fin 4,
    (ContinuousLinearMap.proj i : Covector →L[ℝ] ℝ).smulRight
      (ContinuousLinearMap.proj i : Covector →L[ℝ] ℝ)

private theorem pair_apply (v x : Covector) :
    angularPair v x = (2 * Real.pi)⁻¹ * ∑ i : Fin 4, v i * x i := by
  simp [angularPair, Fin.sum_univ_four, mul_add]

private theorem pair_axis (v : Covector) (i : Fin 4) :
    angularPair v (Madelung.coordinateVector i) = (2*Real.pi)⁻¹ * v i := by
  rw [pair_apply]
  simp [Madelung.coordinateVector, Pi.single_apply, mul_ite]

private def shellMeasure (μ : ℝ) : Measure Covector := Measure.map (shell μ) volume

private def transform (μ : ℝ) (f : Covector → ℂ) :=
  VectorFourier.fourierIntegral Real.fourierChar (shellMeasure μ) angularPair.toLinearMap₁₂ f

private theorem character_shell (μ : ℝ) (k : Spatial) (x : Covector) :
    Complex.exp (((-2 * Real.pi * angularPair (shell μ k) x : ℝ) : ℂ) * Complex.I) = mode μ k x := by
  rw [pair_apply]
  unfold mode
  congr 1
  rw [mul_comm Complex.I]
  congr 1
  push_cast
  simp [Fin.sum_univ_four, shell, assemble, spatialDot, Fin.succ]
  field_simp [Real.pi_ne_zero]
  ring

private theorem transform_apply {f : Covector → ℂ} (hf : Continuous f) (μ : ℝ) (x : Covector) :
    transform μ f x = ∫ k, mode μ k x * f (shell μ k) := by
  rw [transform, Real.vector_fourierIntegral_eq_integral_exp_smul, shellMeasure,
    integral_map (shell_continuous μ).aemeasurable (by
      apply Continuous.aestronglyMeasurable
      change Continuous (fun v => Complex.exp ((↑(-2*Real.pi*(angularPair v x)) : ℂ)*Complex.I) * f v)
      fun_prop)]
  apply integral_congr_ae
  filter_upwards with k
  exact congrArg (fun z => z * f (shell μ k)) (character_shell μ k x)

private theorem lift_continuous {A : Spatial → ℂ} (hA : Continuous A) : Continuous (A ∘ frequencyPart) :=
  hA.comp (continuous_pi fun i => (continuous_apply i.succ).neg)

private theorem wave_transform {A : Spatial → ℂ} (μ : ℝ) (hA : Continuous A) :
    wave μ A = transform μ (A ∘ frequencyPart) := by
  funext x
  rw [transform_apply (lift_continuous hA)]
  simp only [Function.comp_apply, recovered, wave]

private theorem shell_moment {A : Spatial → ℂ} {μ : ℝ} (hA : Continuous A)
    (hm : HasMoments μ A) (n : ℕ) :
    Integrable (fun v => ‖v‖^n * ‖(A ∘ frequencyPart) v‖) (shellMeasure μ) := by
  refine (integrable_map_measure (Continuous.aestronglyMeasurable (by
    exact (continuous_norm.pow n).mul (lift_continuous hA).norm)) (shell_continuous μ).aemeasurable).mpr ?_
  change Integrable (fun k => ‖shell μ k‖^n * ‖A (frequencyPart (shell μ k))‖)
  simpa only [recovered] using hm n

/-- The spacetime Fourier wave is jointly smooth to every order. -/
theorem smooth_wave (μ : ℝ) {A : Spatial → ℂ} (hA : Continuous A) (hm : HasMoments μ A) :
    ContDiff ℝ ∞ (wave μ A) := by
  rw [wave_transform μ hA]
  exact VectorFourier.contDiff_fourierIntegral angularPair (fun n _ => shell_moment hA hm n)

/-- The true initial wave is the positive spatial angular transform of its spectrum. -/
theorem initial_value (μ : ℝ) (A : Spatial → ℂ) (y : Spatial) :
    wave μ A (slicePoint 0 y) = ∫ k, GaussianSpatialFourier.character y k * A k := by
  simp [wave, mode, GaussianSpatialFourier.character, spatialDot, slicePoint, assemble]

/-- The coordinate multiplier for differentiating an angular wave on the mass shell. -/
def differentiated (μ : ℝ) (i : Fin 4) (A : Spatial → ℂ) (k : Spatial) : ℂ :=
  -Complex.I * (shell μ k i : ℂ) * A k

private theorem differentiated_continuous {A : Spatial → ℂ} (hA : Continuous A) (μ : ℝ) (i : Fin 4) :
    Continuous (differentiated μ i A) := by
  have h := (continuous_apply i).comp (shell_continuous μ)
  unfold differentiated
  fun_prop

private theorem differentiated_moments {A : Spatial → ℂ} {μ : ℝ} (hA : Continuous A)
    (hm : HasMoments μ A) (i : Fin 4) : HasMoments μ (differentiated μ i A) := by
  intro n
  apply (hm (n+1)).mono' ((continuous_norm.comp (shell_continuous μ)).pow n |>.mul
    (differentiated_continuous hA μ i).norm).aestronglyMeasurable
  refine ae_of_all _ fun k => ?_
  change ‖‖shell μ k‖^n * ‖differentiated μ i A k‖‖ ≤ ‖shell μ k‖^(n+1) * ‖A k‖
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (pow_nonneg (norm_nonneg _) _) (norm_nonneg _))]
  simp only [differentiated, norm_mul, norm_neg,
    Complex.norm_I, one_mul, Complex.norm_real, pow_succ]
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right (norm_le_pi_norm (shell μ k) i) (norm_nonneg (A k)))
    (pow_nonneg (norm_nonneg (shell μ k)) n)

/-- Actual coordinate derivative of the wave as a Fourier transform with the differentiated amplitude. -/
theorem first_coordinate (μ : ℝ) {A : Spatial → ℂ} (hA : Continuous A) (hm : HasMoments μ A)
    (i : Fin 4) (x : Covector) :
    directionalDerivative (wave μ A) (Madelung.coordinateVector i) x = wave μ (differentiated μ i A) x := by
  let f := A ∘ frequencyPart
  have hf : Continuous f := lift_continuous hA
  have h₀ : Integrable f (shellMeasure μ) := by
    apply (integrable_norm_iff hf.aestronglyMeasurable).mp
    simpa only [pow_zero, one_mul] using shell_moment hA hm 0
  have h₁ : Integrable (fun v => ‖v‖ * ‖f v‖) (shellMeasure μ) := by
    simpa only [pow_one] using shell_moment hA hm 1
  have hL : Integrable (VectorFourier.fourierSMulRight angularPair f) (shellMeasure μ) := by
    apply (h₁.const_mul (2*Real.pi*‖angularPair‖)).mono' hf.aestronglyMeasurable.fourierSMulRight
    refine ae_of_all _ fun v => ?_
    simpa only [mul_assoc] using VectorFourier.norm_fourierSMulRight_le angularPair f v
  have hscale (v : Covector) : VectorFourier.fourierSMulRight angularPair f v (Madelung.coordinateVector i) =
      -Complex.I * (v i : ℂ) * f v := by
    rw [VectorFourier.fourierSMulRight_apply, pair_axis]
    simp only [smul_eq_mul, Complex.real_smul, Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_ofNat]
    field_simp [Real.pi_ne_zero]

  rw [wave_transform μ hA]
  unfold directionalDerivative transform
  rw [VectorFourier.fderiv_fourierIntegral angularPair h₀ h₁,
    Real.fourierIntegral_continuousLinearMap_apply' (L := angularPair) hL]
  change transform μ (fun v => VectorFourier.fourierSMulRight angularPair f v (Madelung.coordinateVector i)) x = _
  simp_rw [hscale]
  rw [transform_apply (by fun_prop)]
  simp only [wave, differentiated, f, Function.comp_apply, recovered]

/-- The normal Cauchy datum for the positive branch carries the negative imaginary frequency multiplier. -/
theorem initial_normal (μ : ℝ) {A : Spatial → ℂ} (hA : Continuous A) (hm : HasMoments μ A) (y : Spatial) :
    directionalDerivative (wave μ A) (Madelung.coordinateVector 0) (slicePoint 0 y) =
      -Complex.I * ∫ k, GaussianSpatialFourier.character y k * (rate μ k : ℂ) * A k := by
  rw [first_coordinate μ hA hm, initial_value, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with k
  simp [differentiated, shell, assemble]
  ring

private theorem mode_integrable {A : Spatial → ℂ} {μ : ℝ} (hA : Continuous A)
    (hm : HasMoments μ A) (x : Covector) : Integrable (fun k => mode μ k x * A k) := by
  have hz : Integrable (fun k => ‖A k‖) := by simpa using hm 0
  apply hz.mono' (by unfold mode rate speedSq spatialDot; fun_prop)
  refine ae_of_all _ fun k => ?_
  simp only [mode, norm_mul, mul_comm Complex.I, Complex.norm_exp_ofReal_mul_I, one_mul, le_refl]

/-- The actual flat wave operator of the spacetime superposition satisfies the massive KG
equation everywhere for the dispersion Ω²=μ²+|k|². -/
theorem klein_gordon (μ : ℝ) {A : Spatial → ℂ} (hA : Continuous A) (hm : HasMoments μ A) (x : Covector) :
    box (wave μ A) Madelung.coordinateVector x + ((μ^2 : ℝ):ℂ) * wave μ A x = 0 := by
  let second := fun i => differentiated μ i (differentiated μ i A)
  have jet (i : Fin 4) : secondDirectionalDerivative (wave μ A) (Madelung.coordinateVector i) x =
      wave μ (second i) x := by
    unfold secondDirectionalDerivative
    rw [funext (first_coordinate μ hA hm i)]
    exact first_coordinate μ (differentiated_continuous hA μ i) (differentiated_moments hA hm i) i x
  have hi (i : Fin 4) : Integrable (fun k => mode μ k x * second i k) :=
    mode_integrable (differentiated_continuous (differentiated_continuous hA μ i) μ i)
      (differentiated_moments (differentiated_continuous hA μ i) (differentiated_moments hA hm i) i) x
  let g := fun i k => mode μ k x * second i k
  have h01 : Integrable (fun k => g 0 k - g 1 k) := (hi 0).sub (hi 1)
  have h012 : Integrable (fun k => g 0 k - g 1 k - g 2 k) := h01.sub (hi 2)
  have h0123 : Integrable (fun k => g 0 k - g 1 k - g 2 k - g 3 k) := h012.sub (hi 3)
  have hc : Integrable (fun k => ((μ^2 : ℝ) : ℂ) * (mode μ k x * A k)) :=
    (mode_integrable hA hm x).const_mul _
  simp only [box, jet, wave]
  rw [← integral_sub (hi 0) (hi 1), ← integral_sub h01 (hi 2), ← integral_sub h012 (hi 3),
    ← integral_const_mul, ← integral_add h0123 hc]
  apply integral_eq_zero_of_ae
  refine ae_of_all _ fun k => ?_
  have he : (rate μ k : ℂ)^2 = (μ:ℂ)^2 + (k 0:ℂ)^2 + (k 1:ℂ)^2 + (k 2:ℂ)^2 := by
    exact_mod_cast (show (rate μ k)^2 = μ^2 + (k 0)^2 + (k 1)^2 + (k 2)^2 by
      rw [rate_sq, speedSq_eq_sum]; ring)
  have hs (i : Fin 4) : second i k = -((shell μ k i : ℂ)^2) * A k := by
    calc
      _ = Complex.I^2 * (shell μ k i : ℂ)^2 * A k := by unfold second differentiated; ring
      _ = _ := by rw [Complex.I_sq]; ring
  have e₀ : shell μ k 0 = rate μ k := rfl
  have e₁ : shell μ k 1 = -k 0 := rfl
  have e₂ : shell μ k 2 = -k 1 := rfl
  have e₃ : shell μ k 3 = -k 2 := rfl
  simp only [g, hs, e₀, e₁, e₂, e₃, Complex.ofReal_neg, Complex.ofReal_pow, Pi.zero_apply]
  linear_combination (norm := ring_nf) -(mode μ k x * A k) * he

end FoliationQM.MassShellFourier
