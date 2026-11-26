module

public import FoliationQM.ReducedPlaneWave

/-!
# Fourier waves on a continuous frequency graph

Source: v13 `cor:schrodinger`, component kinds C and D. Actual graph
moments give smooth physical-time superpositions and genuine coordinate
derivatives. The frequency and amplitude need only be continuous in the
spectral variable; the plane kernel is the existing ReducedPlaneWave mode.
-/

@[expose] public section
noncomputable section

namespace FoliationQM.FrequencyGraphFourier

open MeasureTheory LorentzCoordinates PolarSecondDifferential
open Madelung (coordinateVector)
open OsmoticSliceFields (slicePoint)
open scoped ContDiff FourierTransform Real

/-- The actual temporal and negative spatial frequencies of a continuous graph. -/
def graph (w : Spatial → ℝ) (k : Spatial) : Covector := assemble (w k) (-k)

/-- The physical-time superposition of the existing angular plane modes. -/
def wave (w : Spatial → ℝ) (A : Spatial → ℂ) (x : Covector) : ℂ :=
  ∫ k, ReducedPlaneWave.mode (w k) k x * A k

/-- Genuine integrability of every graph-norm moment of the spectral amplitude. -/
def HasMoments (w : Spatial → ℝ) (A : Spatial → ℂ) : Prop :=
  ∀ n : ℕ, Integrable (fun k => ‖graph w k‖ ^ n * ‖A k‖)

/-- The spectral amplitude obtained by differentiating in one spacetime coordinate. -/
def differentiated (w : Spatial → ℝ) (i : Fin 4) (A : Spatial → ℂ) (k : Spatial) : ℂ :=
  -Complex.I * (graph w k i : ℂ) * A k

/-- A continuous temporal frequency gives a continuous actual spacetime frequency graph. -/
theorem continuous_graph {w : Spatial → ℝ} (hw : Continuous w) : Continuous (graph w) := by
  apply continuous_pi
  intro i
  fin_cases i <;> simp [graph, assemble] <;> fun_prop

private def frequencyPart (v : Covector) : Spatial := fun i => -v i.succ

private theorem recovered (w : Spatial → ℝ) (k : Spatial) : frequencyPart (graph w k) = k := by
  ext i
  fin_cases i <;> simp [frequencyPart, graph, assemble]

private def angularPair : Covector →L[ℝ] Covector →L[ℝ] ℝ :=
  (2 * Real.pi)⁻¹ • ∑ i : Fin 4,
    (ContinuousLinearMap.proj i : Covector →L[ℝ] ℝ).smulRight
      (ContinuousLinearMap.proj i : Covector →L[ℝ] ℝ)

private theorem pair_apply (v x : Covector) :
    angularPair v x = (2 * Real.pi)⁻¹ * ∑ i : Fin 4, v i * x i := by
  simp [angularPair, Fin.sum_univ_four, mul_add]

private theorem pair_axis (v : Covector) (i : Fin 4) :
    angularPair v (coordinateVector i) = (2 * Real.pi)⁻¹ * v i := by
  rw [pair_apply]
  simp [coordinateVector, Pi.single_apply, mul_ite]

private def graphMeasure (w : Spatial → ℝ) : Measure Covector := Measure.map (graph w) volume

private def transform (w : Spatial → ℝ) (f : Covector → ℂ) :=
  VectorFourier.fourierIntegral Real.fourierChar (graphMeasure w) angularPair.toLinearMap₁₂ f

private theorem character_graph (w : Spatial → ℝ) (k : Spatial) (x : Covector) :
    Complex.exp (((-2 * Real.pi * angularPair (graph w k) x : ℝ) : ℂ) * Complex.I) =
      ReducedPlaneWave.mode (w k) k x := by
  rw [pair_apply]
  unfold ReducedPlaneWave.mode
  congr 1
  rw [mul_comm Complex.I]
  congr 1
  push_cast
  simp [Fin.sum_univ_four, graph, assemble, spatialDot, Fin.succ]
  field_simp [Real.pi_ne_zero]
  ring

private theorem transform_apply {w : Spatial → ℝ} {f : Covector → ℂ}
    (hw : Continuous w) (hf : Continuous f) (x : Covector) :
    transform w f x = ∫ k, ReducedPlaneWave.mode (w k) k x * f (graph w k) := by
  rw [transform, Real.vector_fourierIntegral_eq_integral_exp_smul, graphMeasure,
    integral_map (continuous_graph hw).aemeasurable (by
      apply Continuous.aestronglyMeasurable
      change Continuous (fun v =>
        Complex.exp ((↑(-2 * Real.pi * (angularPair v x)) : ℂ) * Complex.I) * f v)
      fun_prop)]
  apply integral_congr_ae
  filter_upwards with k
  exact congrArg (fun z => z * f (graph w k)) (character_graph w k x)

private theorem lift_continuous {A : Spatial → ℂ} (hA : Continuous A) :
    Continuous (A ∘ frequencyPart) :=
  hA.comp (continuous_pi fun i => (continuous_apply i.succ).neg)

private theorem wave_transform {w : Spatial → ℝ} {A : Spatial → ℂ}
    (hw : Continuous w) (hA : Continuous A) :
    wave w A = transform w (A ∘ frequencyPart) := by
  funext x
  rw [transform_apply hw (lift_continuous hA)]
  simp only [Function.comp_apply, recovered, wave]

private theorem graph_moment {w : Spatial → ℝ} {A : Spatial → ℂ}
    (hw : Continuous w) (hA : Continuous A) (hm : HasMoments w A) (n : ℕ) :
    Integrable (fun v => ‖v‖ ^ n * ‖(A ∘ frequencyPart) v‖) (graphMeasure w) := by
  refine (integrable_map_measure (Continuous.aestronglyMeasurable (by
    exact (continuous_norm.pow n).mul (lift_continuous hA).norm))
    (continuous_graph hw).aemeasurable).mpr ?_
  change Integrable (fun k => ‖graph w k‖ ^ n * ‖A (frequencyPart (graph w k))‖)
  simpa only [recovered] using hm n

/-- All genuine graph moments make the physical-time Fourier wave jointly smooth. -/
theorem smooth_wave {w : Spatial → ℝ} {A : Spatial → ℂ}
    (hw : Continuous w) (hA : Continuous A) (hm : HasMoments w A) :
    ContDiff ℝ ∞ (wave w A) := by
  rw [wave_transform hw hA]
  exact VectorFourier.contDiff_fourierIntegral angularPair (fun n _ => graph_moment hw hA hm n)

private theorem differentiated_continuous {w : Spatial → ℝ} {A : Spatial → ℂ}
    (hw : Continuous w) (hA : Continuous A) (i : Fin 4) :
    Continuous (differentiated w i A) := by
  have h := (continuous_apply i).comp (continuous_graph hw)
  unfold differentiated
  fun_prop

/-- Coordinate differentiation preserves continuity and every genuine graph moment of the amplitude. -/
theorem differentiated_data {w : Spatial → ℝ} {A : Spatial → ℂ}
    (hw : Continuous w) (hA : Continuous A) (hm : HasMoments w A) (i : Fin 4) :
    Continuous (differentiated w i A) ∧ HasMoments w (differentiated w i A) := by
  refine ⟨differentiated_continuous hw hA i, ?_⟩
  intro n
  apply (hm (n + 1)).mono' ((continuous_norm.comp (continuous_graph hw)).pow n |>.mul
    (differentiated_continuous hw hA i).norm).aestronglyMeasurable
  refine ae_of_all _ fun k => ?_
  change ‖‖graph w k‖ ^ n * ‖differentiated w i A k‖‖ ≤ ‖graph w k‖ ^ (n + 1) * ‖A k‖
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (pow_nonneg (norm_nonneg _) _) (norm_nonneg _))]
  simp only [differentiated, norm_mul, norm_neg,
    Complex.norm_I, one_mul, Complex.norm_real, pow_succ]
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right (norm_le_pi_norm (graph w k) i) (norm_nonneg (A k)))
    (pow_nonneg (norm_nonneg (graph w k)) n)

/-- The actual complex mode-amplitude product is integrable at every physical spacetime point. -/
theorem integrable_mode {w : Spatial → ℝ} {A : Spatial → ℂ}
    (hw : Continuous w) (hA : Continuous A) (hm : HasMoments w A) (x : Covector) :
    Integrable (fun k => ReducedPlaneWave.mode (w k) k x * A k) := by
  have hz : Integrable (fun k => ‖A k‖) := by simpa using hm 0
  apply hz.mono' (by unfold ReducedPlaneWave.mode spatialDot; fun_prop)
  refine ae_of_all _ fun k => ?_
  simp only [norm_mul, ReducedPlaneWave.norm_mode, one_mul, le_refl]

/-- The true coordinate derivative is the same Fourier wave with its differentiated amplitude. -/
theorem first_coordinate {w : Spatial → ℝ} {A : Spatial → ℂ}
    (hw : Continuous w) (hA : Continuous A) (hm : HasMoments w A) (i : Fin 4) (x : Covector) :
    directionalDerivative (wave w A) (coordinateVector i) x = wave w (differentiated w i A) x := by
  let f := A ∘ frequencyPart
  have hf : Continuous f := lift_continuous hA
  have h₀ : Integrable f (graphMeasure w) := by
    apply (integrable_norm_iff hf.aestronglyMeasurable).mp
    simpa only [pow_zero, one_mul] using graph_moment hw hA hm 0
  have h₁ : Integrable (fun v => ‖v‖ * ‖f v‖) (graphMeasure w) := by
    simpa only [pow_one] using graph_moment hw hA hm 1
  have hL : Integrable (VectorFourier.fourierSMulRight angularPair f) (graphMeasure w) := by
    apply (h₁.const_mul (2 * Real.pi * ‖angularPair‖)).mono' hf.aestronglyMeasurable.fourierSMulRight
    refine ae_of_all _ fun v => ?_
    simpa only [mul_assoc] using VectorFourier.norm_fourierSMulRight_le angularPair f v
  have hscale (v : Covector) : VectorFourier.fourierSMulRight angularPair f v (coordinateVector i) =
      -Complex.I * (v i : ℂ) * f v := by
    rw [VectorFourier.fourierSMulRight_apply, pair_axis]
    simp only [smul_eq_mul, Complex.real_smul, Complex.ofReal_mul,
      Complex.ofReal_inv, Complex.ofReal_ofNat]
    field_simp [Real.pi_ne_zero]
  rw [wave_transform hw hA]
  unfold directionalDerivative transform
  rw [VectorFourier.fderiv_fourierIntegral angularPair h₀ h₁,
    Real.fourierIntegral_continuousLinearMap_apply' (L := angularPair) hL]
  change transform w (fun v =>
    VectorFourier.fourierSMulRight angularPair f v (coordinateVector i)) x = _
  simp_rw [hscale]
  rw [transform_apply hw (by fun_prop)]
  simp only [wave, differentiated, f, Function.comp_apply, recovered]

/-- Differentiating the actual first-derivative function gives the recursively certified second derivative. -/
theorem second_coordinate {w : Spatial → ℝ} {A : Spatial → ℂ}
    (hw : Continuous w) (hA : Continuous A) (hm : HasMoments w A) (i : Fin 4) (x : Covector) :
    secondDirectionalDerivative (wave w A) (coordinateVector i) x =
      wave w (differentiated w i (differentiated w i A)) x := by
  unfold secondDirectionalDerivative
  rw [funext (first_coordinate hw hA hm i)]
  have hd := differentiated_data hw hA hm i
  exact first_coordinate hw hd.1 hd.2 i x

/-- At time zero the same wave is the positive spatial angular transform, independently of its frequency graph. -/
theorem initial_value (w : Spatial → ℝ) (A : Spatial → ℂ) (y : Spatial) :
    wave w A (slicePoint 0 y) = ∫ k, GaussianSpatialFourier.character y k * A k := by
  simp [wave, ReducedPlaneWave.mode, GaussianSpatialFourier.character, spatialDot, slicePoint, assemble]

end FoliationQM.FrequencyGraphFourier
