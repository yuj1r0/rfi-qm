module

public import FoliationQM.GaussianQuantumMoments
public import FoliationQM.GaussianSobolevWitness

/-!
# Prescribed Gaussian source states and the optimal uncertainty constant

Sources: v13 thm:uncertainty and eq:heisenberg, component kinds C and D.
The concrete Gaussian Lp state and its specified distributional derivative
realize arbitrary position and momentum means and positive position variance.
Their original-state current and quadratic form are genuinely integrable.
These actual normalized Bessel H¹ witnesses also establish optimality of the
universal lower constant on the stated source class.
-/

@[expose] public section
noncomputable section

namespace FoliationQM.GaussianUncertaintyRealization
open MeasureTheory ProbabilityTheory Filter GaussianDistributionalDerivative
open WaveDensityMeasure QuantumCurrentAlgebra WaveMomentumQuadraticForm
open CenteredL2Variance
open scoped NNReal SchwartzMap LineDeriv

/-- The specific Gaussian Lp wave and its actual weak derivative realize the
prescribed means and variance with finite original observables and sharp product. -/
theorem prescribed_gaussian_realization (hbar : ℝ) (hhbar : 0 < hbar) (m p0 : ℝ)
    {v : ℝ≥0} (hv : v ≠ 0) (theta : ℝ) :
    let f := waveLp m hv (p0 / hbar) theta
    let g := derivativeLp m hv (p0 / hbar) theta
    TemperedDistribution.MemSobolev 1 2 (f : 𝓢'(ℝ, ℂ)) ∧
    (∫ x : ℝ, ‖f x‖ ^ 2) = 1 ∧
    MemLp (fun x : ℝ => (x : ℂ) * f x) 2 volume ∧
    ∂_{(1 : ℝ)} (f : 𝓢'(ℝ, ℂ)) = (g : 𝓢'(ℝ, ℂ)) ∧
    densityMeasure f = gaussianReal m v ∧
    IsProbabilityMeasure (densityMeasure f) ∧
    MemLp (fun x : ℝ => x) 2 (densityMeasure f) ∧
    Integrable (fun x => current hbar (f x) (g x)) volume ∧
    Integrable (fun x => ‖centeredPValue hbar (meanMomentum hbar f g) (f x) (g x)‖ ^ 2)
      volume ∧
    mean (densityMeasure f) (fun x : ℝ => x) = m ∧
    variance (densityMeasure f) (fun x : ℝ => x) = (v : ℝ) ∧
    quantumExpectation hbar f g = (p0 : ℂ) ∧
    meanMomentum hbar f g = p0 ∧
    momentumVariance hbar f g = hbar ^ 2 / (4 * (v : ℝ)) ∧
    Real.sqrt (variance (densityMeasure f) (fun x : ℝ => x)) *
      Real.sqrt (momentumVariance hbar f g) = hbar / 2 := by
  dsimp only
  obtain ⟨hf, hn, hx, hD, _, hμ, hp⟩ :=
    GaussianSobolevWitness.source_data m hv (p0 / hbar) theta
  have hF := waveLp_ae_eq m hv (p0 / hbar) theta
  have hG := derivativeLp_ae_eq m hv (p0 / hbar) theta
  have hk : hbar * (p0 / hbar) = p0 := by
    field_simp [hhbar.ne']
  have hE : quantumExpectation hbar (waveLp m hv (p0 / hbar) theta)
      (derivativeLp m hv (p0 / hbar) theta) = (p0 : ℂ) := by
    rw [quantumExpectation_congr_ae hbar hF hG,
      GaussianQuantumMoments.quantumExpectation_wave hbar m hv (p0 / hbar) theta, hk]
  have hP : meanMomentum hbar (waveLp m hv (p0 / hbar) theta)
      (derivativeLp m hv (p0 / hbar) theta) = p0 := by
    exact congrArg Complex.re hE
  refine ⟨hf, hn, hx, hD, hμ, hp, ?_, ?_, ?_, ?_, ?_, hE, hP, ?_, ?_⟩
  · rw [hμ]
    exact GaussianScoreMoments.memLp_position m v
  · exact integrable_current hbar (Lp.memLp _) (Lp.memLp _)
  · exact integrable_centered_norm_sq hbar _ (Lp.memLp _) (Lp.memLp _)
  · rw [hμ]
    exact GaussianScoreMoments.mean_position m v
  · rw [hμ]
    exact GaussianScoreMoments.variance_position m v
  · rw [momentumVariance_congr_ae hbar hF hG]
    exact GaussianQuantumMoments.momentumVariance_wave hbar m hv (p0 / hbar) theta
  · exact GaussianSobolevWitness.sqrt_equality m hv (p0 / hbar) theta hbar hhbar

/-- Every prescribed pair of physical means and positive position variance has
an actual normalized H¹ state with finite observables attaining sharp uncertainty. -/
theorem exists_prescribed_sharp_state (hbar : ℝ) (hhbar : 0 < hbar) (m p0 : ℝ)
    {v : ℝ≥0} (hv : v ≠ 0) :
    ∃ f g : Lp ℂ 2 (volume : Measure ℝ),
    TemperedDistribution.MemSobolev 1 2 (f : 𝓢'(ℝ, ℂ)) ∧
    (∫ x : ℝ, ‖f x‖ ^ 2) = 1 ∧
    MemLp (fun x : ℝ => (x : ℂ) * f x) 2 volume ∧
    ∂_{(1 : ℝ)} (f : 𝓢'(ℝ, ℂ)) = (g : 𝓢'(ℝ, ℂ)) ∧
    densityMeasure f = gaussianReal m v ∧
    IsProbabilityMeasure (densityMeasure f) ∧
    MemLp (fun x : ℝ => x) 2 (densityMeasure f) ∧
    Integrable (fun x => current hbar (f x) (g x)) volume ∧
    Integrable (fun x => ‖centeredPValue hbar (meanMomentum hbar f g) (f x) (g x)‖ ^ 2)
      volume ∧
    mean (densityMeasure f) (fun x : ℝ => x) = m ∧
    variance (densityMeasure f) (fun x : ℝ => x) = (v : ℝ) ∧
    quantumExpectation hbar f g = (p0 : ℂ) ∧
    meanMomentum hbar f g = p0 ∧
    momentumVariance hbar f g = hbar ^ 2 / (4 * (v : ℝ)) ∧
    Real.sqrt (variance (densityMeasure f) (fun x : ℝ => x)) *
      Real.sqrt (momentumVariance hbar f g) = hbar / 2 := by
  exact ⟨waveLp m hv (p0 / hbar) 0, derivativeLp m hv (p0 / hbar) 0,
    prescribed_gaussian_realization hbar hhbar m p0 hv 0⟩

/-- Any lower constant valid for every actual normalized H¹ source state with
finite position moment and its true weak derivative is at most half of hbar. -/
theorem universal_lower_bound_le_half (hbar : ℝ) (hhbar : 0 < hbar) (C : ℝ)
    (hbound : ∀ f g : Lp ℂ 2 (volume : Measure ℝ),
      TemperedDistribution.MemSobolev 1 2 (f : 𝓢'(ℝ, ℂ)) →
      (∫ x : ℝ, ‖f x‖ ^ 2) = 1 →
      MemLp (fun x : ℝ => (x : ℂ) * f x) 2 volume →
      ∂_{(1 : ℝ)} (f : 𝓢'(ℝ, ℂ)) = (g : 𝓢'(ℝ, ℂ)) →
      C ≤ Real.sqrt (variance (densityMeasure f) (fun x : ℝ => x)) *
        Real.sqrt (momentumVariance hbar f g)) :
    C ≤ hbar / 2 := by
  obtain ⟨f, g, hf, hn, hx, hD, _, _, _, _, _, _, _, _, _, _, heq⟩ :=
    exists_prescribed_sharp_state hbar hhbar 0 0 (v := 1) one_ne_zero
  simpa only [heq] using hbound f g hf hn hx hD

end FoliationQM.GaussianUncertaintyRealization
