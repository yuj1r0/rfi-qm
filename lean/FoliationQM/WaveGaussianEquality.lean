module

public import FoliationQM.GaussianWaveRigidity
public import FoliationQM.GaussianDensitySaturation
public import FoliationQM.WaveHeisenberg
public import FoliationQM.SobolevPhaseVariance

/-!
# Actual Gaussian equality classification on one wave representative

Sources: v13 thm:uncertainty and eq:heisenberg, component kinds C and D.
The derived whole-line equality equation is solved using the actual Gaussian
reference wave. Its parameters are the genuine position mean, positive position
variance and momentum mean. The converse uses literal Gaussian density and
constant actual local phase gradient. Every compatible supplied phase has the
same two-way criterion on this same wave and derivative. Original Lp states
are handled separately by genuine almost-everywhere transport.
-/

@[expose] public section
noncomputable section

namespace FoliationQM.WaveGaussianEquality
open MeasureTheory Filter WaveScoreAlgebra WaveDensityMeasure
open WaveMomentumQuadraticForm CenteredL2Variance SobolevPhaseVariance
open scoped NNReal

variable {u g : ℝ → ℂ}

/-- Equality gives the actual Gaussian plane-phase wave at its genuine means
and variance, pointwise for the continuous AC representative. -/
theorem eq_wave_of_equality (hc : Continuous u)
    (hAC : ∀ a b, AbsolutelyContinuousOnInterval u a b)
    (hd : ∀ᵐ x ∂volume, HasDerivAt u (g x) x)
    (hu : MemLp u 2 volume) (hg : MemLp g 2 volume)
    (hxu : MemLp (fun x : ℝ => (x : ℂ) * u x) 2 volume)
    (hnorm : (∫ x, density (u x)) = 1) (hbar : ℝ) (hhbar : 0 < hbar)
    (heq : Real.sqrt (variance (densityMeasure u) (fun x : ℝ => x)) *
      Real.sqrt (momentumVariance hbar u g) = hbar / 2) :
    ∃ theta : ℝ, ∀ x, u x = GaussianPlanePhaseWave.wave
      (mean (densityMeasure u) (fun y : ℝ => y))
      ⟨variance (densityMeasure u) (fun y : ℝ => y),
        variance_nonneg (densityMeasure u) (fun y : ℝ => y)⟩
      (meanMomentum hbar u g / hbar) theta x := by
  let s : ℝ≥0 := ⟨variance (densityMeasure u) (fun y : ℝ => y),
    variance_nonneg (densityMeasure u) (fun y : ℝ => y)⟩
  have hs : s ≠ 0 := by
    intro hz
    exact (WaveHeisenberg.variance_pos hc hAC hd hu hg hxu hnorm).ne'
      (congrArg (fun r : ℝ≥0 => (r : ℝ)) hz)
  have hode := WaveHeisenberg.equality_ode hc hAC hd hu hg hxu hnorm hbar hhbar heq
  exact GaussianWaveRigidity.eq_wave_of_ae_ode hAC hd
    (mean (densityMeasure u) (fun y : ℝ => y)) hs
    (meanMomentum hbar u g / hbar) hode hnorm

/-- Equality is equivalent to literal Gaussian density and constant genuine
local phase gradient for the same wave, with nonzero Gaussian variance. -/
theorem equality_iff_gaussian_local_phase (hc : Continuous u)
    (hAC : ∀ a b, AbsolutelyContinuousOnInterval u a b)
    (hd : ∀ᵐ x ∂volume, HasDerivAt u (g x) x)
    (hu : MemLp u 2 volume) (hg : MemLp g 2 volume)
    (hxu : MemLp (fun x : ℝ => (x : ℂ) * u x) 2 volume)
    (hnorm : (∫ x, density (u x)) = 1) (hbar : ℝ) (hhbar : 0 < hbar) :
    Real.sqrt (variance (densityMeasure u) (fun x : ℝ => x)) *
        Real.sqrt (momentumVariance hbar u g) = hbar / 2 ↔
      ∃ (m : ℝ) (s : ℝ≥0), s ≠ 0 ∧ ∃ p0 : ℝ,
        ((fun x => density (u x)) =ᵐ[volume] ProbabilityTheory.gaussianPDFReal m s) ∧
        (∀ᵐ x ∂densityMeasure u, localPhaseGradient hbar u x = p0) := by
  constructor
  · intro heq
    obtain ⟨theta, hw⟩ := eq_wave_of_equality hc hAC hd hu hg hxu hnorm hbar hhbar heq
    let s : ℝ≥0 := ⟨variance (densityMeasure u) (fun y : ℝ => y),
      variance_nonneg (densityMeasure u) (fun y : ℝ => y)⟩
    have hs : s ≠ 0 := by
      intro hz
      exact (WaveHeisenberg.variance_pos hc hAC hd hu hg hxu hnorm).ne'
        (congrArg (fun r : ℝ≥0 => (r : ℝ)) hz)
    refine ⟨mean (densityMeasure u) (fun y : ℝ => y), s, hs,
      meanMomentum hbar u g, ?_, ?_⟩
    · exact Eventually.of_forall fun x => by
        change density (u x) = ProbabilityTheory.gaussianPDFReal
          (mean (densityMeasure u) (fun y : ℝ => y)) s x
        rw [hw x]
        exact GaussianPlanePhaseWave.norm_sq _ hs _ theta x
    · have hb := ((WaveHeisenberg.equality_iff hc hAC hd hu hg hxu hnorm
        hbar hhbar).mp heq).1
      exact (ae_localPhaseGradient_eq_bulk hc hd hbar).trans hb
  · rintro ⟨m, s, hs, p0, hGaussian, hphase⟩
    exact GaussianDensitySaturation.sqrt_equality_of_local_phase
      hc hAC hd hu hg hxu hnorm hbar hhbar m hs hGaussian p0 hphase

/-- For each genuinely compatible supplied phase, the same state saturates
exactly when its density is Gaussian and that phase derivative is constant AE. -/
theorem equality_iff_gaussian_supplied_phase (hc : Continuous u)
    (hAC : ∀ a b, AbsolutelyContinuousOnInterval u a b)
    (hd : ∀ᵐ x ∂volume, HasDerivAt u (g x) x)
    (hu : MemLp u 2 volume) (hg : MemLp g 2 volume)
    (hxu : MemLp (fun x : ℝ => (x : ℂ) * u x) 2 volume)
    (hnorm : (∫ x, density (u x)) = 1) (hbar : ℝ) (hhbar : 0 < hbar)
    (S : ℝ → ℝ)
    (hS : ∀ᵐ x ∂volume, 0 < density (u x) → DifferentiableAt ℝ S x)
    (hpolar : ∀ x, 0 < density (u x) → u x =
      (Real.sqrt (density (u x)) : ℂ) * Complex.exp (Complex.I * ((S x / hbar : ℝ) : ℂ))) :
    Real.sqrt (variance (densityMeasure u) (fun x : ℝ => x)) *
        Real.sqrt (momentumVariance hbar u g) = hbar / 2 ↔
      ∃ (m : ℝ) (s : ℝ≥0), s ≠ 0 ∧ ∃ p0 : ℝ,
        ((fun x => density (u x)) =ᵐ[volume] ProbabilityTheory.gaussianPDFReal m s) ∧
        (∀ᵐ x ∂densityMeasure u, deriv S x = p0) := by
  constructor
  · intro heq
    obtain ⟨m, s, hs, p0, hGaussian, hphase⟩ :=
      (equality_iff_gaussian_local_phase hc hAC hd hu hg hxu hnorm hbar hhbar).mp heq
    exact ⟨m, s, hs, p0, hGaussian,
      (ae_supplied_deriv_eq_localPhaseGradient hc hd hS hhbar.ne' hpolar).trans hphase⟩
  · rintro ⟨m, s, hs, p0, hGaussian, hphase⟩
    exact GaussianDensitySaturation.sqrt_equality_of_supplied_phase
      hc hAC hd hu hg hxu hnorm hbar hhbar m hs hGaussian S hS hpolar p0 hphase

end FoliationQM.WaveGaussianEquality
