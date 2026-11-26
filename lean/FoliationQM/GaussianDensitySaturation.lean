module

public import FoliationQM.WaveHeisenberg
public import FoliationQM.SobolevPhaseVariance
public import FoliationQM.GaussianScoreMoments

/-!
# Gaussian density and constant phase gradient imply sharp uncertainty

Sources: v13 thm:uncertainty and eq:heisenberg, component kinds C and D.
The density is the actual norm square of the same continuous locally AC wave
whose genuine derivative supplies its finite quantum quadratic form. Equality
with a positive-variance Gaussian density is upgraded from Lebesgue AE to
pointwise equality before taking the logarithmic derivative. The actual local
phase gradient, or any genuinely compatible supplied phase derivative, being
constant then gives both proved equality conditions of the Heisenberg bound.
No Gaussian wave form or saturation is assumed, and no new H1 representative
is selected. Original Sobolev-state packaging remains a separate application.
-/

@[expose] public section
noncomputable section

namespace FoliationQM.GaussianDensitySaturation
open MeasureTheory ProbabilityTheory Filter WaveScoreAlgebra WaveDensityMeasure
open WaveMomentumQuadraticForm CenteredL2Variance SobolevCramerRao SobolevPhaseVariance
open scoped NNReal

variable {u g : ℝ → ℂ}

/-- Gaussian density and a constant actual local phase gradient imply the
literal sharp square-root uncertainty equality for the same wave and derivative. -/
theorem sqrt_equality_of_local_phase (hc : Continuous u)
    (hAC : ∀ a b, AbsolutelyContinuousOnInterval u a b)
    (hd : ∀ᵐ x ∂volume, HasDerivAt u (g x) x)
    (hu : MemLp u 2 volume) (hg : MemLp g 2 volume)
    (hxu : MemLp (fun x : ℝ => (x : ℂ) * u x) 2 volume)
    (hnorm : (∫ x, density (u x)) = 1) (hbar : ℝ) (hhbar : 0 < hbar)
    (m : ℝ) {sigma2 : ℝ≥0} (hvar : sigma2 ≠ 0)
    (hGaussian : (fun x => density (u x)) =ᵐ[volume] gaussianPDFReal m sigma2)
    (p0 : ℝ) (hphase : ∀ᵐ x ∂densityMeasure u, localPhaseGradient hbar u x = p0) :
    Real.sqrt (variance (densityMeasure u) (fun x : ℝ => x)) *
      Real.sqrt (momentumVariance hbar u g) = hbar / 2 := by
  have hρ : (fun x => density (u x)) = gaussianPDFReal m sigma2 :=
    Measure.eq_of_ae_eq hGaussian (hc.norm.pow 2)
      (GaussianDensityScore.contDiff_density m sigma2).continuous
  have hμ : densityMeasure u = gaussianReal m sigma2 := by
    rw [densityMeasure, gaussianReal_of_var_ne_zero m hvar, gaussianPDF_def]
    apply congrArg (Measure.withDensity volume)
    funext x
    exact congrArg ENNReal.ofReal (congrFun hρ x)
  have hmean : mean (densityMeasure u) (fun x : ℝ => x) = m := by
    rw [hμ, GaussianScoreMoments.mean_position]
  have hvariance : variance (densityMeasure u) (fun x : ℝ => x) = (sigma2 : ℝ) := by
    rw [hμ, GaussianScoreMoments.variance_position]
  have hlog (x : ℝ) : logDensityDerivative u x = -(x - m) / (sigma2 : ℝ) := by
    simp only [logDensityDerivative]
    simp_rw [congrFun hρ]
    exact GaussianDensityScore.deriv_log_density m hvar x
  have hbulk : ∀ᵐ x ∂densityMeasure u, bulk hbar (u x) (g x) = p0 := by
    filter_upwards [ae_localPhaseGradient_eq_bulk hc hd hbar, hphase] with x hx hp
    exact hx.symm.trans hp
  let : IsProbabilityMeasure (densityMeasure u) := isProbabilityMeasure hu hnorm
  have hmomentum : meanMomentum hbar u g = p0 := by
    have hM : meanMomentum hbar u g =
        mean (densityMeasure u) (fun x => bulk hbar (u x) (g x)) := by
      simpa only [meanMomentum, Complex.ofReal_re] using
        congrArg Complex.re (quantumExpectation_eq_bulk_mean hc hAC hd hu hg hbar)
    rw [hM, mean_congr (densityMeasure u) hbulk, mean_const]
  apply (WaveHeisenberg.equality_iff hc hAC hd hu hg hxu hnorm hbar hhbar).mpr
  constructor
  · simpa only [hmomentum] using hbulk
  · exact Eventually.of_forall fun x => by rw [hlog, hmean, hvariance]

/-- For every compatible supplied phase, Gaussian density and constant actual
phase derivative imply sharp uncertainty; no convenient phase is selected. -/
theorem sqrt_equality_of_supplied_phase (hc : Continuous u)
    (hAC : ∀ a b, AbsolutelyContinuousOnInterval u a b)
    (hd : ∀ᵐ x ∂volume, HasDerivAt u (g x) x)
    (hu : MemLp u 2 volume) (hg : MemLp g 2 volume)
    (hxu : MemLp (fun x : ℝ => (x : ℂ) * u x) 2 volume)
    (hnorm : (∫ x, density (u x)) = 1) (hbar : ℝ) (hhbar : 0 < hbar)
    (m : ℝ) {sigma2 : ℝ≥0} (hvar : sigma2 ≠ 0)
    (hGaussian : (fun x => density (u x)) =ᵐ[volume] gaussianPDFReal m sigma2)
    (S : ℝ → ℝ)
    (hS : ∀ᵐ x ∂volume, 0 < density (u x) → DifferentiableAt ℝ S x)
    (hpolar : ∀ x, 0 < density (u x) → u x =
      (Real.sqrt (density (u x)) : ℂ) * Complex.exp (Complex.I * ((S x / hbar : ℝ) : ℂ)))
    (p0 : ℝ) (hphase : ∀ᵐ x ∂densityMeasure u, deriv S x = p0) :
    Real.sqrt (variance (densityMeasure u) (fun x : ℝ => x)) *
      Real.sqrt (momentumVariance hbar u g) = hbar / 2 := by
  apply sqrt_equality_of_local_phase hc hAC hd hu hg hxu hnorm hbar hhbar
    m hvar hGaussian p0
  filter_upwards [ae_supplied_deriv_eq_localPhaseGradient hc hd hS hhbar.ne' hpolar,
    hphase] with x hx hp
  exact hx.symm.trans hp

end FoliationQM.GaussianDensitySaturation
