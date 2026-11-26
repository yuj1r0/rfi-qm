module

public import FoliationQM.SobolevACRepresentative
public import FoliationQM.SobolevCramerRao
public import FoliationQM.WaveMomentumQuadraticForm

/-!
# Actual momentum quadratic variance of the normalized source H¹ class

Sources: v13 eq:p_fisher_bound, eq:p_var_decomp and thm:uncertainty,
component kinds C and D. Actual Bessel H¹ membership supplies the genuine
L² weak derivative of the original state. Its continuous AC representative
derives the canonical bulk and logarithmic score identities. Actual finite
current and quadratic integrals are retained for the original state and weak
derivative, independently of the choice of derivative representative.

No position moment is needed for these momentum identities. The osmotic
variance and momentum–Fisher bound are derived from actual integrals. Supplied
or local phase-gradient compatibility, Heisenberg and Gaussian classification
remain separate. No classical derivative of an arbitrary original Lp function
or domain condition for the square of the momentum operator is asserted.
-/

@[expose] public section
noncomputable section

namespace FoliationQM.SobolevMomentumVariance

open MeasureTheory Filter QuantumCurrentAlgebra WaveMomentumQuadraticForm
open WaveScoreAlgebra WaveDensityMeasure CenteredL2Variance SobolevCramerRao
open scoped ENNReal SchwartzMap LineDeriv

/-- Two actual L² representatives of the same distributional derivative give
the same expectation, every centered quadratic moment, and momentum variance. -/
theorem weak_derivative_observables_eq
    (f g₁ g₂ : Lp ℂ 2 (volume : Measure ℝ))
    (hg₁ : ∂_{(1 : ℝ)} (f : 𝓢'(ℝ, ℂ)) = (g₁ : 𝓢'(ℝ, ℂ)))
    (hg₂ : ∂_{(1 : ℝ)} (f : 𝓢'(ℝ, ℂ)) = (g₂ : 𝓢'(ℝ, ℂ))) (hbar : ℝ) :
    g₁ =ᵐ[volume] g₂ ∧
      quantumExpectation hbar f g₁ = quantumExpectation hbar f g₂ ∧
      (∀ p : ℝ, quadraticMoment hbar p f g₁ = quadraticMoment hbar p f g₂) ∧
      momentumVariance hbar f g₁ = momentumVariance hbar f g₂ := by
  have he : g₁ =ᵐ[volume] g₂ :=
    (SobolevWeakDerivative.of_distributional_eq f g₁ hg₁).unique_ae
      (SobolevWeakDerivative.of_distributional_eq f g₂ hg₂)
  exact ⟨he, quantumExpectation_congr_ae hbar EventuallyEq.rfl he,
    fun p => quadraticMoment_congr_ae hbar p EventuallyEq.rfl he,
    momentumVariance_congr_ae hbar EventuallyEq.rfl he⟩

/-- A normalized actual H¹ state has a finite original-state momentum quadratic
variance, equal to the canonical bulk plus actual osmotic variance and bounded
below by its genuine logarithmic Fisher contribution. -/
theorem exists_source_momentum_variance
    (f : Lp ℂ 2 (volume : Measure ℝ))
    (hf : TemperedDistribution.MemSobolev 1 2 (f : 𝓢'(ℝ, ℂ)))
    (hnorm : (∫ x : ℝ, ‖f x‖ ^ 2) = 1) (hbar : ℝ) :
    ∃ (g : Lp ℂ 2 (volume : Measure ℝ)) (u : ℝ → ℂ),
      ∂_{(1 : ℝ)} (f : 𝓢'(ℝ, ℂ)) = (g : 𝓢'(ℝ, ℂ)) ∧
      u =ᵐ[volume] f ∧ Continuous u ∧
      (∀ a b, AbsolutelyContinuousOnInterval u a b) ∧
      (∀ᵐ x ∂volume, HasDerivAt u (g x) x) ∧
      MemLp u 2 volume ∧ MemLp (deriv u) 2 volume ∧
      densityMeasure u = densityMeasure f ∧ IsProbabilityMeasure (densityMeasure u) ∧
      MemLp (fun x => pValue hbar (g x)) 2 volume ∧
      Integrable (fun x => current hbar (f x) (g x)) volume ∧
      Integrable (fun x => ‖centeredPValue hbar (meanMomentum hbar f g)
        (f x) (g x)‖ ^ 2) volume ∧
      quantumExpectation hbar f g = (meanMomentum hbar f g : ℂ) ∧
      meanMomentum hbar f g =
        mean (densityMeasure u) (fun x => bulk hbar (u x) (g x)) ∧
      MemLp (fun x => bulk hbar (u x) (g x)) 2 (densityMeasure u) ∧
      MemLp (logDensityDerivative u) 2 (densityMeasure u) ∧
      MemLp (OsmoticScoreVariance.observable hbar (logDensityDerivative u))
        2 (densityMeasure u) ∧
      mean (densityMeasure u)
        (OsmoticScoreVariance.observable hbar (logDensityDerivative u)) = 0 ∧
      variance (densityMeasure u)
        (OsmoticScoreVariance.observable hbar (logDensityDerivative u)) =
          hbar ^ 2 / 4 * fisherInformation u ∧
      Integrable (fun x => density (f x) * logDensityDerivative u x ^ 2) volume ∧
      fisherInformation u = (∫ x, density (f x) * logDensityDerivative u x ^ 2) ∧
      momentumVariance hbar f g =
        variance (densityMeasure u) (fun x => bulk hbar (u x) (g x)) +
          hbar ^ 2 / 4 * fisherInformation u ∧
      momentumVariance hbar f g =
        variance (densityMeasure u) (fun x => bulk hbar (u x) (g x)) +
          variance (densityMeasure u)
            (OsmoticScoreVariance.observable hbar (logDensityDerivative u)) ∧
      hbar ^ 2 / 4 * fisherInformation u ≤ momentumVariance hbar f g := by
  obtain ⟨g, u, hg, huf, hc, hAC, hd, hu, hdL2⟩ :=
    SobolevACRepresentative.exists_locally_ac_representative f hf
  have hn : (∫ x, density (u x)) = 1 := by
    calc
      (∫ x, density (u x)) = ∫ x : ℝ, ‖f x‖ ^ 2 := by
        apply integral_congr_ae
        filter_upwards [huf] with x he
        exact congrArg (fun z : ℂ => ‖z‖ ^ 2) he
      _ = 1 := hnorm
  have hp : IsProbabilityMeasure (densityMeasure u) := isProbabilityMeasure hu hn
  let : IsProbabilityMeasure (densityMeasure u) := hp
  have hL : MemLp (logDensityDerivative u) 2 (densityMeasure u) :=
    memLp_log_derivative hc hd (Lp.memLp g)
  have hmeanL : mean (densityMeasure u) (logDensityDerivative u) = 0 :=
    WaveScoreIntegrationByParts.integral_log_derivative hc hAC hd hu (Lp.memLp g)
  have hE : quantumExpectation hbar f g =
      (mean (densityMeasure u) (fun x => bulk hbar (u x) (g x)) : ℂ) :=
    (quantumExpectation_congr_ae hbar huf EventuallyEq.rfl).symm.trans
      (quantumExpectation_eq_bulk_mean hc hAC hd hu (Lp.memLp g) hbar)
  have hP : meanMomentum hbar f g =
      mean (densityMeasure u) (fun x => bulk hbar (u x) (g x)) := by
    simpa only [meanMomentum, Complex.ofReal_re] using congrArg Complex.re hE
  have hreal : quantumExpectation hbar f g = (meanMomentum hbar f g : ℂ) :=
    hE.trans (congrArg Complex.ofReal hP.symm)
  have hV : momentumVariance hbar f g = momentumVariance hbar u g :=
    (momentumVariance_congr_ae hbar huf EventuallyEq.rfl).symm
  have ht : Integrable (fun x => density (u x) * logDensityDerivative u x ^ 2) volume ∧
      fisherInformation u = (∫ x, density (u x) * logDensityDerivative u x ^ 2) := by
    simpa only [smul_eq_mul, fisherInformation] using
      integrable_and_integral_transport hc hL.integrable_sq
  have heWeight : (fun x => density (u x) * logDensityDerivative u x ^ 2) =ᵐ[volume]
      (fun x => density (f x) * logDensityDerivative u x ^ 2) := by
    filter_upwards [huf] with x he
    rw [he]
  refine ⟨g, u, hg, huf, hc, hAC, hd, hu, hdL2, densityMeasure_congr_ae huf, hp,
    memLp_pValue hbar (Lp.memLp g), integrable_current hbar (Lp.memLp f) (Lp.memLp g),
    integrable_centered_norm_sq hbar (meanMomentum hbar f g) (Lp.memLp f) (Lp.memLp g),
    hreal, hP, memLp_bulk hc (Lp.memLp g) hbar, hL,
    OsmoticScoreVariance.memLp_observable (densityMeasure u) hL hbar,
    OsmoticScoreVariance.mean_observable (densityMeasure u) hbar hmeanL,
    OsmoticScoreVariance.variance_observable (densityMeasure u) hL hbar hmeanL,
    ht.1.congr heWeight, ht.2.trans (integral_congr_ae heWeight), ?_, ?_, ?_⟩
  · exact hV.trans (variance_decomposition hc hAC hd hu (Lp.memLp g) hn hbar)
  · exact hV.trans (variance_decomposition_osmotic hc hAC hd hu (Lp.memLp g) hn hbar)
  · rw [hV]
    exact fisher_bound hc hAC hd hu (Lp.memLp g) hn hbar

end FoliationQM.SobolevMomentumVariance
