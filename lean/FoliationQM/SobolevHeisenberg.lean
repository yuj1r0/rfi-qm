module

public import FoliationQM.SobolevMomentumVariance
public import FoliationQM.WaveHeisenberg

/-!
# Actual Heisenberg inequality for the normalized source H¹ class

Sources: v13 eq:heisenberg and thm:uncertainty, component kinds C and D.
One actual H¹ representative carries the independently supplied position
moment, the genuine weak derivative, and every density and momentum identity.
The position variance uses the original density measure, and the momentum
quadratic form uses the original state and actual L² weak derivative.

The literal square-root bound and weighted equality criterion are derived.
Saturation gives an actual almost-everywhere differential equation for that
same AC representative. Solving it, Gaussian classification and compatibility
with a supplied phase remain separate. No classical derivative of an arbitrary
original Lp representative or squared-operator domain is asserted.
-/

@[expose] public section
noncomputable section

namespace FoliationQM.SobolevHeisenberg

open MeasureTheory Filter QuantumCurrentAlgebra WaveMomentumQuadraticForm
open WaveScoreAlgebra WaveDensityMeasure CenteredL2Variance SobolevCramerRao
open scoped ENNReal SchwartzMap LineDeriv

private theorem transport_original_weight {u w : ℝ → ℂ} (hu : Continuous u)
    (huw : u =ᵐ[volume] w) {q : ℝ → ℝ} (hq : Integrable q (densityMeasure u)) :
    Integrable (fun x => density (w x) * q x) volume ∧
      (∫ x, q x ∂densityMeasure u) = ∫ x, density (w x) * q x := by
  have ht : Integrable (fun x => density (u x) * q x) volume ∧
      (∫ x, q x ∂densityMeasure u) = ∫ x, density (u x) * q x := by
    simpa only [smul_eq_mul] using integrable_and_integral_transport hu hq
  have he : (fun x => density (u x) * q x) =ᵐ[volume]
      (fun x => density (w x) * q x) := by
    filter_upwards [huw] with x hx
    rw [hx]
  exact ⟨ht.1.congr he, ht.2.trans (integral_congr_ae he)⟩

/-- Actual normalized H¹ data and a separate position moment give finite
original-state variances, the literal Heisenberg bound, its weighted equality
criterion, and the saturation ODE on one actual AC representative. -/
theorem exists_source_heisenberg
    (f : Lp ℂ 2 (volume : Measure ℝ))
    (hf : TemperedDistribution.MemSobolev 1 2 (f : 𝓢'(ℝ, ℂ)))
    (hx : MemLp (fun x : ℝ => (x : ℂ) * f x) 2 volume)
    (hnorm : (∫ x : ℝ, ‖f x‖ ^ 2) = 1) (hbar : ℝ) (hhbar : 0 < hbar) :
    ∃ (g : Lp ℂ 2 (volume : Measure ℝ)) (u : ℝ → ℂ),
      ∂_{(1 : ℝ)} (f : 𝓢'(ℝ, ℂ)) = (g : 𝓢'(ℝ, ℂ)) ∧
      u =ᵐ[volume] f ∧ Continuous u ∧
      (∀ a b, AbsolutelyContinuousOnInterval u a b) ∧
      (∀ᵐ x ∂volume, HasDerivAt u (g x) x) ∧
      MemLp u 2 volume ∧ MemLp (deriv u) 2 volume ∧
      MemLp (fun x : ℝ => (x : ℂ) * u x) 2 volume ∧
      densityMeasure u = densityMeasure f ∧ IsProbabilityMeasure (densityMeasure f) ∧
      MemLp (fun x : ℝ => x) 2 (densityMeasure f) ∧
      MemLp (logDensityDerivative u) 2 (densityMeasure f) ∧
      MemLp (fun x => bulk hbar (u x) (g x)) 2 (densityMeasure f) ∧
      Integrable (fun x => density (f x) * x) volume ∧
      mean (densityMeasure f) (fun y : ℝ => y) = (∫ x, density (f x) * x) ∧
      Integrable (fun x => density (f x) *
        (centered (densityMeasure f) (fun y : ℝ => y) x) ^ 2) volume ∧
      variance (densityMeasure f) (fun y : ℝ => y) =
        (∫ x, density (f x) * (centered (densityMeasure f) (fun y : ℝ => y) x) ^ 2) ∧
      Integrable (fun x => current hbar (f x) (g x)) volume ∧
      Integrable (fun x => ‖centeredPValue hbar (meanMomentum hbar f g)
        (f x) (g x)‖ ^ 2) volume ∧
      quantumExpectation hbar f g = (meanMomentum hbar f g : ℂ) ∧
      0 < variance (densityMeasure f) (fun y : ℝ => y) ∧
      hbar ^ 2 / 4 ≤ variance (densityMeasure f) (fun y : ℝ => y) *
        momentumVariance hbar f g ∧
      hbar / 2 ≤ Real.sqrt (variance (densityMeasure f) (fun y : ℝ => y)) *
        Real.sqrt (momentumVariance hbar f g) ∧
      (Real.sqrt (variance (densityMeasure f) (fun y : ℝ => y)) *
          Real.sqrt (momentumVariance hbar f g) = hbar / 2 ↔
        (∀ᵐ x ∂densityMeasure f, bulk hbar (u x) (g x) = meanMomentum hbar f g) ∧
        (∀ᵐ x ∂densityMeasure f, logDensityDerivative u x =
          -centered (densityMeasure f) (fun y : ℝ => y) x /
            variance (densityMeasure f) (fun y : ℝ => y))) ∧
      (Real.sqrt (variance (densityMeasure f) (fun y : ℝ => y)) *
          Real.sqrt (momentumVariance hbar f g) = hbar / 2 →
        ∀ᵐ x ∂volume, g x =
          (((-(centered (densityMeasure f) (fun y : ℝ => y) x /
              (2 * variance (densityMeasure f) (fun y : ℝ => y))) : ℝ) : ℂ) +
            Complex.I * ((meanMomentum hbar f g / hbar : ℝ) : ℂ)) * u x) := by
  obtain ⟨g, u, hg, huf, hc, hAC, hd, hu, hdL2, hxu⟩ :=
    SobolevACRepresentative.exists_locally_ac_representative_with_position f hf hx
  have hn : (∫ x, density (u x)) = 1 := by
    calc
      (∫ x, density (u x)) = ∫ x : ℝ, ‖f x‖ ^ 2 := by
        apply integral_congr_ae
        filter_upwards [huf] with x he
        exact congrArg (fun z : ℂ => ‖z‖ ^ 2) he
      _ = 1 := hnorm
  have hμ : densityMeasure u = densityMeasure f := densityMeasure_congr_ae huf
  have hp : IsProbabilityMeasure (densityMeasure u) := isProbabilityMeasure hu hn
  let : IsProbabilityMeasure (densityMeasure u) := hp
  have hpF : IsProbabilityMeasure (densityMeasure f) := hμ ▸ hp
  have hX : MemLp (fun x : ℝ => x) 2 (densityMeasure u) := memLp_position hc hxu
  have hL : MemLp (logDensityDerivative u) 2 (densityMeasure u) :=
    memLp_log_derivative hc hd (Lp.memLp g)
  have hB := memLp_bulk hc (Lp.memLp g) hbar
  obtain ⟨hmi, hme⟩ := transport_original_weight hc huf
    (CenteredL2Variance.integrable (densityMeasure u) hX)
  obtain ⟨hvi, hve⟩ := transport_original_weight hc huf
    (integrable_centered_sq (densityMeasure u) hX)
  have hE : quantumExpectation hbar u g = quantumExpectation hbar f g :=
    quantumExpectation_congr_ae hbar huf EventuallyEq.rfl
  have hM : meanMomentum hbar u g = meanMomentum hbar f g := congrArg Complex.re hE
  have hQ : momentumVariance hbar u g = momentumVariance hbar f g :=
    momentumVariance_congr_ae hbar huf EventuallyEq.rfl
  have hEb : quantumExpectation hbar f g =
      (mean (densityMeasure u) (fun x => bulk hbar (u x) (g x)) : ℂ) :=
    hE.symm.trans (quantumExpectation_eq_bulk_mean hc hAC hd hu (Lp.memLp g) hbar)
  have hP : meanMomentum hbar f g =
      mean (densityMeasure u) (fun x => bulk hbar (u x) (g x)) := by
    simpa only [meanMomentum, Complex.ofReal_re] using congrArg Complex.re hEb
  have hreal : quantumExpectation hbar f g = (meanMomentum hbar f g : ℂ) :=
    hEb.trans (congrArg Complex.ofReal hP.symm)
  refine ⟨g, u, hg, huf, hc, hAC, hd, hu, hdL2, hxu, hμ, hpF,
    ?_, ?_, ?_, hmi, ?_, ?_, ?_,
    integrable_current hbar (Lp.memLp f) (Lp.memLp g),
    integrable_centered_norm_sq hbar (meanMomentum hbar f g) (Lp.memLp f) (Lp.memLp g),
    hreal, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [hμ] using hX
  · simpa only [hμ] using hL
  · simpa only [hμ] using hB
  · simpa only [mean, hμ] using hme
  · simpa only [hμ] using hvi
  · simpa only [variance, hμ] using hve
  · simpa only [hμ] using WaveHeisenberg.variance_pos hc hAC hd hu (Lp.memLp g) hxu hn
  · simpa only [hμ, hQ] using
      WaveHeisenberg.squared_bound hc hAC hd hu (Lp.memLp g) hxu hn hbar
  · simpa only [hμ, hQ] using
      WaveHeisenberg.sqrt_bound hc hAC hd hu (Lp.memLp g) hxu hn hbar hhbar
  · simpa only [logDensityDerivative, centered, hμ, hQ, hM] using
      WaveHeisenberg.equality_iff hc hAC hd hu (Lp.memLp g) hxu hn hbar hhbar
  · intro heq
    have heqU : Real.sqrt (variance (densityMeasure u) (fun y : ℝ => y)) *
        Real.sqrt (momentumVariance hbar u g) = hbar / 2 := by
      simpa only [hμ, hQ] using heq
    simpa only [centered, hμ, hM] using
      WaveHeisenberg.equality_ode hc hAC hd hu (Lp.memLp g) hxu hn hbar hhbar heqU

end FoliationQM.SobolevHeisenberg
