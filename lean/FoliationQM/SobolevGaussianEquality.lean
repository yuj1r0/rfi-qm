module

public import FoliationQM.SobolevHeisenberg
public import FoliationQM.WaveGaussianEquality

/-!
# Gaussian equality for the actual normalized source H¹ class

Sources: v13 thm:uncertainty and eq:heisenberg, component kinds C and D.
One actual H¹ representative and weak derivative carry the original state's
finite position and momentum observables. Saturation gives a pointwise
Gaussian plane-phase wave for that continuous representative and an actual
almost-everywhere Gaussian density for the original Lp state.

Both equality directions use the actual local phase gradient. They also hold
for every genuinely compatible supplied phase on the same representative.
The supplied phase is fixed outside its equivalence; only its derivative is
asserted constant almost everywhere. No classical derivative of an arbitrary
original Lp representative or globally affine supplied branch is claimed.
Explicit Gaussian membership in the source H¹ class remains separate.
-/

@[expose] public section
noncomputable section

namespace FoliationQM.SobolevGaussianEquality

open MeasureTheory Filter ProbabilityTheory QuantumCurrentAlgebra WaveMomentumQuadraticForm
open WaveScoreAlgebra WaveDensityMeasure CenteredL2Variance SobolevCramerRao
open SobolevPhaseVariance
open scoped ENNReal NNReal SchwartzMap LineDeriv

private theorem gaussian_phase_condition_congr {u w : ℝ → ℂ}
    (huw : u =ᵐ[volume] w) (q : ℝ → ℝ) :
    (∃ (m : ℝ) (s : ℝ≥0), s ≠ 0 ∧ ∃ p0 : ℝ,
      (fun x => density (u x)) =ᵐ[volume] gaussianPDFReal m s ∧
      (∀ᵐ x ∂densityMeasure u, q x = p0)) ↔
    (∃ (m : ℝ) (s : ℝ≥0), s ≠ 0 ∧ ∃ p0 : ℝ,
      (fun x => density (w x)) =ᵐ[volume] gaussianPDFReal m s ∧
      (∀ᵐ x ∂densityMeasure w, q x = p0)) := by
  have hμ := densityMeasure_congr_ae huw
  have hρ : (fun x => density (u x)) =ᵐ[volume] (fun x => density (w x)) := by
    filter_upwards [huw] with x hx
    exact congrArg density hx
  constructor
  · rintro ⟨m, s, hs, p0, hG, hp⟩
    refine ⟨m, s, hs, p0, hρ.symm.trans hG, ?_⟩
    simpa only [hμ] using hp
  · rintro ⟨m, s, hs, p0, hG, hp⟩
    refine ⟨m, s, hs, p0, hρ.trans hG, ?_⟩
    simpa only [hμ] using hp

/-- One actual normalized H¹ representative preserves the original finite
observables and realizes saturation precisely by Gaussian density and a
constant local or arbitrary compatible supplied phase derivative. -/
theorem exists_source_gaussian_equality
    (f : Lp ℂ 2 (volume : Measure ℝ))
    (hf : TemperedDistribution.MemSobolev 1 2 (f : 𝓢'(ℝ, ℂ)))
    (hx : MemLp (fun x : ℝ => (x : ℂ) * f x) 2 volume)
    (hnorm : (∫ x : ℝ, ‖f x‖ ^ 2) = 1) (hbar : ℝ) (hhbar : 0 < hbar) :
    ∃ (g : Lp ℂ 2 (volume : Measure ℝ)) (u : ℝ → ℂ),
      let sigma2 : ℝ≥0 := ⟨variance (densityMeasure f) (fun y : ℝ => y),
        variance_nonneg (densityMeasure f) (fun y : ℝ => y)⟩
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
      0 < variance (densityMeasure f) (fun y : ℝ => y) ∧ sigma2 ≠ 0 ∧
      hbar ^ 2 / 4 ≤ variance (densityMeasure f) (fun y : ℝ => y) *
        momentumVariance hbar f g ∧
      hbar / 2 ≤ Real.sqrt (variance (densityMeasure f) (fun y : ℝ => y)) *
        Real.sqrt (momentumVariance hbar f g) ∧
      (Real.sqrt (variance (densityMeasure f) (fun y : ℝ => y)) *
          Real.sqrt (momentumVariance hbar f g) = hbar / 2 →
        ∃ theta : ℝ,
          (∀ x, u x = GaussianPlanePhaseWave.wave
            (mean (densityMeasure f) (fun y : ℝ => y)) sigma2
            (meanMomentum hbar f g / hbar) theta x) ∧
          (f =ᵐ[volume] GaussianPlanePhaseWave.wave
            (mean (densityMeasure f) (fun y : ℝ => y)) sigma2
            (meanMomentum hbar f g / hbar) theta) ∧
          (fun x => density (f x)) =ᵐ[volume] gaussianPDFReal
            (mean (densityMeasure f) (fun y : ℝ => y)) sigma2) ∧
      (Real.sqrt (variance (densityMeasure f) (fun y : ℝ => y)) *
          Real.sqrt (momentumVariance hbar f g) = hbar / 2 ↔
        ∃ (m : ℝ) (s : ℝ≥0), s ≠ 0 ∧ ∃ p0 : ℝ,
          (fun x => density (f x)) =ᵐ[volume] gaussianPDFReal m s ∧
          (∀ᵐ x ∂densityMeasure f, localPhaseGradient hbar u x = p0)) ∧
      (∀ S : ℝ → ℝ,
        (∀ᵐ x ∂volume, 0 < density (u x) → DifferentiableAt ℝ S x) →
        (∀ x, 0 < density (u x) → u x =
          (Real.sqrt (density (u x)) : ℂ) *
            Complex.exp (Complex.I * ((S x / hbar : ℝ) : ℂ))) →
        (Real.sqrt (variance (densityMeasure f) (fun y : ℝ => y)) *
            Real.sqrt (momentumVariance hbar f g) = hbar / 2 ↔
          ∃ (m : ℝ) (s : ℝ≥0), s ≠ 0 ∧ ∃ p0 : ℝ,
            (fun x => density (f x)) =ᵐ[volume] gaussianPDFReal m s ∧
            (∀ᵐ x ∂densityMeasure f, deriv S x = p0))) := by
  obtain ⟨g, u, hg, huf, hc, hAC, hd, hu, hdL2, hxu, hμ, hp,
    hX, hL, hB, hmi, hme, hvi, hve, hci, hqi, hreal, hV, hprod, hbound, _, _⟩ :=
    SobolevHeisenberg.exists_source_heisenberg f hf hx hnorm hbar hhbar
  let sigma2 : ℝ≥0 := ⟨variance (densityMeasure f) (fun y : ℝ => y),
    variance_nonneg (densityMeasure f) (fun y : ℝ => y)⟩
  have hs0 : sigma2 ≠ 0 := NNReal.coe_ne_zero.mp hV.ne'
  have hn : (∫ x, density (u x)) = 1 := by
    calc
      (∫ x, density (u x)) = ∫ x : ℝ, ‖f x‖ ^ 2 := by
        apply integral_congr_ae
        filter_upwards [huf] with x he
        exact congrArg (fun z : ℂ => ‖z‖ ^ 2) he
      _ = 1 := hnorm
  have hE : quantumExpectation hbar u g = quantumExpectation hbar f g :=
    quantumExpectation_congr_ae hbar huf EventuallyEq.rfl
  have hM : meanMomentum hbar u g = meanMomentum hbar f g := congrArg Complex.re hE
  have hQ : momentumVariance hbar u g = momentumVariance hbar f g :=
    momentumVariance_congr_ae hbar huf EventuallyEq.rfl
  refine ⟨g, u, hg, huf, hc, hAC, hd, hu, hdL2, hxu, hμ, hp,
    hX, hL, hB, hmi, hme, hvi, hve, hci, hqi, hreal, hV, hs0, hprod, hbound,
    ?_, ?_, ?_⟩
  · intro heq
    have heqU : Real.sqrt (variance (densityMeasure u) (fun y : ℝ => y)) *
        Real.sqrt (momentumVariance hbar u g) = hbar / 2 := by
      simpa only [hμ, hQ] using heq
    obtain ⟨theta, hpoint⟩ := WaveGaussianEquality.eq_wave_of_equality
      hc hAC hd hu (Lp.memLp g) hxu hn hbar hhbar heqU
    have huwave : ∀ x, u x = GaussianPlanePhaseWave.wave
        (mean (densityMeasure f) (fun y : ℝ => y)) sigma2
        (meanMomentum hbar f g / hbar) theta x := by
      simpa only [sigma2, hμ, hM] using hpoint
    have hfwave : f =ᵐ[volume] GaussianPlanePhaseWave.wave
        (mean (densityMeasure f) (fun y : ℝ => y)) sigma2
        (meanMomentum hbar f g / hbar) theta :=
      huf.symm.trans (Eventually.of_forall huwave)
    refine ⟨theta, huwave, hfwave, ?_⟩
    filter_upwards [hfwave] with x hx
    rw [hx]
    exact GaussianPlanePhaseWave.norm_sq
      (mean (densityMeasure f) (fun y : ℝ => y)) hs0
      (meanMomentum hbar f g / hbar) theta x
  · have he := (WaveGaussianEquality.equality_iff_gaussian_local_phase
      hc hAC hd hu (Lp.memLp g) hxu hn hbar hhbar).trans
      (gaussian_phase_condition_congr huf (localPhaseGradient hbar u))
    simpa only [hμ, hQ] using he
  · intro S hS hpolar
    have he := (WaveGaussianEquality.equality_iff_gaussian_supplied_phase
      hc hAC hd hu (Lp.memLp g) hxu hn hbar hhbar S hS hpolar).trans
      (gaussian_phase_condition_congr huf (deriv S))
    simpa only [hμ, hQ] using he

end FoliationQM.SobolevGaussianEquality
