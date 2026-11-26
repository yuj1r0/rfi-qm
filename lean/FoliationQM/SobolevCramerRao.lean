module

public import FoliationQM.SobolevACRepresentative
public import FoliationQM.WaveScoreIntegrationByParts
public import FoliationQM.ScoreCramerRao

/-!
# Cramér–Rao for the actual normalized source H¹ class

Sources: v13 eq:cramer_rao and thm:uncertainty, component kinds C and D.
The source inputs are actual Bessel H¹ membership, a separate finite position
moment, and unit norm-square integral. The continuous locally AC representative
and its actual logarithmic score are constructed from those inputs. Whole-line
integration by parts derives the score pairing; it is not a source hypothesis.

The original state and its representative give the same density measure and
the same finite weighted integrals below. Classical logarithmic differentiation
belongs to the continuous representative. No differentiation of an arbitrary
null-set modification, momentum variance, or Gaussian classification is asserted.
-/

@[expose] public section
noncomputable section

namespace FoliationQM.SobolevCramerRao

open MeasureTheory Filter WaveScoreAlgebra WaveDensityMeasure CenteredL2Variance
open scoped ENNReal SchwartzMap LineDeriv

/-- The actual classical logarithmic derivative of the selected density representative. -/
def logDensityDerivative (u : ℝ → ℂ) (x : ℝ) : ℝ :=
  deriv (fun y => Real.log (density (u y))) x

/-- Actual Fisher information under the wave-density measure; finiteness is proved below. -/
def fisherInformation (u : ℝ → ℂ) : ℝ :=
  ∫ x, logDensityDerivative u x ^ 2 ∂densityMeasure u

/-- Null-set changes of the state preserve its actual density measure. -/
theorem densityMeasure_congr_ae {u w : ℝ → ℂ} (h : u =ᵐ[volume] w) :
    densityMeasure u = densityMeasure w := by
  apply withDensity_congr_ae
  filter_upwards [h] with x hx
  rw [hx]

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

/-- Normalized source H¹ data with a genuine position moment give an actual
AC representative, finite logarithmic score, and the derived centered pairing. -/
theorem exists_log_score_representative
    (f : Lp ℂ 2 (volume : Measure ℝ))
    (hf : TemperedDistribution.MemSobolev 1 2 (f : 𝓢'(ℝ, ℂ)))
    (hx : MemLp (fun x : ℝ => (x : ℂ) * f x) 2 volume)
    (hnorm : (∫ x : ℝ, ‖f x‖ ^ 2) = 1) :
    ∃ (g : Lp ℂ 2 (volume : Measure ℝ)) (u : ℝ → ℂ),
      ∂_{(1 : ℝ)} (f : 𝓢'(ℝ, ℂ)) = (g : 𝓢'(ℝ, ℂ)) ∧
      u =ᵐ[volume] f ∧ Continuous u ∧
      (∀ a b, AbsolutelyContinuousOnInterval u a b) ∧
      (∀ᵐ x ∂volume, HasDerivAt u (g x) x) ∧
      MemLp u 2 volume ∧ MemLp (deriv u) 2 volume ∧
      MemLp (fun x : ℝ => (x : ℂ) * u x) 2 volume ∧
      densityMeasure u = densityMeasure f ∧ IsProbabilityMeasure (densityMeasure u) ∧
      MemLp (fun x : ℝ => x) 2 (densityMeasure u) ∧
      MemLp (logDensityDerivative u) 2 (densityMeasure u) ∧
      (∫ x, logDensityDerivative u x ∂densityMeasure u) = 0 ∧
      (∫ x, centered (densityMeasure u) (fun y : ℝ => y) x *
        logDensityDerivative u x ∂densityMeasure u) = -1 := by
  obtain ⟨g, u, hg, huf, hc, hAC, hd, hu, hdL2, hxu⟩ :=
    SobolevACRepresentative.exists_locally_ac_representative_with_position f hf hx
  have hn : (∫ x, density (u x)) = 1 := by
    calc
      (∫ x, density (u x)) = ∫ x : ℝ, ‖f x‖ ^ 2 := by
        apply integral_congr_ae
        filter_upwards [huf] with x he
        exact congrArg (fun z : ℂ => ‖z‖ ^ 2) he
      _ = 1 := hnorm
  have hp : IsProbabilityMeasure (densityMeasure u) := isProbabilityMeasure hu hn
  have hL : MemLp (logDensityDerivative u) 2 (densityMeasure u) :=
    memLp_log_derivative hc hd (Lp.memLp g)
  have hmean : (∫ x, logDensityDerivative u x ∂densityMeasure u) = 0 :=
    WaveScoreIntegrationByParts.integral_log_derivative hc hAC hd hu (Lp.memLp g)
  have hpair : (∫ x, centered (densityMeasure u) (fun y : ℝ => y) x *
      logDensityDerivative u x ∂densityMeasure u) = -1 := by
    simpa only [centered, logDensityDerivative, hn] using
      WaveScoreIntegrationByParts.integral_shifted_log_derivative hc hAC hd hu
        (Lp.memLp g) hxu (mean (densityMeasure u) (fun y : ℝ => y))
  exact ⟨g, u, hg, huf, hc, hAC, hd, hu, hdL2, hxu, densityMeasure_congr_ae huf,
    hp, memLp_position hc hxu, hL, hmean, hpair⟩

/-- The actual source class satisfies the finite original-density score pairing,
Cramér–Rao product and reciprocal bounds, with exact weighted-AE affine-score equality. -/
theorem exists_source_cramer_rao
    (f : Lp ℂ 2 (volume : Measure ℝ))
    (hf : TemperedDistribution.MemSobolev 1 2 (f : 𝓢'(ℝ, ℂ)))
    (hx : MemLp (fun x : ℝ => (x : ℂ) * f x) 2 volume)
    (hnorm : (∫ x : ℝ, ‖f x‖ ^ 2) = 1) :
    ∃ u : ℝ → ℂ,
      u =ᵐ[volume] f ∧ Continuous u ∧
      (∀ a b, AbsolutelyContinuousOnInterval u a b) ∧
      densityMeasure u = densityMeasure f ∧ IsProbabilityMeasure (densityMeasure u) ∧
      MemLp (fun x : ℝ => x) 2 (densityMeasure u) ∧
      MemLp (logDensityDerivative u) 2 (densityMeasure u) ∧
      Integrable (fun x => density (f x) * x) volume ∧
      mean (densityMeasure u) (fun y : ℝ => y) = (∫ x, density (f x) * x) ∧
      (∫ x, logDensityDerivative u x ∂densityMeasure u) = 0 ∧
      (∫ x, centered (densityMeasure u) (fun y : ℝ => y) x *
        logDensityDerivative u x ∂densityMeasure u) = -1 ∧
      Integrable (fun x => density (f x) *
        (centered (densityMeasure u) (fun y : ℝ => y) x * logDensityDerivative u x)) volume ∧
      (∫ x, density (f x) *
        (centered (densityMeasure u) (fun y : ℝ => y) x * logDensityDerivative u x)) = -1 ∧
      Integrable (fun x => density (f x) *
        (centered (densityMeasure u) (fun y : ℝ => y) x) ^ 2) volume ∧
      variance (densityMeasure u) (fun y : ℝ => y) =
        (∫ x, density (f x) * (centered (densityMeasure u) (fun y : ℝ => y) x) ^ 2) ∧
      Integrable (fun x => density (f x) * logDensityDerivative u x ^ 2) volume ∧
      fisherInformation u = (∫ x, density (f x) * logDensityDerivative u x ^ 2) ∧
      0 < variance (densityMeasure u) (fun y : ℝ => y) ∧
      1 ≤ variance (densityMeasure u) (fun y : ℝ => y) * fisherInformation u ∧
      1 / variance (densityMeasure u) (fun y : ℝ => y) ≤ fisherInformation u ∧
      (variance (densityMeasure u) (fun y : ℝ => y) * fisherInformation u = 1 ↔
        ∀ᵐ x ∂densityMeasure u, logDensityDerivative u x =
          -centered (densityMeasure u) (fun y : ℝ => y) x /
            variance (densityMeasure u) (fun y : ℝ => y)) := by
  obtain ⟨g, u, _, huf, hc, hAC, _, _, _, _, hμ, hp, hX, hL, hmean, hpair⟩ :=
    exists_log_score_representative f hf hx hnorm
  let : IsProbabilityMeasure (densityMeasure u) := hp
  obtain ⟨hmo, hme⟩ := transport_original_weight hc huf
    (CenteredL2Variance.integrable (densityMeasure u) hX)
  have hpi : Integrable (fun x => centered (densityMeasure u) (fun y : ℝ => y) x *
      logDensityDerivative u x) (densityMeasure u) :=
    ((memLp_centered (densityMeasure u) hX).integrable_mul hL).congr
      (Eventually.of_forall fun _ => rfl)
  obtain ⟨hpo, hpe⟩ := transport_original_weight hc huf hpi
  obtain ⟨hvo, hve⟩ := transport_original_weight hc huf
    (integrable_centered_sq (densityMeasure u) hX)
  obtain ⟨hfo, hfe⟩ := transport_original_weight hc huf hL.integrable_sq
  refine ⟨u, huf, hc, hAC, hμ, hp, hX, hL, hmo, hme, hmean, hpair,
    hpo, hpe.symm.trans hpair, hvo, hve, hfo, hfe, ?_, ?_, ?_, ?_⟩
  · exact ScoreCramerRao.variance_pos hX hL hpair
  · exact ScoreCramerRao.cramer_rao hX hL hpair
  · exact ScoreCramerRao.reciprocal_bound hX hL hpair
  · exact ScoreCramerRao.equality_iff hX hL hpair

end FoliationQM.SobolevCramerRao
