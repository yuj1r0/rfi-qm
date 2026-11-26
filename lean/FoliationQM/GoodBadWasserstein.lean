module

public import FoliationQM.WassersteinDirac
public import FoliationQM.UniformTransportConcentration
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# Genuine transport moments on complementary label sets

Source: v13 `rem:wkb_rates_tails` (Kinds C/D).

The extended cost splits on the label domain, even when a moment is infinite.
Real cost identities and concentration require actual integrability on both
restrictions. Every claimed pushforward has an explicit measurability witness.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.GoodBadWasserstein

open MeasureTheory Set Filter WassersteinCoupling
open scoped ENNReal Topology

variable {Label E : Type*} [MeasurableSpace Label]
  [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure Label} [IsProbabilityMeasure μ]
  {S : Set Label} {X : Label → E} {y : E}

/-- The actual extended Dirac cost is the sum of its two label-restricted moments. -/
theorem eW1_dirac_restrict_split (hs : MeasurableSet S)
    (hX : AEMeasurable X μ) :
    eW1 (μ.map X) (Measure.dirac y) =
      (∫⁻ a, edist (X a) y ∂μ.restrict S) +
      ∫⁻ a, edist (X a) y ∂μ.restrict Sᶜ := by
  rw [WassersteinDirac.eW1_dirac,
    lintegral_map' measurable_edist_left.aemeasurable hX]
  exact (lintegral_add_compl (fun a => edist (X a) y) hs).symm

/-- Genuine integrability on both restrictions first gives finite cost, then its exact real split. -/
theorem eW1_dirac_finite_and_split (hs : MeasurableSet S)
    (hX : AEMeasurable X μ)
    (hGood : Integrable (fun a => dist (X a) y) (μ.restrict S))
    (hBad : Integrable (fun a => dist (X a) y) (μ.restrict Sᶜ)) :
    eW1 (μ.map X) (Measure.dirac y) ≠ ∞ ∧
      (eW1 (μ.map X) (Measure.dirac y)).toReal =
        (∫ a, dist (X a) y ∂μ.restrict S) +
        ∫ a, dist (X a) y ∂μ.restrict Sᶜ := by
  have hGlobal : Integrable (fun a => dist (X a) y) μ := by
    simpa only [Measure.restrict_add_restrict_compl hs] using hGood.add_measure hBad
  have hTarget : AEStronglyMeasurable (fun x : E => dist x y) (μ.map X) :=
    (continuous_id.dist continuous_const).aestronglyMeasurable
  have hMapped : Integrable (fun x : E => dist x y) (μ.map X) :=
    (integrable_map_measure hTarget hX).mpr hGlobal
  obtain ⟨hf, he⟩ := WassersteinDirac.eW1_dirac_finite_and_toReal hMapped
  refine ⟨hf, he.trans ?_⟩
  rw [integral_map hX hTarget]
  exact (integral_add_compl hs hGlobal).symm

variable {ι : Type*} {T : ℝ} {Y : ℝ → E} {Bgood Bbad : ι → ℝ}

/-- Vanishing true good and bad first moments give finite uniform costs and the actual time-supremum limit. -/
theorem family_uniform_concentration
    (μ : ι → Measure Label) [∀ i, IsProbabilityMeasure (μ i)]
    (S : ι → Set Label) (hs : ∀ i, MeasurableSet (S i))
    (X : ι → ℝ → Label → E)
    (ν : ι → ℝ → ProbabilityMeasure E) (l : Filter ι)
    (hT : 0 ≤ T)
    (hGood : ∀ᶠ i in l, ∀ t ∈ Icc 0 T,
      AEMeasurable (X i t) (μ i) ∧
      (ν i t : Measure E) = (μ i).map (X i t) ∧
      Integrable (fun a => dist (X i t a) (Y t)) ((μ i).restrict (S i)) ∧
      Integrable (fun a => dist (X i t a) (Y t)) ((μ i).restrict (S i)ᶜ) ∧
      (∫ a, dist (X i t a) (Y t) ∂(μ i).restrict (S i)) ≤ Bgood i ∧
      (∫ a, dist (X i t a) (Y t) ∂(μ i).restrict (S i)ᶜ) ≤ Bbad i)
    (hBg : Tendsto Bgood l (𝓝 0)) (hBb : Tendsto Bbad l (𝓝 0)) :
    (∀ᶠ i in l, ∀ t ∈ Icc 0 T,
      eW1 (ν i t : Measure E) (Measure.dirac (Y t)) ≠ ∞) ∧
    TendstoUniformlyOn
      (fun i t => (eW1 (ν i t : Measure E) (Measure.dirac (Y t))).toReal)
      (fun _ => 0) l (Icc 0 T) ∧
    Tendsto (fun i => UniformTransportConcentration.timeSup
      (fun t => (eW1 (ν i t : Measure E) (Measure.dirac (Y t))).toReal) T)
      l (𝓝 0) := by
  apply UniformTransportConcentration.uniform_concentration_of_bound
    (B := fun i => Bgood i + Bbad i) l hT ?_
    (by simpa only [zero_add] using hBg.add hBb)
  filter_upwards [hGood] with i hi t ht
  obtain ⟨hX, hmap, hGI, hBI, hG, hB⟩ := hi t ht
  rw [hmap]
  obtain ⟨hf, he⟩ := eW1_dirac_finite_and_split (hs i) hX hGI hBI
  exact ⟨hf, he.le.trans (add_le_add hG hB)⟩

end FoliationQM.GoodBadWasserstein
