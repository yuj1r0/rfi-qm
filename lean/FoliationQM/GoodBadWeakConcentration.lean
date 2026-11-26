module

public import FoliationQM.GoodBadTransport

/-!
# Uniform weak concentration from good moments and bad mass

An actual bundled probability family agrees eventually with its certified
measurable label pushforwards. Good restricted first moments and bad label mass
control every bounded continuous test uniformly near a compact reference image.
Bad first moments are not required. The conclusion uses the actual probability
weak topology along the supplied arbitrary filter.

Source: v13 `rem:wkb_rates_tails` (Kinds C/D).
-/

@[expose] public section
noncomputable section
namespace FoliationQM.GoodBadWeakConcentration

open MeasureTheory Set Filter
open scoped Topology BoundedContinuousFunction

variable {α E ι : Type*} [MeasurableSpace α]
  [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
  {Y : ℝ → E} {T : ℝ}

/-- True good restricted moments and vanishing bad label mass imply uniform bounded-test convergence and actual weak probability convergence, with no bad moment assumption. -/
theorem family_uniform_weak_concentration
    (μ : ι → Measure α) [∀ i, IsProbabilityMeasure (μ i)]
    (S : ι → Set α) (hs : ∀ i, MeasurableSet (S i)) (X : ι → ℝ → α → E)
    (ν : ι → ℝ → ProbabilityMeasure E) (l : Filter ι)
    (hY : ContinuousOn Y (Icc 0 T)) {B : ι → ℝ}
    (hGood : ∀ᶠ i in l, ∀ t ∈ Icc 0 T,
      AEMeasurable (X i t) (μ i) ∧
      (ν i t : Measure E) = (μ i).map (X i t) ∧
      Integrable (fun a => dist (X i t a) (Y t)) ((μ i).restrict (S i)) ∧
      (∫ a, dist (X i t a) (Y t) ∂(μ i).restrict (S i)) ≤ B i)
    (hB : Tendsto B l (𝓝 0))
    (heta : Tendsto (fun i => (μ i).real (S i)ᶜ) l (𝓝 0)) :
    (∀ f : E →ᵇ ℝ, TendstoUniformlyOn
      (fun i t => ∫ x, f x ∂(ν i t : Measure E)) (fun t => f (Y t)) l (Icc 0 T)) ∧
    (∀ t ∈ Icc 0 T, Tendsto (fun i => ν i t) l
      (𝓝 (Measure.dirac (Y t)).toProbabilityMeasure)) := by
  have hTests : ∀ f : E →ᵇ ℝ, TendstoUniformlyOn
      (fun i t => ∫ x, f x ∂(ν i t : Measure E)) (fun t => f (Y t)) l (Icc 0 T) := by
    intro f
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro ε hε
    obtain ⟨C, hC, hpoint⟩ := UniformWeakConcentration.exists_affine_test_bound
      (isCompact_Icc.image_of_continuousOn hY) f (half_pos hε)
    have hlim : Tendsto (fun i => ε / 2 + C * B i + 2 * ‖f‖ * (μ i).real (S i)ᶜ)
        l (𝓝 (ε / 2)) := by
      simpa only [mul_zero, add_zero] using
        ((hB.const_mul C).const_add (ε / 2)).add (heta.const_mul (2 * ‖f‖))
    filter_upwards [hGood, hlim.eventually_lt_const (by linarith : ε / 2 < ε)]
      with i hi hsmall t ht
    have herror : |(∫ x, f x ∂(ν i t : Measure E)) - f (Y t)| ≤
        (ε / 2) * (μ i).real (S i) +
          C * (∫ a, dist (X i t a) (Y t) ∂(μ i).restrict (S i)) +
          2 * ‖f‖ * (μ i).real (S i)ᶜ := by
      rw [(hi t ht).2.1]
      exact GoodBadTransport.test_error_le_good_affine (μ i) (hs i) (hi t ht).1 f (Y t)
        (hi t ht).2.2.1 (hpoint (Y t) (mem_image_of_mem Y ht))
    have hm : (ε / 2) * (μ i).real (S i) ≤ ε / 2 := by
      simpa only [mul_one] using
        mul_le_mul_of_nonneg_left (measureReal_le_one (μ := μ i) (s := S i)) (half_pos hε).le
    have hg : C * (∫ a, dist (X i t a) (Y t) ∂(μ i).restrict (S i)) ≤ C * B i :=
      mul_le_mul_of_nonneg_left (hi t ht).2.2.2 hC
    have hbound : |(∫ x, f x ∂(ν i t : Measure E)) - f (Y t)| < ε :=
      (herror.trans (add_le_add (add_le_add hm hg) le_rfl)).trans_lt hsmall
    simpa only [Real.dist_eq, abs_sub_comm] using hbound
  exact ⟨hTests,
    UniformWeakConcentration.tendsto_probabilityMeasure_of_uniform_integral ν l hTests⟩

end FoliationQM.GoodBadWeakConcentration
