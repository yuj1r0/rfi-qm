module

public import FoliationQM.ObserverFisherStability
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# A parameterized limit for the observed spatial Fisher trace

The limiting assertion at v13 line 520 uses a fixed observer slice and
measure. We control amplitudes uniformly almost everywhere and prove
convergence under vanishing integrated factor-score energy. A second
criterion derives the vanishing energy from dominated pointwise limits.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.ObserverFisherLimit

open MeasureTheory Filter FisherNormalization ObserverFisherTrace
open scoped Topology BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
variable {μ : Measure E} {ρ : E → ℝ} {n : ℕ}

/-- For a parameterized family the raw Fisher trace converges to its intrinsic
value as the uniform amplitude error and the observed factor-score energy vanish. -/
theorem tendsto_fisherTrace {ι : Type*} (l : Filter ι) (G : ι → E → ℝ) (d : ι → ℝ)
    (v : Fin n → E) (hr : AEMeasurable ρ μ)
    (ha : ∀ j, AEMeasurable (fun x => score ρ x (v j)) μ)
    (hi : ∀ j, Integrable (fun x => ρ x * score ρ x (v j) ^ 2) μ)
    (hd : Tendsto d l (𝓝 0))
    (hB : Tendsto (fun i => squareEnergy μ (fun x => G i x * ρ x)
      (fun j x => score (G i) x (v j))) l (𝓝 0))
    (hf : ∀ᶠ i in l, (∀ᵐ x ∂μ, DifferentiableAt ℝ (G i) x ∧ DifferentiableAt ℝ ρ x ∧
      0 < G i x ∧ 0 < ρ x) ∧ AEMeasurable (G i) μ ∧ (∀ᵐ x ∂μ, |G i x - 1| ≤ d i) ∧
      (∀ j, AEMeasurable (fun x => score (G i) x (v j)) μ) ∧
      (∀ j, Integrable (fun x => G i x * ρ x * score (G i) x (v j) ^ 2) μ)) :
    Tendsto (fun i => fisherTrace (fun x => G i x * ρ x) v μ) l (𝓝 (fisherTrace ρ v μ)) := by
  let I := fisherTrace ρ v μ
  let B := fun i => squareEnergy μ (fun x => G i x * ρ x) (fun j x => score (G i) x (v j))
  have hrad : Tendsto (fun i => ((1 + d i) * I) * B i) l (𝓝 0) := by
    simpa only [mul_zero] using (((tendsto_const_nhds (x := (1:ℝ))).add hd).mul_const I).mul hB
  have hs : Tendsto (fun i => Real.sqrt (((1+d i)*I)*B i)) l (𝓝 0) := by
    simpa only [Function.comp_def, Real.sqrt_zero] using Real.continuous_sqrt.continuousAt.tendsto.comp hrad
  have hbound : Tendsto (fun i => d i * I + 2 * Real.sqrt (((1+d i)*I)*B i) + B i) l (𝓝 0) := by
    simpa only [zero_mul, mul_zero, add_zero] using ((hd.mul_const I).add (hs.const_mul 2)).add hB
  rw [tendsto_iff_norm_sub_tendsto_zero]
  apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) _ hbound
  filter_upwards [hf] with i h
  exact (ObserverFisherStability.fisherTrace_error v h.1 h.2.1 hr h.2.2.1 ha h.2.2.2.1 hi h.2.2.2.2).2

/-- A common integrable envelope and pointwise decay of the actual observer
scores imply vanishing of the summed observed score energy. The factor itself
converges to one almost everywhere. -/
theorem tendsto_score_energy_of_domination (G : ℕ → E → ℝ) (v : Fin n → E)
    (M : Fin n → E → ℝ) (hM : ∀ j, Integrable (M j) μ)
    (hi : ∀ k j, AEStronglyMeasurable (fun x => G k x * ρ x * score (G k) x (v j) ^ 2) μ)
    (hb : ∀ k j, ∀ᵐ x ∂μ, ‖G k x * ρ x * score (G k) x (v j) ^ 2‖ ≤ M j x)
    (hg : ∀ᵐ x ∂μ, Tendsto (fun k => G k x) atTop (𝓝 1))
    (hs : ∀ j, ∀ᵐ x ∂μ, Tendsto (fun k => score (G k) x (v j)) atTop (𝓝 0)) :
    (∀ k j, Integrable (fun x => G k x * ρ x * score (G k) x (v j) ^ 2) μ) ∧
      Tendsto (fun k => squareEnergy μ (fun x => G k x * ρ x)
        (fun j x => score (G k) x (v j))) atTop (𝓝 0) := by
  refine ⟨fun k j => (hM j).mono' (hi k j) (hb k j), ?_⟩
  have hc (j : Fin n) : Tendsto (fun k => ∫ x, G k x * ρ x * score (G k) x (v j) ^ 2 ∂μ)
      atTop (𝓝 0) := by
    have hlim : ∀ᵐ x ∂μ, Tendsto (fun k => G k x * ρ x * score (G k) x (v j) ^ 2)
        atTop (𝓝 0) := by
      filter_upwards [hg, hs j] with x hx hx'
      simpa using (hx.mul_const (ρ x)).mul (hx'.pow 2)
    simpa using tendsto_integral_of_dominated_convergence (f := fun _ => (0:ℝ)) (M j)
      (fun k => hi k j) (hM j) (fun k => hb k j) hlim
  simpa only [squareEnergy, Finset.sum_const_zero] using tendsto_finsetSum Finset.univ (fun j _ => hc j)

end FoliationQM.ObserverFisherLimit
