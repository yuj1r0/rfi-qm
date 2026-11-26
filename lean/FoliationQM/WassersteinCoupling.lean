module

public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
public import Mathlib.MeasureTheory.Integral.Lebesgue.Map
public import Mathlib.Tactic

/-!
# Actual couplings and extended first Wasserstein cost

A coupling is an actual measure on the product with its two actual
pushforward marginals. The extended transport cost is the infimum over
all such couplings. Product measures witness existence for probabilities;
they do not replace the infimum. Infinite costs remain infinite.

These constructions prove symmetry and zero diagonal cost. They do not
assert the full general metric axioms, duality, or optimizer existence.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.WassersteinCoupling

open MeasureTheory Set
open scoped ENNReal

variable {E : Type*} [MeasurableSpace E]

/-- An actual measure on the product with the specified first and second marginals. -/
structure Coupling (μ ν : Measure E) where
  measure : Measure (E × E)
  fst_marginal : measure.map Prod.fst = μ
  snd_marginal : measure.map Prod.snd = ν

namespace Coupling

variable {μ ν : Measure E}

/-- The genuine product coupling of two probability measures. -/
def prod (μ ν : Measure E) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    Coupling μ ν where
  measure := μ.prod ν
  fst_marginal := by simp
  snd_marginal := by simp

/-- Swapping the coordinates pushes the actual coupling to one with reversed marginals. -/
def swap (π : Coupling μ ν) : Coupling ν μ where
  measure := π.measure.map Prod.swap
  fst_marginal := by
    rw [Measure.map_map measurable_fst measurable_swap]
    exact π.snd_marginal
  snd_marginal := by
    rw [Measure.map_map measurable_snd measurable_swap]
    exact π.fst_marginal

/-- The actual diagonal pushforward is a coupling of a measure with itself. -/
def diagonal (μ : Measure E) : Coupling μ μ where
  measure := μ.map (fun x => (x, x))
  fst_marginal := by
    rw [Measure.map_map measurable_fst (show Measurable (fun x : E => (x, x)) from measurable_id.prodMk measurable_id)]
    exact Measure.map_id
  snd_marginal := by
    rw [Measure.map_map measurable_snd (show Measurable (fun x : E => (x, x)) from measurable_id.prodMk measurable_id)]
    exact Measure.map_id

/-- Probability marginals have an actual coupling. -/
theorem nonempty (μ ν : Measure E) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    Nonempty (Coupling μ ν) :=
  ⟨prod μ ν⟩

/-- An actual coupling whose first marginal is a probability is itself a probability. -/
theorem isProbabilityMeasure (π : Coupling μ ν) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure π.measure := by
  have : IsProbabilityMeasure (π.measure.map Prod.fst) := by
    rw [π.fst_marginal]
    infer_instance
  exact Measure.isProbabilityMeasure_of_map measurable_fst.aemeasurable

end Coupling

section Metric

variable [MetricSpace E] {μ ν : Measure E}

/-- The actual nonnegative extended distance integral of a coupling. -/
def cost (π : Coupling μ ν) : ℝ≥0∞ :=
  ∫⁻ z, edist z.1 z.2 ∂π.measure

/-- Extended first Wasserstein cost, taking the infimum over all actual couplings. An empty coupling type gives infinity. -/
def eW1 (μ ν : Measure E) : ℝ≥0∞ :=
  ⨅ π : Coupling μ ν, cost π

/-- Every actual coupling supplies an upper bound for the infimum transport cost. -/
theorem eW1_le_cost (π : Coupling μ ν) : eW1 μ ν ≤ cost π :=
  iInf_le _ π

/-- A lower bound for every actual coupling is a lower bound for their infimum. -/
theorem le_eW1 {r : ℝ≥0∞} (h : ∀ π : Coupling μ ν, r ≤ cost π) :
    r ≤ eW1 μ ν :=
  le_iInf h

variable [BorelSpace E] [SecondCountableTopology E]

/-- Swapping an actual coupling preserves its distance cost. -/
theorem cost_swap (π : Coupling μ ν) : cost π.swap = cost π := by
  change (∫⁻ z : E × E, edist z.1 z.2 ∂π.measure.map Prod.swap) = _
  rw [lintegral_map measurable_edist measurable_swap]
  exact lintegral_congr fun z => edist_comm z.2 z.1

/-- The infimum over all actual couplings is symmetric, including infinite costs. -/
theorem eW1_comm (μ ν : Measure E) : eW1 μ ν = eW1 ν μ := by
  apply le_antisymm
  · apply le_eW1
    intro π
    exact (eW1_le_cost π.swap).trans_eq (cost_swap π)
  · apply le_eW1
    intro π
    exact (eW1_le_cost π.swap).trans_eq (cost_swap π)

/-- The actual diagonal coupling has zero cost. -/
theorem cost_diagonal (μ : Measure E) : cost (Coupling.diagonal μ) = 0 := by
  change (∫⁻ z : E × E, edist z.1 z.2 ∂μ.map (fun x => (x, x))) = 0
  rw [lintegral_map measurable_edist (show Measurable (fun x : E => (x, x)) from measurable_id.prodMk measurable_id)]
  simp

/-- A measure has zero extended transport cost to itself, witnessed by its actual diagonal coupling. -/
theorem eW1_self (μ : Measure E) : eW1 μ μ = 0 :=
  le_antisymm ((eW1_le_cost (Coupling.diagonal μ)).trans_eq (cost_diagonal μ)) bot_le

end Metric
end FoliationQM.WassersteinCoupling
