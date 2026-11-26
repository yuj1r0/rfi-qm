module

public import Mathlib.MeasureTheory.Measure.Restrict
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Global measure from compatible coordinate volume measures

A countable measurable chart cover determines the metric volume measure
uniquely from the local measures and their agreement on intersections.
Disjointizing the cover constructs that measure even for infinite total
volume. The result is independent of the chart enumeration.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.CurvedAtlasMeasure

open MeasureTheory Set

variable {X : Type*} [MeasurableSpace X]

/-- The measure constructed from chart measures on disjoint pieces of a countable cover. -/
def assemble (U : ℕ → Set X) (μ : ℕ → Measure X) : Measure X :=
  Measure.sum fun i => (μ i).restrict (disjointed U i)

/-- Summing the restrictions of one measure to the disjoint chart pieces recovers the original measure. -/
theorem assemble_constant (U : ℕ → Set X) (hU : ∀ i, MeasurableSet (U i)) (hcover : ⋃ i, U i = univ)
    (μ : Measure X) : assemble U (fun _ => μ) = μ := by
  rw [assemble, ← Measure.restrict_iUnion (disjoint_disjointed _) (MeasurableSet.disjointed hU),
    iUnion_disjointed, hcover, Measure.restrict_univ]

/-- The assembled measure restricts on each chart to its prescribed local volume measure. -/
theorem restrict_chart (U : ℕ → Set X) (hU : ∀ i, MeasurableSet (U i)) (hcover : ⋃ i, U i = univ)
    (μ : ℕ → Measure X)
    (hcompat : ∀ i j, (μ i).restrict (U i ∩ U j) = (μ j).restrict (U i ∩ U j)) (j : ℕ) :
    (assemble U μ).restrict (U j) = (μ j).restrict (U j) := by
  rw [assemble, Measure.restrict_sum _ (hU j)]
  calc
    _ = assemble U (fun _ => (μ j).restrict (U j)) := by
      apply congrArg Measure.sum
      funext i
      rw [Measure.restrict_restrict (hU j), Measure.restrict_restrict (MeasurableSet.disjointed hU i),
        inter_comm (disjointed U i)]
      have hsub : U j ∩ disjointed U i ⊆ U i ∩ U j := fun _ hx => ⟨disjointed_subset U i hx.2, hx.1⟩
      exact Measure.restrict_congr_mono hsub (hcompat i j)
    _ = _ := assemble_constant U hU hcover _

/-- Agreement on every chart characterizes the global volume measure. -/
theorem unique (U : ℕ → Set X) (hU : ∀ i, MeasurableSet (U i)) (hcover : ⋃ i, U i = univ)
    {μ ν : Measure X} (hs : ∀ i, μ.restrict (U i) = ν.restrict (U i)) : μ = ν := by
  rw [← assemble_constant U hU hcover μ, ← assemble_constant U hU hcover ν]
  apply congrArg Measure.sum
  funext i
  exact Measure.restrict_congr_mono (disjointed_subset U i) (hs i)

/-- Two countable measurable atlases defining equal volume measures on all cross-overlaps give exactly the same global measure. -/
theorem independent {U V : ℕ → Set X} {μ ν : ℕ → Measure X}
    (hU : ∀ i, MeasurableSet (U i)) (hV : ∀ i, MeasurableSet (V i))
    (hcU : ⋃ i, U i = univ) (hcV : ⋃ i, V i = univ)
    (hu : ∀ i j, (μ i).restrict (U i ∩ U j) = (μ j).restrict (U i ∩ U j))
    (hv : ∀ i j, (ν i).restrict (V i ∩ V j) = (ν j).restrict (V i ∩ V j))
    (hcross : ∀ i j, (μ i).restrict (U i ∩ V j) = (ν j).restrict (U i ∩ V j)) :
    assemble U μ = assemble V ν := by
  apply unique U hU hcU
  intro i
  rw [restrict_chart U hU hcU μ hu]
  apply unique V hV hcV
  intro j
  rw [Measure.restrict_restrict (hV j), Measure.restrict_restrict (hV j), inter_comm (V j)]
  exact (hcross i j).trans (Measure.restrict_congr_mono inter_subset_right (restrict_chart V hV hcV ν hv j).symm)

/-- Integrating a global scalar over a chart uses the chart's own metric volume measure. -/
theorem integral_chart {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (U : ℕ → Set X) (hU : ∀ i, MeasurableSet (U i)) (hcover : ⋃ i, U i = univ)
    (μ : ℕ → Measure X)
    (hcompat : ∀ i j, (μ i).restrict (U i ∩ U j) = (μ j).restrict (U i ∩ U j))
    (j : ℕ) (f : X → E) :
    (∫ x in U j, f x ∂(assemble U μ)) = ∫ x in U j, f x ∂(μ j) := by
  rw [restrict_chart U hU hcover μ hcompat]

end FoliationQM.CurvedAtlasMeasure
