module

public import Mathlib.MeasureTheory.Measure.Support
public import Mathlib.Topology.MetricSpace.ProperSpace.Real
public import Mathlib.Analysis.Normed.Group.Uniform

/-!
# Actual mapped support inside compact tubes

An actual almost-everywhere map and label bound give zero outside mass and
true measure support containment. Properness supplies compact spatial balls.
A continuous reference on its closed time interval gives a compact spacetime
tube without any assertion that a time-dependent support graph is closed.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.MappedTubeSupport

open MeasureTheory Set Filter Metric
open scoped Topology

variable {α E : Type*} [MeasurableSpace α] [MetricSpace E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure α} {X : α → E} {y : E} {r : ℝ}

/-- A genuine measurable map transports the almost-everywhere label bound to the actual closed ball. -/
theorem ae_map_mem_closedBall (hX : AEMeasurable X μ)
    (hb : ∀ᵐ a ∂μ, dist (X a) y ≤ r) :
    ∀ᵐ x ∂μ.map X, x ∈ Metric.closedBall y r := by
  exact (mem_ae_map_iff hX isClosed_closedBall.measurableSet).2 hb

/-- An actual closed-ball label bound gives actual mapped measure support containment. -/
theorem support_map_subset_closedBall (hX : AEMeasurable X μ)
    (hb : ∀ᵐ a ∂μ, dist (X a) y ≤ r) :
    (μ.map X).support ⊆ Metric.closedBall y r :=
  Measure.support_subset_of_isClosed isClosed_closedBall (ae_map_mem_closedBall hX hb)

/-- The complement of the proved closed tube slice has exactly zero transported mass. -/
theorem map_compl_closedBall_eq_zero (hX : AEMeasurable X μ)
    (hb : ∀ᵐ a ∂μ, dist (X a) y ≤ r) :
    (μ.map X) (Metric.closedBall y r)ᶜ = 0 :=
  (mem_ae_iff).mp (ae_map_mem_closedBall hX hb)

/-- Properness makes the actual closed support inside a bounded tube slice compact. -/
theorem isCompact_support_map [ProperSpace E] (hX : AEMeasurable X μ)
    (hb : ∀ᵐ a ∂μ, dist (X a) y ≤ r) : IsCompact (μ.map X).support :=
  (isCompact_closedBall y r).of_isClosed_subset Measure.isClosed_support
    (support_map_subset_closedBall hX hb)

section Spacetime

variable {V : Type*} [NormedAddCommGroup V] [ProperSpace V]
  {Y : ℝ → V} {T : ℝ}

/-- The literal coordinate-time tube is compact using only reference continuity on the claimed interval. -/
theorem isCompact_worldtube (hY : ContinuousOn Y (Icc 0 T)) (r : ℝ) :
    IsCompact {tx : ℝ × V | tx.1 ∈ Icc 0 T ∧ dist tx.2 (Y tx.1) ≤ r} := by
  have hcont : ContinuousOn (fun q : ℝ × V => (q.1, Y q.1 + q.2))
      (Icc 0 T ×ˢ Metric.closedBall 0 r) :=
    continuousOn_fst.prodMk
      ((hY.comp continuousOn_fst (fun _ hp => hp.1)).add continuousOn_snd)
  have heq : {tx : ℝ × V | tx.1 ∈ Icc 0 T ∧ dist tx.2 (Y tx.1) ≤ r} =
      (fun q : ℝ × V => (q.1, Y q.1 + q.2)) '' (Icc 0 T ×ˢ Metric.closedBall 0 r) := by
    ext tx
    constructor
    · intro ht
      refine ⟨(tx.1, tx.2 - Y tx.1), ⟨ht.1, ?_⟩, ?_⟩
      · simpa only [Metric.mem_closedBall, dist_eq_norm, sub_zero] using ht.2
      · apply Prod.ext
        · rfl
        · dsimp
          abel
    · rintro ⟨q, ⟨ht, hv⟩, rfl⟩
      refine ⟨ht, ?_⟩
      simpa only [Metric.mem_closedBall, dist_eq_norm, sub_zero, add_sub_cancel_left] using hv
  rw [heq]
  exact (isCompact_Icc.prod (isCompact_closedBall (0 : V) r)).image_of_continuousOn hcont

end Spacetime
end FoliationQM.MappedTubeSupport
