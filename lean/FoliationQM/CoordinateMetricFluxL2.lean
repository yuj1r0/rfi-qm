module

public import FoliationQM.CurvedFluxRegularity
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn

/-!
# Compact metric bounds and genuine local flux integrability

Source: v13 `eq:weak_pde_cutoff_bound`, coefficient and flux components.
A C¹ metric with negative determinant on a containing set has uniformly
bounded densitized inverse coefficients on each compact subset. Those
actual coefficients preserve local L² coordinate derivatives in the flux.
The bound is chosen before the field. General positive-metric comparison
and estimates localized to the cutoff derivative's support remain separate.
-/

@[expose] public section
noncomputable section

namespace FoliationQM.CoordinateMetricFluxL2

open MeasureTheory Set LorentzMatrixGroup RNCCoordinateConnection CurvedWaveDivergence
open scoped Matrix.Norms.Operator

/-- On a compact subset, local C¹ metric data and a negative determinant give one nonnegative bound for every actual densitized inverse coefficient, together with genuine L∞ integrability for all those coefficients. -/
theorem coefficient_data {C U : Set Covector} {g : Covector → Mat4}
    (hC : IsCompact C) (hs : C ⊆ U)
    (hg : ∀ x ∈ U, ContDiffAt ℝ 1 g x) (hd : ∀ x ∈ U, (g x).det < 0) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ i j : Fin 4,
      (∀ x ∈ C, ‖coefficient g x i j‖ ≤ B) ∧
      MemLp (fun x => coefficient g x i j) ⊤ (volume.restrict C) := by
  have hc (i j : Fin 4) : ContinuousOn (fun x => coefficient g x i j) C := by
    intro x hx
    exact (CurvedFluxRegularity.coefficient_contDiffAt (hg x (hs hx))
      (hd x (hs hx)) i j).continuousAt.continuousWithinAt
  let f : Covector → (Fin 4 × Fin 4 → ℝ) := fun x ij => coefficient g x ij.1 ij.2
  have hf : ContinuousOn f C := continuousOn_pi.mpr fun ij => hc ij.1 ij.2
  obtain ⟨B, hB⟩ := hC.exists_bound_of_continuousOn hf
  refine ⟨max B 0, le_max_right _ _, ?_⟩
  intro i j
  have hb : ∀ x ∈ C, ‖coefficient g x i j‖ ≤ max B 0 := by
    intro x hx
    exact (norm_le_pi_norm (f x) (i, j)).trans ((hB x hx).trans (le_max_left _ _))
  exact ⟨hb, memLp_top_of_bound ((hc i j).aestronglyMeasurable hC.measurableSet)
    (max B 0) (ae_restrict_of_forall_mem hC.measurableSet hb)⟩

/-- The metric and compact set determine a nonnegative constant before the field: each actual flux component is L² when the actual coordinate derivatives are locally L², and its pointwise norm is bounded by that constant times their finite norm sum. -/
theorem flux_data {C U : Set Covector} {g : Covector → Mat4}
    (hC : IsCompact C) (hs : C ⊆ U)
    (hg : ∀ x ∈ U, ContDiffAt ℝ 1 g x) (hd : ∀ x ∈ U, (g x).det < 0) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ ψ : Covector → ℂ,
      (∀ j : Fin 4, MemLp (fun x => fderiv ℝ ψ x (axis j)) 2 (volume.restrict U)) →
      ∀ i : Fin 4, MemLp (fun x => flux g ψ x i) 2 (volume.restrict C) ∧
        ∀ x ∈ C, ‖flux g ψ x i‖ ≤ B * ∑ j, ‖fderiv ℝ ψ x (axis j)‖ := by
  obtain ⟨B, hB, hc⟩ := coefficient_data hC hs hg hd
  refine ⟨B, hB, ?_⟩
  intro ψ hψ i
  have hp (j : Fin 4) : MemLp (fun x => fderiv ℝ ψ x (axis j)) 2
      (volume.restrict C) := MemLp.mono_measure (Measure.restrict_mono_set volume hs) (hψ j)
  constructor
  · unfold flux
    exact memLp_finsetSum Finset.univ fun j _ => (hc i j).2.smul (hp j)
  · intro x hx
    calc
      ‖flux g ψ x i‖ ≤ ∑ j, ‖coefficient g x i j • fderiv ℝ ψ x (axis j)‖ :=
        norm_sum_le _ _
      _ ≤ ∑ j, B * ‖fderiv ℝ ψ x (axis j)‖ := by
        apply Finset.sum_le_sum
        intro j _
        rw [norm_smul]
        exact mul_le_mul_of_nonneg_right ((hc i j).1 x hx) (norm_nonneg _)
      _ = B * ∑ j, ‖fderiv ℝ ψ x (axis j)‖ := by rw [Finset.mul_sum]

end FoliationQM.CoordinateMetricFluxL2
