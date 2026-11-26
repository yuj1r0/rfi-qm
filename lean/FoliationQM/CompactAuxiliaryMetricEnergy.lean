module

public import FoliationQM.AuxiliaryMetricEnergy
public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.Order.Compact

/-!
# Compact comparison with positive auxiliary-metric energy

Source: v13 `thm:wallstrom` Part (c) and `eq:weak_pde_cutoff_bound`.
Compactness and continuity turn the pointwise positive-metric estimates
into one constant chosen before any field or covector. The density lower
bound is derived from positive definiteness, including for an empty compact
set. Integrability and weak extension are separate consumer statements.
-/

@[expose] public section
noncomputable section

namespace FoliationQM.CompactAuxiliaryMetricEnergy

open Set LorentzMatrixGroup AuxiliaryMetricEnergy
open scoped Matrix.Norms.Operator

variable {X : Type*} [TopologicalSpace X]

/-- A continuous positive metric on a compact set has a strictly positive uniform volume-density lower bound and a nonnegative upper bound for all its diagonal entries. -/
theorem compact_density_diagonal_bounds {K : Set X} {H : X → Mat4}
    (hK : IsCompact K) (hH : ContinuousOn H K)
    (hpos : ∀ x ∈ K, (H x).PosDef) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ B : ℝ, 0 ≤ B ∧
      ∀ x ∈ K, δ ≤ density (H x) ∧ ∀ i : Fin 4, H x i i ≤ B := by
  have hd : ContinuousOn (fun x => density (H x)) K := by
    have hc : Continuous (fun A : Mat4 => density A) :=
      Real.continuous_sqrt.comp continuous_id.matrix_det
    exact hc.comp_continuousOn hH
  obtain ⟨δ, hδ, hδbound⟩ := hK.exists_forall_le' hd
    (fun x hx => density_pos (hpos x hx))
  let f : X → (Fin 4 → ℝ) := fun x i => H x i i
  have hf : ContinuousOn f K := continuousOn_pi.mpr fun i =>
    continuousOn_pi.mp (continuousOn_pi.mp hH i) i
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn hf
  refine ⟨δ, hδ, max B 0, le_max_right _ _, ?_⟩
  intro x hx
  refine ⟨hδbound x hx, ?_⟩
  intro i
  calc
    H x i i ≤ ‖H x i i‖ := le_abs_self _
    _ ≤ ‖f x‖ := norm_le_pi_norm (f x) i
    _ ≤ max B 0 := (hB x hx).trans (le_max_left _ _)

/-- One positive constant determined only by a compact region and its continuous positive metric controls the scalar square and every real or complex covector coordinate square by the actual density-weighted positive energy. -/
theorem compact_energy_comparison {K : Set X} {H : X → Mat4}
    (hK : IsCompact K) (hH : ContinuousOn H K)
    (hpos : ∀ x ∈ K, (H x).PosDef) :
    ∃ C : ℝ, 0 < C ∧ ∀ x ∈ K,
      (∀ u : ℂ, ‖u‖ ^ 2 ≤ C * (density (H x) * ‖u‖ ^ 2)) ∧
      (∀ (a : Covector) (i : Fin 4),
        a i ^ 2 ≤ C * (density (H x) * realEnergy (H x) a)) ∧
      (∀ (z : Fin 4 → ℂ) (i : Fin 4),
        ‖z i‖ ^ 2 ≤ C * (density (H x) * complexEnergy (H x) z)) := by
  obtain ⟨δ, hδ, B, hB, hb⟩ := compact_density_diagonal_bounds hK hH hpos
  let C := max δ⁻¹ (B / δ)
  have hC : 0 < C := lt_of_lt_of_le (inv_pos.mpr hδ) (le_max_left _ _)
  have h1 : 1 ≤ C * δ := by
    calc
      1 = δ⁻¹ * δ := by rw [inv_mul_cancel₀ hδ.ne']
      _ ≤ C * δ := mul_le_mul_of_nonneg_right (le_max_left _ _) hδ.le
  have hBC : B ≤ C * δ := (div_le_iff₀ hδ).mp (le_max_right _ _)
  refine ⟨C, hC, ?_⟩
  intro x hx
  have hd : C * δ ≤ C * density (H x) :=
    mul_le_mul_of_nonneg_left (hb x hx).1 hC.le
  refine ⟨?_, ?_, ?_⟩
  · intro u
    simpa only [one_mul, mul_assoc] using
      mul_le_mul_of_nonneg_right (h1.trans hd) (sq_nonneg ‖u‖)
  · intro a i
    calc
      a i ^ 2 ≤ H x i i * realEnergy (H x) a := coordinate_sq_le (hpos x hx) a i
      _ ≤ (C * density (H x)) * realEnergy (H x) a :=
        mul_le_mul_of_nonneg_right ((hb x hx).2 i |>.trans (hBC.trans hd))
          (realEnergy_nonneg (hpos x hx) a)
      _ = _ := mul_assoc _ _ _
  · intro z i
    calc
      ‖z i‖ ^ 2 ≤ H x i i * complexEnergy (H x) z :=
        complex_coordinate_sq_le (hpos x hx) z i
      _ ≤ (C * density (H x)) * complexEnergy (H x) z :=
        mul_le_mul_of_nonneg_right ((hb x hx).2 i |>.trans (hBC.trans hd))
          (complexEnergy_nonneg (hpos x hx) z)
      _ = _ := mul_assoc _ _ _

end FoliationQM.CompactAuxiliaryMetricEnergy
