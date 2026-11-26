module

public import FoliationQM.CompactAuxiliaryMetricEnergy
public import FoliationQM.CirclePolarEnergy
public import Mathlib.Analysis.Calculus.FDeriv.Measurable
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Integral.IntegrableOn

/-!
# Positive polar energy gives actual coordinate L² data

Source: v13 `thm:wallstrom` Part (c), component kind C.
The positive auxiliary metric is continuous and positive on a compact
comparison region. Genuine weighted integrability on a measurable subset
implies unweighted coordinate L² data. For the supplied circle phase,
the polar energy is integrated against the actual positive volume density,
and the conclusion uses the actual field and its actual derivatives.
No extension across the excluded set or Sobolev membership is asserted.
-/

@[expose] public section
noncomputable section

namespace FoliationQM.WeightedPolarEnergyL2

open MeasureTheory Set LorentzMatrixGroup RNCCoordinateConnection
open AuxiliaryMetricEnergy CompactAuxiliaryMetricEnergy CirclePolarEnergy
open scoped Matrix.Norms.Operator

/-- Genuine integrability of the positive density-weighted total energy gives L² of the field and every complex covector coordinate on any measurable subset of the compact comparison region. -/
theorem memLp_of_weighted_energy {K S : Set Covector} {H : Covector → Mat4}
    (hK : IsCompact K) (hS : MeasurableSet S) (hs : S ⊆ K)
    (hH : ContinuousOn H K) (hpos : ∀ x ∈ K, (H x).PosDef)
    {ψ : Covector → ℂ} {z : Covector → Fin 4 → ℂ}
    (hψ : AEStronglyMeasurable ψ (volume.restrict S))
    (hz : ∀ i, AEStronglyMeasurable (fun x => z x i) (volume.restrict S))
    (he : Integrable (fun x => density (H x) *
      (‖ψ x‖ ^ 2 + complexEnergy (H x) (z x))) (volume.restrict S)) :
    MemLp ψ 2 (volume.restrict S) ∧
      ∀ i : Fin 4, MemLp (fun x => z x i) 2 (volume.restrict S) := by
  obtain ⟨C, hC, hb⟩ := compact_energy_comparison hK hH hpos
  have hψsq : AEStronglyMeasurable (fun x => ‖ψ x‖ ^ 2) (volume.restrict S) := by
    simpa only [pow_two] using! hψ.norm.mul hψ.norm
  have hzsq (i : Fin 4) :
      AEStronglyMeasurable (fun x => ‖z x i‖ ^ 2) (volume.restrict S) := by
    simpa only [pow_two] using! (hz i).norm.mul (hz i).norm
  constructor
  · apply (memLp_two_iff_integrable_sq_norm hψ).2
    apply (he.const_mul C).mono_nonneg hψsq
      (Filter.Eventually.of_forall fun x => sq_nonneg ‖ψ x‖)
    apply ae_restrict_of_forall_mem hS
    intro x hx
    have hd : 0 ≤ density (H x) := (density_pos (hpos x (hs hx))).le
    have hp := complexEnergy_nonneg (hpos x (hs hx)) (z x)
    exact ((hb x (hs hx)).1 (ψ x)).trans <|
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hp) hd) hC.le
  · intro i
    apply (memLp_two_iff_integrable_sq_norm (hz i)).2
    apply (he.const_mul C).mono_nonneg (hzsq i)
      (Filter.Eventually.of_forall fun x => sq_nonneg ‖z x i‖)
    apply ae_restrict_of_forall_mem hS
    intro x hx
    have hd : 0 ≤ density (H x) := (density_pos (hpos x (hs hx))).le
    exact ((hb x (hs hx)).2.2 (z x) i).trans <|
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (sq_nonneg ‖ψ x‖)) hd) hC.le

/-- Finite polar energy for the actual positive volume measure gives L² of the reconstructed field and its actual coordinate derivatives, using the supplied unit-circle differential without a global real phase. -/
theorem polar_memLp {K S : Set Covector} {H : Covector → Mat4}
    (hK : IsCompact K) (hS : MeasurableSet S) (hs : S ⊆ K)
    (hH : ContinuousOn H K) (hpos : ∀ x ∈ K, (H x).PosDef)
    {R : Covector → ℝ} {q : Covector → ℂ}
    {dR α : Covector → Covector →L[ℝ] ℝ} {ω : ℝ}
    (hR : ∀ x ∈ S, HasFDerivAt R (dR x) x)
    (hq : ∀ x ∈ S, HasFDerivAt q
      ((α x).smulRight (-Complex.I * (ω : ℂ) * q x)) x)
    (hunit : ∀ x ∈ S, ‖q x‖ = 1)
    (he : Integrable (fun x => (R x) ^ 2 +
      realEnergy (H x) (fun i => dR x (axis i)) +
      ω ^ 2 * (R x) ^ 2 * realEnergy (H x) (fun i => α x (axis i)))
      ((volume.restrict S).withDensity (fun x => ENNReal.ofReal (density (H x))))) :
    MemLp (field R q) 2 (volume.restrict S) ∧ ∀ i : Fin 4,
      MemLp (fun x => fderiv ℝ (field R q) x (axis i)) 2 (volume.restrict S) := by
  have hf : ContinuousOn (field R q) S := by
    intro x hx
    exact (hasFDerivAt_field (hR x hx) (hq x hx)).continuousAt.continuousWithinAt
  have hd : ContinuousOn (fun x => density (H x)) S := by
    have hc : Continuous (fun A : Mat4 => density A) :=
      Real.continuous_sqrt.comp continuous_id.matrix_det
    exact hc.comp_continuousOn (hH.mono hs)
  have hw := (integrable_withDensity_iff_integrable_smul₀'
    ((hd.aestronglyMeasurable hS).aemeasurable.ennreal_ofReal)
    (Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top)).1 he
  apply memLp_of_weighted_energy hK hS hs hH hpos (hf.aestronglyMeasurable hS)
    (fun i => (measurable_fderiv_apply_const ℝ (field R q) (axis i)).aestronglyMeasurable)
  apply hw.congr
  apply ae_restrict_of_forall_mem hS
  intro x hx
  obtain ⟨hn, hdq⟩ := energy_split (H x) (hR x hx) (hq x hx) (hunit x hx)
  dsimp only
  rw [ENNReal.toReal_ofReal (show 0 ≤ density (H x) from Real.sqrt_nonneg _)]
  change density (H x) * ((R x) ^ 2 +
      realEnergy (H x) (fun i => dR x (axis i)) +
      ω ^ 2 * (R x) ^ 2 * realEnergy (H x) (fun i => α x (axis i))) =
    density (H x) * (‖field R q x‖ ^ 2 +
      complexEnergy (H x) (fun i => fderiv ℝ (field R q) x (axis i)))
  rw [hn, hdq]
  ring

end FoliationQM.WeightedPolarEnergyL2
