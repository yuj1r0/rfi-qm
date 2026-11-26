module

public import FoliationQM.AuxiliaryMetricEnergy
public import FoliationQM.CoordinateCutoffCompactEnergy
public import FoliationQM.LorentzCayleySmooth
public import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
# Actual positive auxiliary-metric cutoff energy on compact regions

Source: v13 `eq:log_cutoff_l2_bound` and `eq:weak_pde_cutoff_bound`,
component kinds C and D. Compact continuity and positive definiteness
bound the actual density-weighted inverse coefficients before the cutoff
radius is chosen. The constructed coordinate cutoff has genuinely
integrable positive h-energy, dominated by its established coordinate
derivative energy, and that h-energy tends to zero. General nodal charts,
normal h-distance and tubular volume geometry are separate bridges.
-/

@[expose] public section
noncomputable section

namespace FoliationQM.AuxiliaryCutoffEnergy

open Filter MeasureTheory Set LorentzMatrixGroup AuxiliaryMetricEnergy
open SmoothCoordinateTubeCutoff RNCCoordinateConnection
open scoped Topology Matrix.Norms.Operator

/-- The actual positive volume density times inverse-metric energy of the constructed real cutoff differential. -/
def energy (H : Covector → Mat4) (ε : ℝ) (x : Covector) : ℝ :=
  density (H x) * realEnergy (H x) (fun i => fderiv ℝ (profile ε) x (axis i))

private theorem coefficient_continuousOn {K : Set Covector} {H : Covector → Mat4}
    (hH : ContinuousOn H K) (hpos : ∀ x ∈ K, (H x).PosDef) (i j : Fin 4) :
    ContinuousOn (fun x => density (H x) * (H x)⁻¹ i j) K := by
  have hd : ContinuousOn (fun x => density (H x)) K := by
    have hc : Continuous (fun A : Mat4 => density A) :=
      Real.continuous_sqrt.comp continuous_id.matrix_det
    exact hc.comp_continuousOn hH
  have hi : ContinuousOn (fun x => (H x)⁻¹) K := by
    intro x hx
    exact (LorentzCayleySmooth.contDiffAt_inverse 0 (hpos x hx).isUnit).continuousAt
      |>.comp_continuousWithinAt (hH x hx)
  exact hd.mul (continuousOn_pi.mp (continuousOn_pi.mp hi i) j)

/-- A compact region and its continuous positive metric determine one nonnegative bound for every actual density-weighted inverse coefficient. -/
theorem compact_coefficient_bounds {K : Set Covector} {H : Covector → Mat4}
    (hK : IsCompact K) (hH : ContinuousOn H K)
    (hpos : ∀ x ∈ K, (H x).PosDef) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x ∈ K, ∀ i j : Fin 4,
      ‖density (H x) * (H x)⁻¹ i j‖ ≤ B := by
  let f : Covector → (Fin 4 × Fin 4 → ℝ) :=
    fun x ij => density (H x) * (H x)⁻¹ ij.1 ij.2
  have hf : ContinuousOn f K := continuousOn_pi.mpr fun ij =>
    coefficient_continuousOn hH hpos ij.1 ij.2
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn hf
  refine ⟨max B 0, le_max_right _ _, ?_⟩
  intro x hx i j
  exact (norm_le_pi_norm (f x) (i, j)).trans ((hB x hx).trans (le_max_left _ _))

private theorem energy_eq_sum (H : Covector → Mat4) (ε : ℝ) (x : Covector) :
    energy H ε x = ∑ i : Fin 4, ∑ j : Fin 4,
      (density (H x) * (H x)⁻¹ i j) *
        fderiv ℝ (profile ε) x (axis i) * fderiv ℝ (profile ε) x (axis j) := by
  simp only [energy, realEnergy, dotProduct, Matrix.mulVec, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

private theorem energy_le {H : Covector → Mat4} {ε : ℝ} {x : Covector} {B : ℝ}
    (hB : 0 ≤ B) (hb : ∀ i j : Fin 4, ‖density (H x) * (H x)⁻¹ i j‖ ≤ B) :
    energy H ε x ≤ 16 * B * ‖fderiv ℝ (profile ε) x‖ ^ 2 := by
  have ha (i : Fin 4) : ‖fderiv ℝ (profile ε) x (axis i)‖ ≤
      ‖fderiv ℝ (profile ε) x‖ := by
    simpa [axis, Pi.norm_single] using (fderiv ℝ (profile ε) x).le_opNorm (axis i)
  rw [energy_eq_sum]
  calc
    _ ≤ ∑ i : Fin 4, ∑ j : Fin 4, B * ‖fderiv ℝ (profile ε) x‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      calc
        _ ≤ ‖(density (H x) * (H x)⁻¹ i j) *
            fderiv ℝ (profile ε) x (axis i) * fderiv ℝ (profile ε) x (axis j)‖ :=
          le_abs_self _
        _ = ‖density (H x) * (H x)⁻¹ i j‖ *
            ‖fderiv ℝ (profile ε) x (axis i)‖ *
            ‖fderiv ℝ (profile ε) x (axis j)‖ := by rw [norm_mul, norm_mul]
        _ ≤ (B * ‖fderiv ℝ (profile ε) x‖) * ‖fderiv ℝ (profile ε) x‖ :=
          mul_le_mul (mul_le_mul (hb i j) (ha i) (norm_nonneg _) hB)
            (ha j) (norm_nonneg _) (mul_nonneg hB (norm_nonneg _))
        _ = _ := by ring
    _ = _ := by simp; ring

private theorem energy_continuousOn {K : Set Covector} {H : Covector → Mat4}
    (hH : ContinuousOn H K) (hpos : ∀ x ∈ K, (H x).PosDef)
    {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1) : ContinuousOn (energy H ε) K := by
  have ha (i : Fin 4) : ContinuousOn
      (fun x => fderiv ℝ (profile ε) x (axis i)) K :=
    ((ContinuousLinearMap.apply ℝ ℝ (axis i)).continuous.comp
      ((contDiff_profile h0 h1).continuous_fderiv (by simp))).continuousOn
  have hs : ContinuousOn (fun x => ∑ i : Fin 4, ∑ j : Fin 4,
      (density (H x) * (H x)⁻¹ i j) *
        fderiv ℝ (profile ε) x (axis i) * fderiv ℝ (profile ε) x (axis j)) K :=
    continuousOn_finsetSum _ fun i _ => continuousOn_finsetSum _ fun j _ =>
      ((coefficient_continuousOn hH hpos i j).mul (ha i)).mul (ha j)
  exact hs.congr fun x _ => energy_eq_sum H ε x

/-- One metric-dependent compact bound, chosen before the radius, gives genuine integrability and bounds the actual nonnegative h-cutoff energy by the proved coordinate derivative energy. -/
theorem compact_energy_data {K : Set Covector} {H : Covector → Mat4}
    (hK : IsCompact K) (hH : ContinuousOn H K)
    (hpos : ∀ x ∈ K, (H x).PosDef) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ {ε : ℝ}, 0 < ε → ε < 1 →
      IntegrableOn (energy H ε) K volume ∧
      0 ≤ (∫ x in K, energy H ε x) ∧
      (∫ x in K, energy H ε x) ≤ B *
        (∫ x in K, ‖fderiv ℝ (profile ε) x‖ ^ 2) := by
  obtain ⟨B, hB, hb⟩ := compact_coefficient_bounds hK hH hpos
  refine ⟨16 * B, mul_nonneg (by norm_num) hB, ?_⟩
  intro ε h0 h1
  have hi : IntegrableOn (energy H ε) K volume :=
    (energy_continuousOn hH hpos h0 h1).integrableOn_compact hK
  have hd := (CoordinateCutoffCompactEnergy.compact_derivative_data K hK h0 h1).2.1
  refine ⟨hi, integral_nonneg_of_ae ?_, ?_⟩
  · apply ae_restrict_of_forall_mem hK.measurableSet
    intro x hx
    exact mul_nonneg (density_pos (hpos x hx)).le (realEnergy_nonneg (hpos x hx) _)
  · calc
      _ ≤ ∫ x in K, (16 * B) * ‖fderiv ℝ (profile ε) x‖ ^ 2 := by
        apply integral_mono_ae hi (hd.const_mul (16 * B))
        exact ae_restrict_of_forall_mem hK.measurableSet fun x hx => energy_le hB (hb x hx)
      _ = _ := integral_const_mul _ _

/-- On every fixed compact comparison region the actual positive h-cutoff energy and its square-root energy norm both vanish through positive cutoff radii. -/
theorem compact_energy_decay {K : Set Covector} {H : Covector → Mat4}
    (hK : IsCompact K) (hH : ContinuousOn H K)
    (hpos : ∀ x ∈ K, (H x).PosDef) :
    Tendsto (fun ε : ℝ => ∫ x in K, energy H ε x) (𝓝[>] 0) (𝓝 0) ∧
    Tendsto (fun ε : ℝ => Real.sqrt (∫ x in K, energy H ε x)) (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨B, _, hb⟩ := compact_energy_data hK hH hpos
  have hlim := (CoordinateCutoffCompactEnergy.compact_derivative_decay K hK).1.const_mul B
  simp only [mul_zero] at hlim
  have he : Tendsto (fun ε : ℝ => ∫ x in K, energy H ε x) (𝓝[>] 0) (𝓝 0) := by
    apply squeeze_zero' ?_ ?_ hlim
    · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with ε hε
      exact (hb hε.1 hε.2).2.1
    · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with ε hε
      exact (hb hε.1 hε.2).2.2
  refine ⟨he, ?_⟩
  simpa only [Function.comp_def, Real.sqrt_zero] using
    Real.continuous_sqrt.continuousAt.tendsto.comp he

end FoliationQM.AuxiliaryCutoffEnergy
