module

public import FoliationQM.SmoothProductTubeCutoff
public import FoliationQM.SmoothNormalPlaneCutoffEnergy
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Function.L2Space

/-!
# Localized energy of the actual four-dimensional product-tube cutoff

Source: v13 `eq:log_cutoff_l2_bound` and the null-axis clause accompanying
`eq:log_cutoff_wallstrom`, component kinds C and D. Actual Hilbert volume
transport and genuine product integrability give the finite-tangential-region
energy and restricted derivative L² norm. The full flat axis is null. General
submanifold geometry and auxiliary-metric comparisons remain separate.
-/

@[expose] public section
noncomputable section

namespace FoliationQM.SmoothProductTubeCutoffEnergy

open Filter MeasureTheory Set
open scoped Topology ContDiff
open SmoothProductTubeCutoff

local notation "Space" => WithLp 2 (ℂ × ℂ)

/-- The part of the Hilbert product whose tangential coordinate belongs to the supplied region; the normal coordinate is unrestricted. -/
def tube (K : Set ℂ) : Set Space := {x | x.fst ∈ K}

/-- The entire flat codimension-two axis has zero actual four-dimensional Hilbert volume, including its unbounded tangential direction. -/
theorem axis_null : volume {x : Space | x.snd = 0} = 0 := by
  let e := (MeasurableEquiv.toLp 2 (ℂ × ℂ)).symm
  have hm : MeasurePreserving e :=
    WithLp.volume_preserving_symm_measurableEquiv_toLp_prod ℂ ℂ
  have hs : {x : Space | x.snd = 0} = e ⁻¹' (univ ×ˢ {(0 : ℂ)}) := by
    ext x
    simp [e]
  rw [hs, hm.measure_preimage_emb e.measurableEmbedding, Measure.volume_eq_prod,
    Measure.prod_prod]
  simp

/-- Finite tangential volume gives genuine tube-energy integrability and exact products with both the plane energy and its twice-pi radial integral. -/
theorem energy_integral (K : Set ℂ) (hK : volume K ≠ ⊤)
    {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1) :
    IntegrableOn (fun x : Space => ‖fderiv ℝ (profile ε) x‖ ^ 2) (tube K) volume ∧
    (∫ x in tube K, ‖fderiv ℝ (profile ε) x‖ ^ 2) =
      volume.real K * (∫ z : ℂ, ‖fderiv ℝ (SmoothNormalPlaneCutoff.profile ε) z‖ ^ 2) ∧
    (∫ x in tube K, ‖fderiv ℝ (profile ε) x‖ ^ 2) =
      volume.real K * (2 * Real.pi * ∫ r in (ε ^ 2)..ε,
        r * (deriv (SmoothLogarithmicCutoffProfile.profile ε) r) ^ 2) := by
  let e := (MeasurableEquiv.toLp 2 (ℂ × ℂ)).symm
  let G : ℂ → ℝ := fun z => ‖fderiv ℝ (SmoothNormalPlaneCutoff.profile ε) z‖ ^ 2
  let H : ℂ × ℂ → ℝ := fun z => G z.2
  have hm : MeasurePreserving e :=
    WithLp.volume_preserving_symm_measurableEquiv_toLp_prod ℂ ℂ
  have ht : tube K = e ⁻¹' (K ×ˢ univ) := by
    ext x
    simp [tube, e]
  have hf : (fun x : Space => ‖fderiv ℝ (profile ε) x‖ ^ 2) = H ∘ e := by
    funext x
    simp only [H, G, Function.comp_apply, e, MeasurableEquiv.toLp_symm_apply,
      WithLp.ofLp_snd, norm_fderiv_profile h0 h1]
  have hi : Integrable G volume := (SmoothNormalPlaneCutoffEnergy.energy_integral h0 h1).1
  have hk : IntegrableOn (fun _ : ℂ => (1 : ℝ)) K volume := integrableOn_const hK
  have hp : IntegrableOn H (K ×ˢ univ) (volume.prod volume) := by
    simpa only [H, IntegrableOn, Measure.prod_restrict, one_mul] using
      hk.mul_prod (hi.restrict (s := univ))
  have hprod : IntegrableOn H (K ×ˢ univ) volume := hp
  have heq : (∫ x in tube K, ‖fderiv ℝ (profile ε) x‖ ^ 2) =
      volume.real K * ∫ z : ℂ, G z := by
    rw [hf, ht]
    calc
      _ = ∫ z in K ×ˢ univ, H z :=
        (hm.restrict_preimage_emb e.measurableEmbedding (K ×ˢ univ)).integral_comp
          e.measurableEmbedding H
      _ = ∫ _ in K, ∫ z : ℂ, G z := by
        simpa only [H, setIntegral_univ, Measure.volume_eq_prod] using setIntegral_prod H hp
      _ = _ := by rw [setIntegral_const, smul_eq_mul]
  refine ⟨?_, heq, ?_⟩
  · rw [hf, ht]
    exact (hm.integrableOn_comp_preimage e.measurableEmbedding).2 hprod
  · rw [heq]
    exact congrArg (volume.real K * ·) (SmoothNormalPlaneCutoffEnergy.energy_integral h0 h1).2

/-- The actual derivative belongs to L² for restricted tube volume, and its finite standard seminorm equals the square root of the genuine tube energy. -/
theorem derivative_l2_data (K : Set ℂ) (hK : volume K ≠ ⊤)
    {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1) :
    MemLp (fderiv ℝ (profile ε)) 2 (volume.restrict (tube K)) ∧
    (eLpNorm (fderiv ℝ (profile ε)) 2 (volume.restrict (tube K))).toReal =
      Real.sqrt (∫ x in tube K, ‖fderiv ℝ (profile ε) x‖ ^ 2) := by
  have hc : Continuous (fderiv ℝ (profile ε)) :=
    (contDiff_profile h0 h1).continuous_fderiv (by simp)
  have hlp : MemLp (fderiv ℝ (profile ε)) 2 (volume.restrict (tube K)) :=
    (memLp_two_iff_integrable_sq_norm hc.aestronglyMeasurable).2
      (energy_integral K hK h0 h1).1
  refine ⟨hlp, ?_⟩
  have hn : eLpNorm (fderiv ℝ (profile ε)) 2 (volume.restrict (tube K)) =
      ENNReal.ofReal (Real.sqrt (∫ x in tube K, ‖fderiv ℝ (profile ε) x‖ ^ 2)) := by
    simpa [Real.sqrt_eq_rpow, one_div] using
      MemLp.eLpNorm_eq_integral_rpow_norm (p := 2) (by norm_num) (by norm_num) hlp
  rw [hn, ENNReal.toReal_ofReal (Real.sqrt_nonneg _)]

/-- One constant independent of the tangential region and radius bounds every finite-region tube energy by its actual tangential volume times the logarithmic plane bound. -/
theorem exists_energy_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ K : Set ℂ, volume K ≠ ⊤ → ∀ ε : ℝ, 0 < ε → ε < 1 →
      0 ≤ (∫ x in tube K, ‖fderiv ℝ (profile ε) x‖ ^ 2) ∧
      (∫ x in tube K, ‖fderiv ℝ (profile ε) x‖ ^ 2) ≤
        volume.real K * (2 * Real.pi * C ^ 2 / |Real.log ε|) := by
  obtain ⟨C, hC, hb⟩ := SmoothNormalPlaneCutoffEnergy.exists_energy_bound
  refine ⟨C, hC, fun K hK ε h0 h1 => ⟨integral_nonneg (fun _ => sq_nonneg _), ?_⟩⟩
  rw [(energy_integral K hK h0 h1).2.1]
  exact mul_le_mul_of_nonneg_left (hb ε h0 h1).2 ENNReal.toReal_nonneg

/-- On each fixed finite-volume tangential region, the actual tube energy and finite restricted derivative L² seminorm tend to zero through positive cutoff radii. -/
theorem tendsto_energy_and_l2_norm (K : Set ℂ) (hK : volume K ≠ ⊤) :
    Tendsto (fun ε : ℝ => ∫ x in tube K, ‖fderiv ℝ (profile ε) x‖ ^ 2)
      (𝓝[>] 0) (𝓝 0) ∧
    Tendsto (fun ε : ℝ =>
      (eLpNorm (fderiv ℝ (profile ε)) 2 (volume.restrict (tube K))).toReal)
      (𝓝[>] 0) (𝓝 0) := by
  have hplane := SmoothNormalPlaneCutoffEnergy.tendsto_energy_and_l2_norm.1
  have hmul := hplane.const_mul (volume.real K)
  have he : Tendsto (fun ε : ℝ => ∫ x in tube K, ‖fderiv ℝ (profile ε) x‖ ^ 2)
      (𝓝[>] 0) (𝓝 0) := by
    apply (show Tendsto (fun ε : ℝ => volume.real K *
      (∫ z : ℂ, ‖fderiv ℝ (SmoothNormalPlaneCutoff.profile ε) z‖ ^ 2))
      (𝓝[>] 0) (𝓝 0) from by simpa only [mul_zero] using hmul).congr'
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with ε hε
    exact (energy_integral K hK hε.1 hε.2).2.1.symm
  refine ⟨he, ?_⟩
  have hs := Real.continuous_sqrt.continuousAt.tendsto.comp he
  have hs0 : Tendsto (fun ε : ℝ => Real.sqrt
      (∫ x in tube K, ‖fderiv ℝ (profile ε) x‖ ^ 2)) (𝓝[>] 0) (𝓝 0) := by
    simpa only [Function.comp_def, Real.sqrt_zero] using hs
  apply hs0.congr'
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with ε hε
  exact (derivative_l2_data K hK hε.1 hε.2).2.symm

end FoliationQM.SmoothProductTubeCutoffEnergy
