module

public import FoliationQM.AuxiliaryCutoffEnergy
public import FoliationQM.WeightedPolarEnergyL2
public import FoliationQM.CoordinateCutoffKineticError

/-!
# Positive-metric energy on the actual cutoff derivative support

Source: v13 `eq:weak_pde_cutoff_bound`, component kinds C and D.
The original sixteen-term metric error is estimated using genuine positive
auxiliary-metric energies. The field energy is restricted to the intersection
of the test support and the actual cutoff derivative support. Integrability
away from the coordinate axis suffices; no field L² or metric symmetry is
assumed. General nodal geometry and its distance cutoff remain separate.
-/

@[expose] public section
noncomputable section

namespace FoliationQM.WeightedCutoffKineticError

open Filter MeasureTheory Set LorentzMatrixGroup RNCCoordinateConnection
open AuxiliaryMetricEnergy CompactAuxiliaryMetricEnergy SmoothCoordinateTubeCutoff
open CoordinateCutoffKineticError CurvedWaveDivergence ProductTubeCoordinates
open scoped Topology ContDiff Matrix.Norms.Operator

private theorem derivative_support_off_axis {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1) :
    tsupport (fderiv ℝ (profile ε)) ⊆
      {x : Covector | ¬ (x 2 = 0 ∧ x 3 = 0)} := by
  have hr : Continuous (fun x : Covector => ‖(coordinates x).snd‖) :=
    ((WithLp.sndL 2 ℝ ℂ ℂ).continuous.comp coordinates.continuous).norm
  have hp : Function.support (profile ε) ⊆ {x | ε ^ 2 ≤ ‖(coordinates x).snd‖} := by
    intro x hx
    by_contra hn
    exact hx ((profile_spec h0 h1).1 x (le_of_lt (lt_of_not_ge hn)))
  have ht : tsupport (profile ε) ⊆ {x | ε ^ 2 ≤ ‖(coordinates x).snd‖} :=
    closure_minimal hp (isClosed_le continuous_const hr)
  intro x hx ha
  have hz : (coordinates x).snd = 0 :=
    show x ∈ coordinates ⁻¹' {y : WithLp 2 (ℂ × ℂ) | y.snd = 0} from
      axis_preimage.symm ▸ ha
  have hb := ht (tsupport_fderiv_subset ℝ hx)
  change ε ^ 2 ≤ ‖(coordinates x).snd‖ at hb
  rw [hz, norm_zero] at hb
  exact (not_le_of_gt (sq_pos_of_pos h0)) hb

private theorem error_zero_outside {ε : ℝ} {g : Covector → Mat4}
    {φ ψ : Covector → ℂ} {x : Covector}
    (hx : x ∉ tsupport φ ∩ tsupport (fderiv ℝ (profile ε))) :
    error ε g φ ψ x = 0 := by
  by_cases hφ : x ∈ tsupport φ
  · have hd : fderiv ℝ (profile ε) x = 0 :=
      image_eq_zero_of_notMem_tsupport (fun hd => hx ⟨hφ, hd⟩)
    simp [error, hd]
  · simp [error, image_eq_zero_of_notMem_tsupport hφ]

private theorem sqrt_energy_bound {μ : Measure Covector} {F : Type*}
    [NormedAddCommGroup F] {f : Covector → F} {e : Covector → ℝ} {C : ℝ}
    (hf : MemLp f 2 μ) (he : Integrable e μ) (hC : 0 ≤ C)
    (hb : ∀ᵐ x ∂μ, ‖f x‖ ^ 2 ≤ C * e x) :
    Real.sqrt (∫ x, ‖f x‖ ^ 2 ∂μ) ≤ Real.sqrt C * Real.sqrt (∫ x, e x ∂μ) := by
  have hsq := (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).1 hf
  have hi := integral_mono_ae hsq (he.const_mul C) hb
  rw [integral_const_mul] at hi
  exact (Real.sqrt_le_sqrt hi).trans_eq (Real.sqrt_mul hC _)

private theorem term_data {S : Set Covector} (hS : MeasurableSet S)
    {b a : Covector → ℝ} {φ z : Covector → ℂ} {B A : ℝ}
    (hb : MemLp b ⊤ (volume.restrict S)) (ha : MemLp a 2 (volume.restrict S))
    (hφ : MemLp φ ⊤ (volume.restrict S)) (hz : MemLp z 2 (volume.restrict S))
    (hB : 0 ≤ B) (hA : 0 ≤ A)
    (hbb : ∀ x ∈ S, ‖b x‖ ≤ B) (hAb : ∀ x ∈ S, ‖φ x‖ ≤ A) :
    IntegrableOn (fun x => (b x * a x) • (star (φ x) * z x)) S volume ∧
    (∫ x in S, ‖(b x * a x) • (star (φ x) * z x)‖) ≤
      B * A * Real.sqrt (∫ x in S, ‖a x‖ ^ 2) *
        Real.sqrt (∫ x in S, ‖z x‖ ^ 2) := by
  have hba : MemLp (fun x => b x * a x) 2 (volume.restrict S) := hb.mul ha
  have hφz : MemLp (fun x => star (φ x) * z x) 2 (volume.restrict S) := hφ.star.mul hz
  have hi : IntegrableOn (fun x => (b x * a x) • (star (φ x) * z x)) S volume :=
    memLp_one_iff_integrable.1 (hba.smul hφz)
  have hm := ha.norm.integrable_mul hz.norm
  have hh := integral_mul_norm_le_Lp_mul_Lq (μ := volume.restrict S)
    Real.HolderConjugate.two_two
    (show MemLp (fun x => ‖a x‖) (ENNReal.ofReal 2) (volume.restrict S) by simpa using ha.norm)
    (show MemLp (fun x => ‖z x‖) (ENNReal.ofReal 2) (volume.restrict S) by simpa using hz.norm)
  have hholder : (∫ x in S, ‖a x‖ * ‖z x‖) ≤
      Real.sqrt (∫ x in S, ‖a x‖ ^ 2) * Real.sqrt (∫ x in S, ‖z x‖ ^ 2) := by
    simpa only [norm_norm, Real.rpow_two, ← Real.sqrt_eq_rpow] using hh
  refine ⟨hi, ?_⟩
  calc
    _ ≤ ∫ x in S, (B * A) * (‖a x‖ * ‖z x‖) := by
      apply integral_mono_ae hi.norm (hm.const_mul (B * A))
      apply ae_restrict_of_forall_mem hS
      intro x hx
      dsimp only
      rw [norm_smul, norm_mul, norm_mul, norm_star]
      calc
        _ ≤ (B * ‖a x‖) * (A * ‖z x‖) :=
          mul_le_mul (mul_le_mul_of_nonneg_right (hbb x hx) (norm_nonneg _))
            (mul_le_mul_of_nonneg_right (hAb x hx) (norm_nonneg _))
            (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (mul_nonneg hB (norm_nonneg _))
        _ = _ := by dsimp only [Pi.mul_apply]; ring
    _ = (B * A) * (∫ x in S, ‖a x‖ * ‖z x‖) := integral_const_mul _ _
    _ ≤ (B * A) * (Real.sqrt (∫ x in S, ‖a x‖ ^ 2) *
        Real.sqrt (∫ x in S, ‖z x‖ ^ 2)) :=
      mul_le_mul_of_nonneg_left hholder (mul_nonneg hB hA)
    _ = _ := by ring

/-- Compact metric data determine the constant before the test and field; the actual metric error is integrable and bounded by positive energies localized to the actual derivative support. -/
theorem weighted_error_data {K : Set Covector} {H g : Covector → Mat4}
    (hK : IsCompact K) (hH : ContinuousOn H K) (hpos : ∀ x ∈ K, (H x).PosDef)
    (hg : ∀ x ∈ K, ContDiffAt ℝ 1 g x) (hd : ∀ x ∈ K, (g x).det < 0) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (φ ψ : Covector → ℂ) (A : ℝ),
      Continuous φ → tsupport φ ⊆ K → 0 ≤ A → (∀ x ∈ tsupport φ, ‖φ x‖ ≤ A) →
      IntegrableOn (fun x => density (H x) *
        complexEnergy (H x) (fun i => fderiv ℝ ψ x (axis i)))
        (K \ {x : Covector | x 2 = 0 ∧ x 3 = 0}) volume →
      ∀ {ε : ℝ}, 0 < ε → ε < 1 →
        let S := tsupport φ ∩ tsupport (fderiv ℝ (profile ε))
        IsCompact S ∧ S ⊆ K \ {x : Covector | x 2 = 0 ∧ x 3 = 0} ∧
        IntegrableOn (fun x => density (H x) *
          complexEnergy (H x) (fun i => fderiv ℝ ψ x (axis i))) S volume ∧
        IntegrableOn (AuxiliaryCutoffEnergy.energy H ε) (tsupport φ) volume ∧
        Integrable (error ε g φ ψ) volume ∧ Integrable (fun x => ‖error ε g φ ψ x‖) volume ∧
        ‖∫ x, error ε g φ ψ x‖ ≤ ∫ x, ‖error ε g φ ψ x‖ ∧
        (∫ x, ‖error ε g φ ψ x‖) ≤ M * A *
          Real.sqrt (∫ x in S, density (H x) *
            complexEnergy (H x) (fun i => fderiv ℝ ψ x (axis i))) *
          Real.sqrt (∫ x in tsupport φ, AuxiliaryCutoffEnergy.energy H ε x) := by
  obtain ⟨Ch, hCh, hcmp⟩ := compact_energy_comparison hK hH hpos
  obtain ⟨Bg, hBg, hcoeff⟩ := CoordinateMetricFluxL2.coefficient_data hK Subset.rfl hg hd
  refine ⟨16 * Bg * Ch, by positivity, ?_⟩
  intro φ ψ A hφ hs hA hAb hE ε h0 h1
  let C := tsupport φ
  let S := C ∩ tsupport (fderiv ℝ (profile ε))
  let E : Covector → ℝ := fun x => density (H x) *
    complexEnergy (H x) (fun i => fderiv ℝ ψ x (axis i))
  have hC : IsCompact C := hK.of_isClosed_subset (isClosed_tsupport _) hs
  have hS : IsCompact S := hC.inter_right (isClosed_tsupport _)
  have hSC : S ⊆ C := inter_subset_left
  have hSK : S ⊆ K := hSC.trans hs
  have hSN : S ⊆ K \ {x : Covector | x 2 = 0 ∧ x 3 = 0} := by
    intro x hx
    exact ⟨hSK hx, derivative_support_off_axis h0 h1 hx.2⟩
  have hN : IsClosed {x : Covector | x 2 = 0 ∧ x 3 = 0} :=
    (isClosed_eq (continuous_apply 2) continuous_const).inter
      (isClosed_eq (continuous_apply 3) continuous_const)
  have hKN : MeasurableSet (K \ {x : Covector | x 2 = 0 ∧ x 3 = 0}) :=
    hK.measurableSet.diff hN.measurableSet
  have hEL : IntegrableOn E S volume := hE.mono_set hSN
  have hZ0 := (WeightedPolarEnergyL2.memLp_of_weighted_energy hK hKN sdiff_subset
    hH hpos (ψ := fun _ => (0 : ℂ)) (z := fun x i => fderiv ℝ ψ x (axis i))
    aestronglyMeasurable_const
    (fun i => (measurable_fderiv_apply_const ℝ ψ (axis i)).aestronglyMeasurable)
    (by simpa only [norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_add] using! hE)).2
  have hZ (i : Fin 4) : MemLp (fun x => fderiv ℝ ψ x (axis i)) 2 (volume.restrict S) :=
    MemLp.mono_measure (Measure.restrict_mono_set volume hSN) (hZ0 i)
  have hD := (CoordinateCutoffCompactEnergy.compact_derivative_data C hC h0 h1).1
  have ha (i : Fin 4) : MemLp (fun x => fderiv ℝ (profile ε) x (axis i)) 2
      (volume.restrict S) :=
    MemLp.mono_measure (Measure.restrict_mono_set volume hSC)
      ((ContinuousLinearMap.apply ℝ ℝ (axis i)).comp_memLp' hD)
  have hb (i j : Fin 4) : MemLp (fun x => coefficient g x i j) ⊤ (volume.restrict S) :=
    MemLp.mono_measure (Measure.restrict_mono_set volume hSK) (hcoeff i j).2
  have hφtop : MemLp φ ⊤ (volume.restrict S) :=
    memLp_top_of_bound hφ.aestronglyMeasurable A
      (ae_restrict_of_forall_mem hS.measurableSet (fun x hx => hAb x hx.1))
  obtain ⟨_, _, hecut⟩ := AuxiliaryCutoffEnergy.compact_energy_data hK hH hpos
  have hcutK := (hecut h0 h1).1
  have hcutC := hcutK.mono_set hs
  have hcutS := hcutK.mono_set hSK
  have hcutroot (i : Fin 4) :
      Real.sqrt (∫ x in S, ‖fderiv ℝ (profile ε) x (axis i)‖ ^ 2) ≤
        Real.sqrt Ch * Real.sqrt (∫ x in S, AuxiliaryCutoffEnergy.energy H ε x) := by
    apply sqrt_energy_bound (ha i) hcutS hCh.le
    apply ae_restrict_of_forall_mem hS.measurableSet
    intro x hx
    simpa only [Real.norm_eq_abs, sq_abs, AuxiliaryCutoffEnergy.energy] using
      (hcmp x (hSK hx)).2.1 (fun j => fderiv ℝ (profile ε) x (axis j)) i
  have hfieldroot (i : Fin 4) :
      Real.sqrt (∫ x in S, ‖fderiv ℝ ψ x (axis i)‖ ^ 2) ≤
        Real.sqrt Ch * Real.sqrt (∫ x in S, E x) := by
    apply sqrt_energy_bound (hZ i) hEL hCh.le
    exact ae_restrict_of_forall_mem hS.measurableSet fun x hx =>
      (hcmp x (hSK hx)).2.2 (fun j => fderiv ℝ ψ x (axis j)) i
  let term (μ ν : Fin 4) (x : Covector) : ℂ :=
    (coefficient g x μ ν * fderiv ℝ (profile ε) x (axis ν)) •
      (star (φ x) * fderiv ℝ ψ x (axis μ))
  have ht (μ ν : Fin 4) := term_data hS.measurableSet (hb μ ν) (ha ν) hφtop (hZ μ)
    hBg hA (fun x hx => (hcoeff μ ν).1 x (hSK hx)) (fun x hx => hAb x hx.1)
  have hti (μ ν : Fin 4) : IntegrableOn (term μ ν) S volume := (ht μ ν).1
  have heq (x) : error ε g φ ψ x = ∑ μ, ∑ ν, term μ ν x := rfl
  have hi : IntegrableOn (error ε g φ ψ) S volume := by
    change Integrable (fun x => ∑ μ, ∑ ν, term μ ν x) (volume.restrict S)
    exact integrable_finsetSum Finset.univ fun μ _ =>
      integrable_finsetSum Finset.univ fun ν _ => hti μ ν
  have hia := hi.integrable_of_forall_notMem_eq_zero fun x hx => error_zero_outside hx
  have hsum (μ) := integrable_finsetSum Finset.univ fun ν _ => (hti μ ν).norm
  have htb (μ ν : Fin 4) : (∫ x in S, ‖term μ ν x‖) ≤
      Bg * A * Ch * Real.sqrt (∫ x in S, E x) *
        Real.sqrt (∫ x in S, AuxiliaryCutoffEnergy.energy H ε x) := by
    calc
      _ ≤ Bg * A * Real.sqrt (∫ x in S, ‖fderiv ℝ (profile ε) x (axis ν)‖ ^ 2) *
          Real.sqrt (∫ x in S, ‖fderiv ℝ ψ x (axis μ)‖ ^ 2) := (ht μ ν).2
      _ ≤ Bg * A * (Real.sqrt Ch * Real.sqrt (∫ x in S, AuxiliaryCutoffEnergy.energy H ε x)) *
          (Real.sqrt Ch * Real.sqrt (∫ x in S, E x)) := by
        gcongr
        · exact hcutroot ν
        · exact hfieldroot μ
      _ = (Bg * A) * (Real.sqrt Ch * Real.sqrt Ch) *
          (Real.sqrt (∫ x in S, E x) *
            Real.sqrt (∫ x in S, AuxiliaryCutoffEnergy.energy H ε x)) := by ring
      _ = _ := by rw [Real.mul_self_sqrt hCh.le]; ring
  have hcutmono : (∫ x in S, AuxiliaryCutoffEnergy.energy H ε x) ≤
      ∫ x in C, AuxiliaryCutoffEnergy.energy H ε x := by
    apply setIntegral_mono_set hcutC _ hSC.eventuallySubset
    exact ae_restrict_of_forall_mem hC.measurableSet fun x hx =>
      mul_nonneg (Real.sqrt_nonneg _) (realEnergy_nonneg (hpos x (hs hx)) _)
  refine ⟨hS, hSN, hEL, hcutC, hia, hia.norm, norm_integral_le_integral_norm _, ?_⟩
  calc
    _ = ∫ x in S, ‖error ε g φ ψ x‖ :=
      (setIntegral_eq_integral_of_forall_compl_eq_zero
        (fun x hx => by rw [error_zero_outside hx, norm_zero])).symm
    _ ≤ ∫ x in S, ∑ μ, ∑ ν, ‖term μ ν x‖ := by
      apply integral_mono hi.norm (integrable_finsetSum Finset.univ fun μ _ => hsum μ)
      intro x
      dsimp only
      rw [heq]
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun μ _ => norm_sum_le _ _)
    _ = ∑ μ, ∑ ν, ∫ x in S, ‖term μ ν x‖ := by
      rw [integral_finsetSum Finset.univ (fun μ _ => hsum μ)]
      exact Finset.sum_congr rfl fun μ _ => integral_finsetSum Finset.univ fun ν _ => (hti μ ν).norm
    _ ≤ ∑ _μ : Fin 4, ∑ _ν : Fin 4, Bg * A * Ch * Real.sqrt (∫ x in S, E x) *
        Real.sqrt (∫ x in S, AuxiliaryCutoffEnergy.energy H ε x) :=
      Finset.sum_le_sum fun μ _ => Finset.sum_le_sum fun ν _ => htb μ ν
    _ = (16 * Bg * Ch) * A * Real.sqrt (∫ x in S, E x) *
        Real.sqrt (∫ x in S, AuxiliaryCutoffEnergy.energy H ε x) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring
    _ ≤ _ := by gcongr

/-- For fixed finite positive derivative energy away from the axis, the actual metric error and its norm integral tend to zero through positive cutoff radii; no field L² premise is needed. -/
theorem weighted_error_limits {K : Set Covector} {H g : Covector → Mat4}
    (hK : IsCompact K) (hH : ContinuousOn H K) (hpos : ∀ x ∈ K, (H x).PosDef)
    (hg : ∀ x ∈ K, ContDiffAt ℝ 1 g x) (hd : ∀ x ∈ K, (g x).det < 0)
    {φ ψ : Covector → ℂ} (hφ : Continuous φ) (hs : tsupport φ ⊆ K)
    (hE : IntegrableOn (fun x => density (H x) *
      complexEnergy (H x) (fun i => fderiv ℝ ψ x (axis i)))
      (K \ {x : Covector | x 2 = 0 ∧ x 3 = 0}) volume) :
    Tendsto (fun ε : ℝ => ∫ x, ‖error ε g φ ψ x‖) (𝓝[>] 0) (𝓝 0) ∧
    Tendsto (fun ε : ℝ => ∫ x, error ε g φ ψ x) (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨M, hM, hb⟩ := weighted_error_data hK hH hpos hg hd
  obtain ⟨A0, hA0⟩ := hK.exists_bound_of_continuousOn hφ.continuousOn
  let A := max A0 0
  have hA : 0 ≤ A := le_max_right _ _
  have hAb : ∀ x ∈ tsupport φ, ‖φ x‖ ≤ A := fun x hx =>
    (hA0 x (hs hx)).trans (le_max_left _ _)
  let E : Covector → ℝ := fun x => density (H x) *
    complexEnergy (H x) (fun i => fderiv ℝ ψ x (axis i))
  let T := K \ {x : Covector | x 2 = 0 ∧ x 3 = 0}
  have hT : MeasurableSet T := hK.measurableSet.diff
    ((isClosed_eq (continuous_apply 2) continuous_const).inter
      (isClosed_eq (continuous_apply 3) continuous_const)).measurableSet
  have hEn : 0 ≤ᵐ[volume.restrict T] E :=
    ae_restrict_of_forall_mem hT fun x hx =>
      mul_nonneg (Real.sqrt_nonneg _) (complexEnergy_nonneg (hpos x hx.1) _)
  obtain ⟨_, _, hcut⟩ := AuxiliaryCutoffEnergy.compact_energy_data hK hH hpos
  have hlim := ((AuxiliaryCutoffEnergy.compact_energy_decay hK hH hpos).2.const_mul
    (M * A * Real.sqrt (∫ x in T, E x)))
  have hnorm : Tendsto (fun ε : ℝ => ∫ x, ‖error ε g φ ψ x‖) (𝓝[>] 0) (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall fun _ => integral_nonneg fun _ => norm_nonneg _) ?_
      (by simpa only [mul_zero] using hlim)
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with ε hε
    obtain ⟨_, hST, _, _, _, _, _, hbound⟩ := hb φ ψ A hφ hs hA hAb hE hε.1 hε.2
    have hfield : (∫ x in tsupport φ ∩ tsupport (fderiv ℝ (profile ε)), E x) ≤
        ∫ x in T, E x := setIntegral_mono_set hE hEn hST.eventuallySubset
    have hcutmono : (∫ x in tsupport φ, AuxiliaryCutoffEnergy.energy H ε x) ≤
        ∫ x in K, AuxiliaryCutoffEnergy.energy H ε x := by
      apply setIntegral_mono_set (hcut hε.1 hε.2).1 _ hs.eventuallySubset
      exact ae_restrict_of_forall_mem hK.measurableSet fun x hx =>
        mul_nonneg (Real.sqrt_nonneg _) (realEnergy_nonneg (hpos x hx) _)
    exact hbound.trans (by gcongr)
  exact ⟨hnorm, squeeze_zero_norm' (Eventually.of_forall fun ε => norm_integral_le_integral_norm _) hnorm⟩

end FoliationQM.WeightedCutoffKineticError
