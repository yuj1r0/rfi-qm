module

public import FoliationQM.DistanceCutoffEnergy
public import FoliationQM.CompactAuxiliaryMetricEnergy
public import FoliationQM.CoordinateMetricFluxL2
public import FoliationQM.LorentzCayleySmooth
public import Mathlib.MeasureTheory.Integral.MeanInequalities
public import Mathlib.Analysis.Calculus.FDeriv.Measurable

/-!
# The cutoff error of the weak equation for a distance cutoff

Source: v13 `eq:weak_pde_cutoff_bound`,

`|∫ g^{μν} (∂_μψ) φ (∂_νχ_ε) √(-g) d⁴x| ≤
   C ‖φ‖_{L^∞} ‖dψ‖_{L²(h; supp dχ_ε)} ‖dχ_ε‖_{L²(h)} → 0`,

component kinds C and D. On a compact coordinate set `K` with a continuously
differentiable Lorentzian metric `g` and a continuous positive-definite
auxiliary metric `h`, there is a constant `M` such that for every real
function `χ`, bounded `φ` and field `ψ`

`∫_K |Σ g^{μν} √(-g) ∂_νχ φ̄ ∂_μψ| ≤
   M sup|φ| (∫_{K ∩ {dχ ≠ 0}} |dψ|²_h dvol_h)^{1/2} (∫_K |dχ|²_h dvol_h)^{1/2}`.

For the logarithmic cutoff `χ_ε ∘ r` of a distance function `r` to a locally
flat nodal set, and a field of finite `h`-energy on `K`, the left side tends
to zero with `ε`, and so does the integral of the error itself.

The integrals on the right are lower Lebesgue integrals. The cutoff is the
Lipschitz one of `eq:log_cutoff_wallstrom`, not a smoothed one, so the error
is paired with a bounded `φ`; the passage from this limit to the weak equation
with smooth tests is the subject of the chart-cutoff theorems. That the
distance of a Riemannian metric is comparable to the coordinate distance is
not proved here.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.DistanceCutoffWeakError

open Filter MeasureTheory Set Metric LorentzMatrixGroup RNCVolumeDensity AuxiliaryMetricEnergy
open LogarithmicCutoffProfile LocallyFlatNodalSet RNCCoordinateConnection RealLorentzFrame
open CurvedWaveDivergence CompactAuxiliaryMetricEnergy
open scoped Topology ENNReal Matrix.Norms.Operator

/-- The metric cutoff error integrand for a real cutoff function, with the
test conjugated and the field derivative unchanged. -/
def error (χ : Covector → ℝ) (g : Covector → Mat4) (φ ψ : Covector → ℂ) (x : Covector) : ℂ :=
  ∑ μ, ∑ ν, (volumeFactor (g x) * (g x)⁻¹ μ ν *
    fderiv ℝ χ x (axis ν)) • (star (φ x) * fderiv ℝ ψ x (axis μ))

/-- The `h`-energy density of the differential of the field. -/
def fieldEnergy (H : Covector → Mat4) (ψ : Covector → ℂ) (x : Covector) : ℝ :=
  density (H x) * complexEnergy (H x) (fun i => fderiv ℝ ψ x (axis i))

/-- The `h`-energy density of the differential of the cutoff. -/
def cutoffEnergy (H : Covector → Mat4) (χ : Covector → ℝ) (x : Covector) : ℝ :=
  density (H x) * realEnergy (H x) (fun i => fderiv ℝ χ x (axis i))

variable {K : Set Covector} {H g : Covector → Mat4} {χ : Covector → ℝ} {φ ψ : Covector → ℂ}
  {x : Covector}

/-- Where the differential of the cutoff vanishes, so does the error. -/
theorem error_eq_zero (hχ : fderiv ℝ χ x = 0) : error χ g φ ψ x = 0 := by
  simp [error, hχ]

/-- The pointwise Cauchy–Schwarz bound for the error. -/
theorem norm_error_le {Bg Ch A : ℝ} (hBg : 0 ≤ Bg) (hCh : 0 ≤ Ch) (hA : 0 ≤ A)
    (hcoef : ∀ μ ν : Fin 4, ‖coefficient g x μ ν‖ ≤ Bg) (hφ : ‖φ x‖ ≤ A)
    (hre : ∀ (a : Covector) (i : Fin 4), a i ^ 2 ≤ Ch * (density (H x) * realEnergy (H x) a))
    (hce : ∀ (z : Fin 4 → ℂ) (i : Fin 4),
      ‖z i‖ ^ 2 ≤ Ch * (density (H x) * complexEnergy (H x) z)) :
    ‖error χ g φ ψ x‖ ≤ 16 * Bg * Ch * A * (√(fieldEnergy H ψ x) * √(cutoffEnergy H χ x)) := by
  have hχi (ν : Fin 4) : ‖fderiv ℝ χ x (axis ν)‖ ≤ √Ch * √(cutoffEnergy H χ x) := by
    rw [← Real.sqrt_mul hCh, Real.norm_eq_abs, ← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt (hre (fun i => fderiv ℝ χ x (axis i)) ν)
  have hψi (μ : Fin 4) : ‖fderiv ℝ ψ x (axis μ)‖ ≤ √Ch * √(fieldEnergy H ψ x) := by
    rw [← Real.sqrt_mul hCh]
    exact Real.le_sqrt_of_sq_le (hce (fun i => fderiv ℝ ψ x (axis i)) μ)
  have hterm (μ ν : Fin 4) : ‖(volumeFactor (g x) * (g x)⁻¹ μ ν *
      fderiv ℝ χ x (axis ν)) • (star (φ x) * fderiv ℝ ψ x (axis μ))‖ ≤
      Bg * Ch * A * (√(fieldEnergy H ψ x) * √(cutoffEnergy H χ x)) := by
    have h1 : ‖volumeFactor (g x) * (g x)⁻¹ μ ν‖ ≤ Bg := hcoef μ ν
    have e : ‖(volumeFactor (g x) * (g x)⁻¹ μ ν * fderiv ℝ χ x (axis ν)) •
        (star (φ x) * fderiv ℝ ψ x (axis μ))‖ =
        ‖volumeFactor (g x) * (g x)⁻¹ μ ν‖ * ‖fderiv ℝ χ x (axis ν)‖ *
          (‖φ x‖ * ‖fderiv ℝ ψ x (axis μ)‖) := by
      rw [norm_smul, norm_mul (volumeFactor (g x) * (g x)⁻¹ μ ν), norm_mul (star (φ x)),
        norm_star]
    rw [e]
    calc ‖volumeFactor (g x) * (g x)⁻¹ μ ν‖ * ‖fderiv ℝ χ x (axis ν)‖ *
          (‖φ x‖ * ‖fderiv ℝ ψ x (axis μ)‖)
        ≤ Bg * (√Ch * √(cutoffEnergy H χ x)) * (A * (√Ch * √(fieldEnergy H ψ x))) := by
          gcongr
          · exact hχi ν
          · exact hψi μ
      _ = Bg * (√Ch * √Ch) * A * (√(fieldEnergy H ψ x) * √(cutoffEnergy H χ x)) := by ring
      _ = Bg * Ch * A * (√(fieldEnergy H ψ x) * √(cutoffEnergy H χ x)) := by
          rw [Real.mul_self_sqrt hCh]
  calc ‖error χ g φ ψ x‖
      ≤ ∑ μ : Fin 4, ∑ ν : Fin 4, ‖(volumeFactor (g x) * (g x)⁻¹ μ ν *
          fderiv ℝ χ x (axis ν)) • (star (φ x) * fderiv ℝ ψ x (axis μ))‖ :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun μ _ => norm_sum_le _ _)
    _ ≤ ∑ _μ : Fin 4, ∑ _ν : Fin 4,
          Bg * Ch * A * (√(fieldEnergy H ψ x) * √(cutoffEnergy H χ x)) :=
        Finset.sum_le_sum fun μ _ => Finset.sum_le_sum fun ν _ => hterm μ ν
    _ = 16 * Bg * Ch * A * (√(fieldEnergy H ψ x) * √(cutoffEnergy H χ x)) := by
        simp
        ring

/-- The density-weighted inverse coefficients of a continuous positive-definite
metric are almost everywhere measurable on a compact set. -/
theorem aemeasurable_coefficient (hK : IsCompact K) (hH : ContinuousOn H K)
    (hpos : ∀ x ∈ K, (H x).PosDef) (i j : Fin 4) :
    AEMeasurable (fun x => density (H x) * (H x)⁻¹ i j) (volume.restrict K) := by
  have hinv : ContinuousOn (fun x => (H x)⁻¹) K := fun x hx =>
    ContinuousAt.comp_continuousWithinAt (g := fun N : Mat4 => N⁻¹)
      (LorentzCayleySmooth.contDiffAt_inverse 0
        ((Matrix.isUnit_iff_isUnit_det _).mpr
          (isUnit_iff_ne_zero.mpr (hpos x hx).det_pos.ne'))).continuousAt (hH x hx)
  have hdet : ContinuousOn (fun x => density (H x)) K :=
    (Real.continuous_sqrt.comp (Continuous.matrix_det continuous_id)).comp_continuousOn hH
  have hentry : ContinuousOn (fun x => (H x)⁻¹ i j) K :=
    (continuous_apply j).comp_continuousOn ((continuous_apply i).comp_continuousOn hinv)
  exact (hdet.mul hentry).aemeasurable hK.measurableSet

/-- The energy density of the cutoff differential is almost everywhere
measurable on a compact set. -/
theorem aemeasurable_cutoffEnergy (hK : IsCompact K) (hH : ContinuousOn H K)
    (hpos : ∀ x ∈ K, (H x).PosDef) (χ : Covector → ℝ) :
    AEMeasurable (cutoffEnergy H χ) (volume.restrict K) := by
  have he : cutoffEnergy H χ = fun x => ∑ i : Fin 4, ∑ j : Fin 4,
      (density (H x) * (H x)⁻¹ i j) * fderiv ℝ χ x (axis i) * fderiv ℝ χ x (axis j) := by
    funext x
    simp only [cutoffEnergy, realEnergy, dotProduct, Matrix.mulVec, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [he]
  refine Finset.aemeasurable_fun_sum _ fun i _ => Finset.aemeasurable_fun_sum _ fun j _ => ?_
  exact ((aemeasurable_coefficient hK hH hpos i j).mul
    (measurable_fderiv_apply_const ℝ χ (axis i)).aemeasurable).mul
    (measurable_fderiv_apply_const ℝ χ (axis j)).aemeasurable

/-- The energy density of the field differential is almost everywhere
measurable on a compact set. -/
theorem aemeasurable_fieldEnergy (hK : IsCompact K) (hH : ContinuousOn H K)
    (hpos : ∀ x ∈ K, (H x).PosDef) (ψ : Covector → ℂ) :
    AEMeasurable (fieldEnergy H ψ) (volume.restrict K) := by
  have he : fieldEnergy H ψ = fun x => ∑ i : Fin 4, ∑ j : Fin 4,
      ((density (H x) * (H x)⁻¹ i j) * (fderiv ℝ ψ x (axis i)).re * (fderiv ℝ ψ x (axis j)).re +
        (density (H x) * (H x)⁻¹ i j) * (fderiv ℝ ψ x (axis i)).im *
          (fderiv ℝ ψ x (axis j)).im) := by
    funext x
    simp only [fieldEnergy, complexEnergy, realEnergy, dotProduct, Matrix.mulVec, Finset.mul_sum,
      mul_add, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have hre (i : Fin 4) : AEMeasurable (fun x => (fderiv ℝ ψ x (axis i)).re) (volume.restrict K) :=
    (Complex.measurable_re.comp (measurable_fderiv_apply_const ℝ ψ (axis i))).aemeasurable
  have him (i : Fin 4) : AEMeasurable (fun x => (fderiv ℝ ψ x (axis i)).im) (volume.restrict K) :=
    (Complex.measurable_im.comp (measurable_fderiv_apply_const ℝ ψ (axis i))).aemeasurable
  rw [he]
  refine Finset.aemeasurable_fun_sum _ fun i _ => Finset.aemeasurable_fun_sum _ fun j _ => ?_
  exact (((aemeasurable_coefficient hK hH hpos i j).mul (hre i)).mul (hre j)).add
    (((aemeasurable_coefficient hK hH hpos i j).mul (him i)).mul (him j))

/-- The cutoff error bound: one constant, determined by the compact set and
the two metrics, bounds the integrated error by the supremum of the test and
the `L²(h)` norms of the field differential on the support of the cutoff
differential and of the cutoff differential. -/
theorem exists_error_bound (hK : IsCompact K) (hH : ContinuousOn H K)
    (hpos : ∀ x ∈ K, (H x).PosDef) (hg : ∀ x ∈ K, ContDiffAt ℝ 1 g x)
    (hd : ∀ x ∈ K, (g x).det < 0) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (χ : Covector → ℝ) (φ ψ : Covector → ℂ) (A : ℝ), 0 ≤ A →
      (∀ x ∈ K, ‖φ x‖ ≤ A) →
      ∫⁻ x in K, ‖error χ g φ ψ x‖ₑ ≤ ENNReal.ofReal (M * A) *
        ((∫⁻ x in K ∩ {x | fderiv ℝ χ x ≠ 0}, ENNReal.ofReal (fieldEnergy H ψ x)) ^ (1 / 2 : ℝ) *
          (∫⁻ x in K, ENNReal.ofReal (cutoffEnergy H χ x)) ^ (1 / 2 : ℝ)) := by
  obtain ⟨Ch, hCh, hcmp⟩ := compact_energy_comparison hK hH hpos
  obtain ⟨Bg, hBg, hcoeff⟩ := CoordinateMetricFluxL2.coefficient_data hK Subset.rfl hg hd
  refine ⟨16 * Bg * Ch, by positivity, fun χ φ ψ A hA hφ => ?_⟩
  have hKm : MeasurableSet K := hK.measurableSet
  set S : Set Covector := {x | fderiv ℝ χ x ≠ 0} with hSdef
  have hSm : MeasurableSet S :=
    (measurable_fderiv ℝ χ) (measurableSet_singleton (0 : Covector →L[ℝ] ℝ)).compl
  set F : Covector → ℝ≥0∞ := S.indicator fun x => ENNReal.ofReal (√(fieldEnergy H ψ x))
    with hFdef
  set G : Covector → ℝ≥0∞ := fun x => ENNReal.ofReal (√(cutoffEnergy H χ x)) with hGdef
  have hGm : AEMeasurable G (volume.restrict K) :=
    (aemeasurable_cutoffEnergy hK hH hpos χ).sqrt.ennreal_ofReal
  have hpoint : ∀ x ∈ K, ‖error χ g φ ψ x‖ₑ ≤
      ENNReal.ofReal (16 * Bg * Ch * A) * (F x * G x) := by
    intro x hx
    by_cases hxS : x ∈ S
    · have hb := norm_error_le (χ := χ) (ψ := ψ) hBg hCh.le hA (fun μ ν => (hcoeff μ ν).1 x hx)
        (hφ x hx) (hcmp x hx).2.1 (hcmp x hx).2.2
      rw [hFdef, indicator_of_mem hxS, hGdef, ← ENNReal.ofReal_mul (Real.sqrt_nonneg _),
        ← ENNReal.ofReal_mul (by positivity), ← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal hb
    · have hz : fderiv ℝ χ x = 0 := not_not.mp hxS
      rw [error_eq_zero hz, enorm_zero]
      exact bot_le
  have hF2 : ∫⁻ x in K, F x ^ (2 : ℝ) =
      ∫⁻ x in K ∩ S, ENNReal.ofReal (fieldEnergy H ψ x) := by
    have e1 : ∀ x ∈ K, F x ^ (2 : ℝ) =
        S.indicator (fun x => ENNReal.ofReal (fieldEnergy H ψ x)) x := by
      intro x hx
      have hnn : 0 ≤ fieldEnergy H ψ x :=
        mul_nonneg (density_pos (hpos x hx)).le (complexEnergy_nonneg (hpos x hx) _)
      by_cases hxS : x ∈ S
      · rw [hFdef, indicator_of_mem hxS, indicator_of_mem hxS,
          ENNReal.ofReal_rpow_of_nonneg (Real.sqrt_nonneg _) (by norm_num), Real.rpow_two,
          Real.sq_sqrt hnn]
      · rw [hFdef, indicator_of_notMem hxS, indicator_of_notMem hxS]
        simp
    rw [setLIntegral_congr_fun hKm e1, lintegral_indicator hSm, Measure.restrict_restrict hSm,
      inter_comm]
  have hG2 : ∫⁻ x in K, G x ^ (2 : ℝ) = ∫⁻ x in K, ENNReal.ofReal (cutoffEnergy H χ x) := by
    refine setLIntegral_congr_fun hKm fun x hx => ?_
    have hnn : 0 ≤ cutoffEnergy H χ x :=
      mul_nonneg (density_pos (hpos x hx)).le (realEnergy_nonneg (hpos x hx) _)
    rw [hGdef, ENNReal.ofReal_rpow_of_nonneg (Real.sqrt_nonneg _) (by norm_num), Real.rpow_two,
      Real.sq_sqrt hnn]
  have hFm : AEMeasurable F (volume.restrict K) :=
    (aemeasurable_fieldEnergy hK hH hpos ψ).sqrt.ennreal_ofReal.indicator hSm
  have hholder := ENNReal.lintegral_mul_le_Lp_mul_Lq (volume.restrict K)
    Real.HolderConjugate.two_two hFm hGm
  calc ∫⁻ x in K, ‖error χ g φ ψ x‖ₑ
      ≤ ∫⁻ x in K, ENNReal.ofReal (16 * Bg * Ch * A) * (F x * G x) :=
        setLIntegral_mono' hKm hpoint
    _ = ENNReal.ofReal (16 * Bg * Ch * A) * ∫⁻ x in K, F x * G x :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (16 * Bg * Ch * A) *
          ((∫⁻ x in K, F x ^ (2 : ℝ)) ^ (1 / 2 : ℝ) * (∫⁻ x in K, G x ^ (2 : ℝ)) ^ (1 / 2 : ℝ)) := by
        gcongr
        exact hholder
    _ = _ := by rw [hF2, hG2]

variable {N V : Set Covector} {r : Covector → ℝ} {L c A : ℝ}

/-- For the logarithmic cutoff of a distance function to a locally flat nodal
set and a field of finite `h`-energy on the compact set, the integrated
cutoff error tends to zero with the cutoff radius. -/
theorem tendsto_error (h : LocallyFlat N V) (hK : IsCompact K) (hKV : K ⊆ V)
    (hN : N.Nonempty) (hL : 0 ≤ L) (hc : 0 < c)
    (hlip : ∀ x ∈ K, ∀ᶠ y in 𝓝 x, |r y - r x| ≤ L * ‖y - x‖)
    (hlow : ∀ x ∈ K, c * infDist x N ≤ r x) (hH : ContinuousOn H K)
    (hpos : ∀ x ∈ K, (H x).PosDef) (hg : ∀ x ∈ K, ContDiffAt ℝ 1 g x)
    (hd : ∀ x ∈ K, (g x).det < 0) (hA : 0 ≤ A) (hφ : ∀ x ∈ K, ‖φ x‖ ≤ A)
    (hE : ∫⁻ x in K, ENNReal.ofReal (fieldEnergy H ψ x) ≠ ⊤) :
    Tendsto (fun ε : ℝ => ∫⁻ x in K, ‖error (fun y => profile ε (r y)) g φ ψ x‖ₑ)
      (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨M, -, hM⟩ := exists_error_bound hK hH hpos hg hd
  obtain ⟨C, ε₀, hC, hε₀, hε₁, hb⟩ :=
    DistanceCutoffEnergy.exists_auxiliary_energy_bound h hK hKV hN hL hc hlip hlow hH hpos
  set T : ℝ≥0∞ := ∫⁻ x in K, ENNReal.ofReal (fieldEnergy H ψ x) with hTdef
  have hlog : Tendsto (fun ε : ℝ => ENNReal.ofReal (C / |Real.log ε|)) (𝓝[>] 0) (𝓝 0) :=
    DistanceCutoffEnergy.tendsto_of_log_bound ⟨C, ε₀, hC, hε₀, hε₁, fun _ _ _ => le_rfl⟩
  have hsqrt : Tendsto (fun ε : ℝ => ENNReal.ofReal (C / |Real.log ε|) ^ (1 / 2 : ℝ))
      (𝓝[>] 0) (𝓝 0) := by
    have h1 := ((ENNReal.continuous_rpow_const (y := (1 / 2 : ℝ))).tendsto 0).comp hlog
    rwa [ENNReal.zero_rpow_of_pos (by norm_num)] at h1
  have hT : T ^ (1 / 2 : ℝ) ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by norm_num) hE
  have hupper : Tendsto (fun ε : ℝ => ENNReal.ofReal (M * A) *
      (T ^ (1 / 2 : ℝ) * ENNReal.ofReal (C / |Real.log ε|) ^ (1 / 2 : ℝ))) (𝓝[>] 0) (𝓝 0) := by
    have h1 := ENNReal.Tendsto.const_mul hsqrt (Or.inr hT)
    have h2 := ENNReal.Tendsto.const_mul h1 (Or.inr (ENNReal.ofReal_ne_top (r := M * A)))
    simpa using h2
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
    (Eventually.of_forall fun _ => bot_le) ?_
  filter_upwards [Ioo_mem_nhdsGT hε₀] with ε hε
  refine (hM (fun y => profile ε (r y)) φ ψ A hA hφ).trans ?_
  gcongr
  · exact lintegral_mono_set inter_subset_left
  · exact hb ε hε.1 hε.2

/-- The integral of the cutoff error itself tends to zero. -/
theorem tendsto_integral_error (h : LocallyFlat N V) (hK : IsCompact K) (hKV : K ⊆ V)
    (hN : N.Nonempty) (hL : 0 ≤ L) (hc : 0 < c)
    (hlip : ∀ x ∈ K, ∀ᶠ y in 𝓝 x, |r y - r x| ≤ L * ‖y - x‖)
    (hlow : ∀ x ∈ K, c * infDist x N ≤ r x) (hH : ContinuousOn H K)
    (hpos : ∀ x ∈ K, (H x).PosDef) (hg : ∀ x ∈ K, ContDiffAt ℝ 1 g x)
    (hd : ∀ x ∈ K, (g x).det < 0) (hA : 0 ≤ A) (hφ : ∀ x ∈ K, ‖φ x‖ ≤ A)
    (hE : ∫⁻ x in K, ENNReal.ofReal (fieldEnergy H ψ x) ≠ ⊤) :
    Tendsto (fun ε : ℝ => ∫ x in K, error (fun y => profile ε (r y)) g φ ψ x)
      (𝓝[>] 0) (𝓝 0) := by
  have h1 := tendsto_error h hK hKV hN hL hc hlip hlow hH hpos hg hd hA hφ hE
  have h2 : Tendsto (fun ε : ℝ => ‖∫ x in K, error (fun y => profile ε (r y)) g φ ψ x‖ₑ)
      (𝓝[>] 0) (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h1 (fun _ => bot_le)
      fun _ => enorm_integral_le_lintegral_enorm _
  have h3 := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h2
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine h3.congr fun ε => ?_
  simp only [Function.comp_apply, toReal_enorm]

end FoliationQM.DistanceCutoffWeakError
