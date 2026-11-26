module

public import FoliationQM.AdaptedChartCutoffTests
public import FoliationQM.CoordinateChartAuxiliaryMetric
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Algebra.Order.Star.Real

/-!
# Limits of the adapted-chart cutoff as the radius tends to zero

Source: v13 `thm:wallstrom` Part(c), the cutoff-removal step following
`eq:log_cutoff_l2_bound`, component kinds C and D. On a set inside the source
of a smooth chart, cutoff-weighted integrals of an integrable field converge to
the unweighted integral, using the derived nullity of the points sent to the
axis. On a compact set, the square integral of each directional derivative of
the cutoff tends to zero, by the proved chart energy decay for the Euclidean
coordinate metric, and hence its pairing with any square-integrable field
tends to zero. Neither nullity nor energy decay is a hypothesis.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.AdaptedChartCutoffLimits

open Filter MeasureTheory Set SmoothCoordinateTubeCutoff AdaptedChartCutoffTests RealLorentzFrame
open LorentzMatrixGroup
open scoped ContDiff Topology

variable {e : OpenPartialHomeomorph Covector Covector} {K : Set Covector}

/-- Cutoff-weighted integrals over a measurable set in the chart source converge
to the unweighted integral. -/
theorem cutoff_limit (hi : ContDiffOn ℝ 1 e.symm e.target) (hK : MeasurableSet K)
    (hKs : K ⊆ e.source) {F : Covector → ℂ} (hF : IntegrableOn F K volume) :
    Tendsto (fun ε : ℝ => ∫ x in K, cutoff e ε x • F x) (𝓝[>] 0) (𝓝 (∫ x in K, F x)) := by
  have hI : ∀ᶠ ε : ℝ in 𝓝[>] 0, ε ∈ Ioo (0 : ℝ) 1 :=
    Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)
  refine tendsto_integral_filter_of_dominated_convergence (fun x => ‖F x‖) ?_ ?_ hF.norm ?_
  · filter_upwards [hI] with ε hε
    have hcont : ContinuousOn (cutoff e ε) K :=
      ((contDiff_profile hε.1 hε.2).continuous.comp_continuousOn e.continuousOn).mono hKs
    exact (hcont.aestronglyMeasurable hK).smul hF.aestronglyMeasurable
  · filter_upwards [hI] with ε hε
    refine Eventually.of_forall fun x => ?_
    have hb := cutoff_mem_Icc (e := e) hε.1 hε.2 x
    rw [norm_smul, Real.norm_of_nonneg hb.1]
    exact mul_le_of_le_one_left (norm_nonneg _) hb.2
  · have hnull : ∀ᵐ x ∂volume, x ∉ {x | x ∈ e.source ∧ (e x) 2 = 0 ∧ (e x) 3 = 0} :=
      measure_eq_zero_iff_ae_notMem.mp (volume_axis_preimage hi)
    filter_upwards [ae_restrict_mem hK, ae_restrict_of_ae hnull] with x hx hn
    have hoff : ¬ ((e x) 2 = 0 ∧ (e x) 3 = 0) := fun h => hn ⟨hKs hx, h⟩
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_cutoff_eq_one hoff] with ε hε
    rw [hε, one_smul]

private theorem memLp_of_continuousOn (hK : IsCompact K) {a : Covector → ℝ}
    (ha : ContinuousOn a K) : MemLp a 2 (volume.restrict K) := by
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn ha
  have : IsFiniteMeasure (volume.restrict K) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hK.measure_lt_top⟩
  exact MemLp.of_bound (ha.aestronglyMeasurable hK.measurableSet) C
    ((ae_restrict_mem hK.measurableSet).mono fun x hx => hC x hx)

/-- Each directional derivative of the cutoff is square integrable on a compact
set in the chart source. -/
theorem memLp_cutoff_derivative (he : ContDiffOn ℝ ∞ e e.source) {ε : ℝ} (h0 : 0 < ε)
    (h1 : ε < 1) (hK : IsCompact K) (hKs : K ⊆ e.source) (v : Covector) :
    MemLp (fun x => fderiv ℝ (cutoff e ε) x v) 2 (volume.restrict K) :=
  memLp_of_continuousOn hK
    ((((contDiffOn_cutoff he h0 h1).continuousOn_fderiv_of_isOpen e.open_source
      (by simp)).clm_apply continuousOn_const).mono hKs)

private theorem sq_apply_le (L : Covector →L[ℝ] ℝ) (v : Covector) :
    (L v) ^ 2 ≤ (∑ i, v i ^ 2) * ∑ i, L (RNCCoordinateConnection.axis i) ^ 2 := by
  have h1 : v = ∑ i, v i • RNCCoordinateConnection.axis i := by
    ext j
    simp [RNCCoordinateConnection.axis, Pi.single_apply, Finset.sum_apply]
  have hv : L v = ∑ i, v i * L (RNCCoordinateConnection.axis i) := by
    conv_lhs => rw [h1]
    simp [map_sum, map_smul]
  rw [hv]
  exact Finset.sum_mul_sq_le_sq_mul_sq _ _ _

private theorem energy_one (e : OpenPartialHomeomorph Covector Covector) (ε : ℝ)
    (x : Covector) :
    CoordinateChartAuxiliaryMetric.energy (fun _ => (1 : Mat4)) e ε x =
      ∑ i, (fderiv ℝ (cutoff e ε) x (RNCCoordinateConnection.axis i)) ^ 2 := by
  simp [CoordinateChartAuxiliaryMetric.energy, AuxiliaryMetricEnergy.density,
    AuxiliaryMetricEnergy.realEnergy, dotProduct, cutoff, sq]

/-- The square integral of each directional derivative of the cutoff over a
compact set in the chart source tends to zero. -/
theorem derivative_sq_decay (he : ContDiffOn ℝ ∞ e e.source)
    (hi : ContDiffOn ℝ ∞ e.symm e.target) (hK : IsCompact K) (hKs : K ⊆ e.source)
    (v : Covector) :
    Tendsto (fun ε : ℝ => ∫ x in K, (fderiv ℝ (cutoff e ε) x v) ^ 2) (𝓝[>] 0) (𝓝 0) := by
  have he1 : ContDiffOn ℝ 1 e e.source := he.of_le (by simp)
  have hi1 : ContDiffOn ℝ 1 e.symm e.target := hi.of_le (by simp)
  have hH : ContinuousOn (fun _ : Covector => (1 : Mat4)) K := continuousOn_const
  have hpos : ∀ y ∈ K, ((fun _ : Covector => (1 : Mat4)) y).PosDef := fun _ _ => Matrix.PosDef.one
  have hdecay := (CoordinateChartAuxiliaryMetric.compact_energy_decay he1 hi1 hK hKs hH hpos).1
  obtain ⟨B, -, hb⟩ := CoordinateChartAuxiliaryMetric.compact_energy_data he1 hi1 hK hKs hH hpos
  have hlim : Tendsto (fun ε : ℝ => (∑ i, v i ^ 2) *
      ∫ x in K, CoordinateChartAuxiliaryMetric.energy (fun _ => (1 : Mat4)) e ε x)
      (𝓝[>] 0) (𝓝 0) := by
    simpa only [mul_zero] using hdecay.const_mul (∑ i, v i ^ 2)
  refine squeeze_zero' (Eventually.of_forall fun _ => integral_nonneg fun _ => sq_nonneg _)
    ?_ hlim
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with ε hε
  rw [← integral_const_mul]
  refine integral_mono (memLp_cutoff_derivative he hε.1 hε.2 hK hKs v).integrable_sq
    ((hb hε.1 hε.2).1.const_mul _) fun x => ?_
  dsimp only
  rw [energy_one]
  exact sq_apply_le _ v

/-- The pairing of a directional derivative of the cutoff with a square-integrable
field on a compact set in the chart source tends to zero. -/
theorem derivative_pairing_decay (he : ContDiffOn ℝ ∞ e e.source)
    (hi : ContDiffOn ℝ ∞ e.symm e.target) (hK : IsCompact K) (hKs : K ⊆ e.source)
    {F : Covector → ℂ} (hF : MemLp F 2 (volume.restrict K)) (v : Covector) :
    Tendsto (fun ε : ℝ => ∫ x in K, fderiv ℝ (cutoff e ε) x v • F x) (𝓝[>] 0) (𝓝 0) := by
  have hs : Tendsto (fun ε : ℝ => Real.sqrt (∫ x in K, (fderiv ℝ (cutoff e ε) x v) ^ 2) *
      Real.sqrt (∫ x in K, ‖F x‖ ^ 2)) (𝓝[>] 0) (𝓝 0) := by
    simpa only [Function.comp_def, Real.sqrt_zero, zero_mul] using
      (Real.continuous_sqrt.continuousAt.tendsto.comp
        (derivative_sq_decay he hi hK hKs v)).mul_const (Real.sqrt (∫ x in K, ‖F x‖ ^ 2))
  refine tendsto_zero_iff_norm_tendsto_zero.2
    (squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hs)
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with ε hε
  have ha := memLp_cutoff_derivative he hε.1 hε.2 hK hKs v
  have H := integral_mul_norm_le_Lp_mul_Lq (μ := volume.restrict K)
    Real.HolderConjugate.two_two
    (show MemLp (fun x => ‖fderiv ℝ (cutoff e ε) x v‖) (ENNReal.ofReal 2)
      (volume.restrict K) by simpa using ha.norm)
    (show MemLp (fun x => ‖F x‖) (ENNReal.ofReal 2)
      (volume.restrict K) by simpa using hF.norm)
  have H' : (∫ x in K, ‖fderiv ℝ (cutoff e ε) x v‖ * ‖F x‖) ≤
      Real.sqrt (∫ x in K, (fderiv ℝ (cutoff e ε) x v) ^ 2) *
        Real.sqrt (∫ x in K, ‖F x‖ ^ 2) := by
    simpa only [norm_norm, Real.rpow_two, ← Real.sqrt_eq_rpow, Real.norm_eq_abs, sq_abs,
      abs_abs, abs_norm]
      using H
  calc ‖∫ x in K, fderiv ℝ (cutoff e ε) x v • F x‖
      ≤ ∫ x in K, ‖fderiv ℝ (cutoff e ε) x v • F x‖ := norm_integral_le_integral_norm _
    _ = ∫ x in K, ‖fderiv ℝ (cutoff e ε) x v‖ * ‖F x‖ := by simp only [norm_smul]
    _ ≤ _ := H'

end FoliationQM.AdaptedChartCutoffLimits
