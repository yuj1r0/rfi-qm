module

public import FoliationQM.WassersteinDirac
public import FoliationQM.WassersteinFiniteMoment
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
public import Mathlib.Topology.UniformSpace.HeineCantor
public import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

/-!
# Uniform test convergence from finite concentration

A compact reference image controls each bounded continuous test near the
reference and its global bound controls the remaining points. Integrable
first distance moments then give uniform convergence in time, followed by
convergence in the actual weak topology on probability measures at each time.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.UniformWeakConcentration

open MeasureTheory Filter Set WassersteinCoupling
open scoped Topology ENNReal BoundedContinuousFunction

variable {E ι : Type*} [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
variable {Y : ℝ → E} {T : ℝ}

omit [MeasurableSpace E] [BorelSpace E] in
/-- Compact reference points have a common affine distance bound for each bounded continuous test, including points outside the compact set. -/
theorem exists_affine_test_bound {K : Set E} (hK : IsCompact K)
    (f : E →ᵇ ℝ) {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ K, ∀ x, |f x - f y| ≤ η + C * dist x y := by
  have hu := hK.uniformContinuousAt_of_continuousAt (f : E → ℝ)
    (fun _ _ => f.continuous.continuousAt) (Metric.dist_mem_uniformity hη)
  obtain ⟨δ, hδ, hnear⟩ := Metric.mem_uniformity_dist.mp hu
  let C : ℝ := 2 * ‖f‖ / δ
  have hC : 0 ≤ C := div_nonneg (mul_nonneg (by norm_num) (norm_nonneg f)) hδ.le
  refine ⟨C, hC, ?_⟩
  intro y hy x
  by_cases hxy : dist x y < δ
  · have hfxy : |f x - f y| < η := by
      have h := hnear (a := y) (b := x) (by simpa only [dist_comm] using hxy) hy
      change dist (f y) (f x) < η at h
      simpa only [Real.dist_eq, abs_sub_comm] using h
    exact hfxy.le.trans (le_add_of_nonneg_right (mul_nonneg hC dist_nonneg))
  · have hfar : δ ≤ dist x y := le_of_not_gt hxy
    have hglob : |f x - f y| ≤ 2 * ‖f‖ := by
      simpa only [Real.dist_eq] using f.dist_le_two_norm x y
    have hcancel : C * δ = 2 * ‖f‖ := by
      dsimp [C]
      exact div_mul_cancel₀ _ hδ.ne'
    calc
      |f x - f y| ≤ 2 * ‖f‖ := hglob
      _ = C * δ := hcancel.symm
      _ ≤ C * dist x y := mul_le_mul_of_nonneg_left hfar hC
      _ ≤ η + C * dist x y := le_add_of_nonneg_left hη.le

/-- Genuine integrability of the distance majorant gives the corresponding actual probability-integral error bound. -/
theorem integral_error_le_affine (ν : ProbabilityMeasure E) (f : E →ᵇ ℝ)
    {y : E} {η C : ℝ}
    (hdist : Integrable (fun x => dist x y) (ν : Measure E))
    (hpoint : ∀ x, |f x - f y| ≤ η + C * dist x y) :
    |(∫ x, f x ∂(ν : Measure E)) - f y| ≤
      η + C * (∫ x, dist x y ∂(ν : Measure E)) := by
  have hf : Integrable (fun x => f x) (ν : Measure E) := f.integrable _
  have hdiff : Integrable (fun x => f x - f y) (ν : Measure E) :=
    hf.sub (integrable_const _)
  have habs : Integrable (fun x => |f x - f y|) (ν : Measure E) := by
    simpa only [Real.norm_eq_abs] using hdiff.norm
  have hmajor : Integrable (fun x => η + C * dist x y) (ν : Measure E) :=
    (integrable_const η).add (hdist.const_mul C)
  calc
    |(∫ x, f x ∂(ν : Measure E)) - f y| =
        |∫ x, f x - f y ∂(ν : Measure E)| := by
      rw [integral_sub hf (integrable_const _)]
      simp
    _ ≤ ∫ x, |f x - f y| ∂(ν : Measure E) := by
      simpa only [Real.norm_eq_abs] using
        norm_integral_le_integral_norm (fun x => f x - f y)
    _ ≤ ∫ x, η + C * dist x y ∂(ν : Measure E) :=
      integral_mono habs hmajor hpoint
    _ = η + C * (∫ x, dist x y ∂(ν : Measure E)) := by
      rw [integral_add (integrable_const η) (hdist.const_mul C), integral_const_mul]
      simp

/-- An eventual integrable first-moment majorant tending to zero controls each bounded continuous test uniformly over the fixed time interval. -/
theorem tendstoUniformlyOn_integral_of_moment_bound
    (ν : ι → ℝ → ProbabilityMeasure E) (l : Filter ι)
    (hY : ContinuousOn Y (Icc 0 T)) {B : ι → ℝ}
    (hgood : ∀ᶠ i in l, ∀ t ∈ Icc 0 T,
      Integrable (fun x => dist x (Y t)) (ν i t : Measure E) ∧
      (∫ x, dist x (Y t) ∂(ν i t : Measure E)) ≤ B i)
    (hB : Tendsto B l (𝓝 0)) :
    ∀ f : E →ᵇ ℝ, TendstoUniformlyOn
      (fun i t => ∫ x, f x ∂(ν i t : Measure E))
      (fun t => f (Y t)) l (Icc 0 T) := by
  intro f
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  obtain ⟨C, hC, hpoint⟩ := exists_affine_test_bound
    (isCompact_Icc.image_of_continuousOn hY) f (half_pos hε)
  have hlim : Tendsto (fun i => ε / 2 + C * B i) l (𝓝 (ε / 2)) := by
    simpa only [mul_zero, add_zero] using (hB.const_mul C).const_add (ε / 2)
  filter_upwards [hgood, hlim.eventually_lt_const (by linarith : ε / 2 < ε)]
    with i hi hsmall t ht
  have herror := integral_error_le_affine (ν i t) f (hi t ht).1
    (hpoint (Y t) (mem_image_of_mem Y ht))
  have hbound : |(∫ x, f x ∂(ν i t : Measure E)) - f (Y t)| < ε := by
    calc
      |(∫ x, f x ∂(ν i t : Measure E)) - f (Y t)| ≤
          ε / 2 + C * (∫ x, dist x (Y t) ∂(ν i t : Measure E)) := herror
      _ ≤ ε / 2 + C * B i := add_le_add le_rfl
        (mul_le_mul_of_nonneg_left (hi t ht).2 hC)
      _ < ε := hsmall
  simpa only [Real.dist_eq, abs_sub_comm] using hbound

/-- Uniform real Dirac costs together with their eventual genuine finiteness imply uniform convergence for every fixed bounded continuous test. -/
theorem tendstoUniformlyOn_integral_of_uniform_cost
    (ν : ι → ℝ → ProbabilityMeasure E) (l : Filter ι)
    (hY : ContinuousOn Y (Icc 0 T))
    (hfinite : ∀ᶠ i in l, ∀ t ∈ Icc 0 T,
      eW1 (ν i t : Measure E) (Measure.dirac (Y t)) ≠ ∞)
    (hcost : TendstoUniformlyOn
      (fun i t => (eW1 (ν i t : Measure E) (Measure.dirac (Y t))).toReal)
      (fun _ => 0) l (Icc 0 T)) :
    ∀ f : E →ᵇ ℝ, TendstoUniformlyOn
      (fun i t => ∫ x, f x ∂(ν i t : Measure E))
      (fun t => f (Y t)) l (Icc 0 T) := by
  intro f
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  obtain ⟨C, hC, hpoint⟩ := exists_affine_test_bound
    (isCompact_Icc.image_of_continuousOn hY) f (half_pos hε)
  have hC1 : 0 < C + 1 := by linarith
  have hδ : 0 < ε / (2 * (C + 1)) := div_pos hε (mul_pos (by norm_num) hC1)
  filter_upwards [hfinite, Metric.tendstoUniformlyOn_iff.mp hcost _ hδ]
    with i hi hsmall t ht
  have hmoment : WassersteinFiniteMoment.moment (ν i t : Measure E) (Y t) < ∞ := by
    rw [WassersteinFiniteMoment.moment, ← WassersteinDirac.eW1_dirac]
    exact lt_top_iff_ne_top.mpr (hi t ht)
  have hdist := (WassersteinFiniteMoment.moment_lt_top_iff_integrable_dist
    (ν i t : Measure E) (Y t)).mp hmoment
  have hq : (eW1 (ν i t : Measure E) (Measure.dirac (Y t))).toReal <
      ε / (2 * (C + 1)) := by
    simpa only [Real.dist_eq, zero_sub, abs_neg,
      abs_of_nonneg ENNReal.toReal_nonneg] using hsmall t ht
  have hmul : (C + 1) * (eW1 (ν i t : Measure E)
      (Measure.dirac (Y t))).toReal < ε / 2 := by
    have h := (lt_div_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) hC1)).mp hq
    nlinarith
  have herror := integral_error_le_affine (ν i t) f hdist
    (hpoint (Y t) (mem_image_of_mem Y ht))
  rw [← WassersteinDirac.eW1_dirac_toReal hdist] at herror
  have hbound : |(∫ x, f x ∂(ν i t : Measure E)) - f (Y t)| < ε := by
    have hnonneg := ENNReal.toReal_nonneg
      (a := eW1 (ν i t : Measure E) (Measure.dirac (Y t)))
    nlinarith
  simpa only [Real.dist_eq, abs_sub_comm] using hbound

/-- Uniform convergence of every fixed test gives actual weak convergence of probability measures at every interval time, along an arbitrary filter. -/
theorem tendsto_probabilityMeasure_of_uniform_integral
    (ν : ι → ℝ → ProbabilityMeasure E) (l : Filter ι)
    (h : ∀ f : E →ᵇ ℝ, TendstoUniformlyOn
      (fun i t => ∫ x, f x ∂(ν i t : Measure E))
      (fun t => f (Y t)) l (Icc 0 T)) :
    ∀ t ∈ Icc 0 T, Tendsto (fun i => ν i t) l
      (𝓝 (Measure.dirac (Y t)).toProbabilityMeasure) := by
  intro t ht
  apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr
  intro f
  simpa using (h f).tendsto_at ht

/-- Finite genuine Dirac concentration yields convergence in the library probability weak topology at each fixed interval time. -/
theorem tendsto_probabilityMeasure_of_uniform_cost
    (ν : ι → ℝ → ProbabilityMeasure E) (l : Filter ι)
    (hY : ContinuousOn Y (Icc 0 T))
    (hfinite : ∀ᶠ i in l, ∀ t ∈ Icc 0 T,
      eW1 (ν i t : Measure E) (Measure.dirac (Y t)) ≠ ∞)
    (hcost : TendstoUniformlyOn
      (fun i t => (eW1 (ν i t : Measure E) (Measure.dirac (Y t))).toReal)
      (fun _ => 0) l (Icc 0 T)) :
    ∀ t ∈ Icc 0 T, Tendsto (fun i => ν i t) l
      (𝓝 (Measure.dirac (Y t)).toProbabilityMeasure) :=
  tendsto_probabilityMeasure_of_uniform_integral ν l
    (tendstoUniformlyOn_integral_of_uniform_cost ν l hY hfinite hcost)

end FoliationQM.UniformWeakConcentration
