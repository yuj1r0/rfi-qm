module
public import FoliationQM.TwistedScalarAction

/-!
# Testing local L¹ limits against compact functions

For the stationary limit in v13 `thm:dirac_lift`, a compact test probes
only its own closed support. The integral bound uses its uniform norm and
the ordinary local L¹ error of the field; derivatives of the field are
unnecessary for this step.
-/

@[expose] public section
noncomputable section
open scoped Topology ComplexConjugate
namespace FoliationQM.ScalarLocalTesting
open MeasureTheory Filter Set

/-- Local L¹ convergence on each compact subset of the comparison region, including
integrability of the fields being compared. -/
def LocalL1 (U : Set Covector) (F : ℕ → Covector → ℂ) (f : Covector → ℂ) : Prop :=
  ∀ K : Set Covector, IsCompact K → K ⊆ U →
    (∀ n, IntegrableOn (F n) K) ∧ IntegrableOn f K ∧
      Tendsto (fun n => ∫ x in K, ‖F n x - f x‖) atTop (𝓝 0)

variable {U : Set Covector} {F : ℕ → Covector → ℂ} {f : Covector → ℂ}

/-- Convergence uniformly on compact sets of continuous fields implies local L¹ convergence. -/
theorem of_locally_uniform (hF : ∀ n, ∀ x ∈ U, ContinuousAt (F n) x) (hf : ∀ x ∈ U, ContinuousAt f x)
    (hu : ∀ K : Set Covector, IsCompact K → K ⊆ U → TendstoUniformlyOn F f atTop K) : LocalL1 U F f := by
  intro K hK hs
  have hn (n : ℕ) : ContinuousOn (F n) K := fun x hx => (hF n x (hs hx)).continuousWithinAt
  have hcont : ContinuousOn f K := fun x hx => (hf x (hs hx)).continuousWithinAt
  refine ⟨fun n => (hn n).integrableOn_compact hK, hcont.integrableOn_compact hK, ?_⟩
  have hv := hu K hK hs
  have ht := tendsto_integral_filter_of_dominated_convergence (l := (atTop : Filter ℕ)) (μ := volume.restrict K)
    (F := fun n x => ‖F n x - f x‖) (f := fun _ => (0 : ℝ)) (fun _ => (1 : ℝ))
    (Eventually.of_forall fun n => ((hn n).sub hcont).norm.aestronglyMeasurable hK.measurableSet)
    ?_ (integrableOn_const (μ := volume) hK.measure_lt_top.ne) ?_
  · simpa using ht
  · filter_upwards [(Metric.tendstoUniformlyOn_iff.mp hv) 1 zero_lt_one] with n hn'
    filter_upwards [ae_restrict_mem hK.measurableSet] with x hx
    change ‖‖F n x - f x‖‖ ≤ (1 : ℝ)
    rw [Real.norm_of_nonneg (norm_nonneg _), ← dist_eq_norm, dist_comm]
    exact (hn' x hx).le
  · filter_upwards [ae_restrict_mem hK.measurableSet] with x hx
    simpa using ((hv.tendsto_at hx).sub (tendsto_const_nhds (x := f x))).norm

/-- A complex test against a locally integrable field, using its real Dirac/KG pairing. -/
def tested (U : Set Covector) (η f : Covector → ℂ) : ℝ := ∫ x in U, (conj (η x) * f x).re

/-- The tested integral can be restricted to the actual compact interior support. -/
theorem tested_support (hU : IsOpen U) {η : Covector → ℂ} (hs : tsupport η ⊆ U) (f : Covector → ℂ) :
    tested U η f = ∫ x in tsupport η, (conj (η x) * f x).re := by
  apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hU.measurableSet hs
  intro x hx
  simp [image_eq_zero_of_notMem_tsupport hx.2]

/-- Local L¹ convergence passes through every continuous compact interior test. -/
theorem tendsto_tested (hU : IsOpen U) (h : LocalL1 U F f) {η : Covector → ℂ}
    (he : Continuous η) (hc : HasCompactSupport η) (hs : tsupport η ⊆ U) :
    Tendsto (fun n => tested U η (F n)) atTop (𝓝 (tested U η f)) := by
  let K := tsupport η
  obtain ⟨hi, hf, hlim⟩ := h K hc hs
  obtain ⟨C, hC⟩ := hc.exists_bound_of_continuous he
  have it {g : Covector → ℂ} (hg : IntegrableOn g K) : IntegrableOn (fun x => (conj (η x) * g x).re) K := by
    exact (hg.bdd_mul he.star.aestronglyMeasurable
      (Eventually.of_forall (fun x => by simpa using hC x))).re
  have hdiff (n : ℕ) :
      tested U η (F n) - tested U η f = ∫ x in K, (conj (η x) * (F n x - f x)).re := by
    rw [tested_support hU hs, tested_support hU hs, ← integral_sub (it (hi n)) (it hf)]
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by simp [mul_sub]
  rw [tendsto_iff_norm_sub_tendsto_zero]
  apply squeeze_zero (fun _ => norm_nonneg _) (g := fun n => C * ∫ x in K, ‖F n x - f x‖)
  · intro n
    rw [hdiff n, ← integral_const_mul]
    apply norm_integral_le_of_norm_le ((hi n).sub hf |>.norm.const_mul C)
    apply Eventually.of_forall
    intro x
    calc
      ‖(conj (η x) * (F n x - f x)).re‖ ≤ ‖conj (η x) * (F n x - f x)‖ :=
        Complex.abs_re_le_norm _
      _ ≤ C * ‖F n x - f x‖ := by
        rw [norm_mul, Complex.norm_conj]
        exact mul_le_mul_of_nonneg_right (hC x) (norm_nonneg _)
  · simpa using hlim.const_mul C

end FoliationQM.ScalarLocalTesting
