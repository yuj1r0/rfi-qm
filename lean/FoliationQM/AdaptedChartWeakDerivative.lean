module

public import FoliationQM.AdaptedChartCutoffLimits
public import FoliationQM.ActionDensity
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

/-!
# Weak directional derivatives across a nodal set in an adapted chart

Source: v13 `thm:wallstrom` Part(c), the distributional-derivative argument
following `eq:log_cutoff_l2_bound`, component kinds C and D. Let `e` be a
smooth coordinate chart with smooth inverse. For a smooth compact test whose
closed support lies in the chart source, the cut-off tests avoid every point
sent to the coordinate axis, so integration by parts needs differentiability
of the field only away from those points. The proved pairing limits then give
the weak directional-derivative identity for the original test. Thus a field
that is square integrable with square-integrable classical derivative off a
smooth embedded codimension-two set has that derivative as its weak derivative
across the set, locally in each adapted chart.

This is a chart-local coordinate statement. Summation over a partition of
unity, Hilbert Sobolev membership and the metric-weighted wave equation are
separate.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.AdaptedChartWeakDerivative

open Filter MeasureTheory Set SmoothCoordinateTubeCutoff AdaptedChartCutoffTests
open AdaptedChartCutoffLimits RealLorentzFrame
open scoped ContDiff Topology ComplexConjugate

variable {e : OpenPartialHomeomorph Covector Covector} {φ ψ : Covector → ℂ} {U : Set Covector}

/-- A pairing whose first factor is supported in a set is globally integrable with the same integral. -/
theorem supported_pair {a b : Covector → ℂ} {C : Set Covector}
    (hs : tsupport a ⊆ C) (hi : IntegrableOn (fun x => star (a x) * b x) C volume) :
    Integrable (fun x => star (a x) * b x) volume ∧
    (∫ x in C, star (a x) * b x) = ∫ x, star (a x) * b x := by
  have hz : ∀ x, x ∉ C → star (a x) * b x = 0 := by
    intro x hx
    have hxa : x ∉ tsupport a := fun ha => hx (hs ha)
    simp only [image_eq_zero_of_notMem_tsupport hxa, star_zero, zero_mul]
  exact ⟨hi.integrable_of_forall_notMem_eq_zero hz,
    setIntegral_eq_integral_of_forall_compl_eq_zero hz⟩

/-- A smooth compact test and its directional derivative pair integrably with any field square integrable on a set. -/
theorem smooth_pairing {a b : Covector → ℂ} {C : Set Covector}
    (ha : ContDiff ℝ ∞ a) (hca : HasCompactSupport a) (hb : MemLp b 2 (volume.restrict C))
    (v : Covector) :
    IntegrableOn (fun x => star (a x) * b x) C volume ∧
    IntegrableOn (fun x => star (fderiv ℝ a x v) * b x) C volume := by
  have ha2 : MemLp a 2 volume := ha.continuous.memLp_of_hasCompactSupport hca
  have hd2 : MemLp (fun x => fderiv ℝ a x v) 2 volume :=
    ((ha.continuous_fderiv (by simp)).clm_apply
      (continuous_const (y := v))).memLp_of_hasCompactSupport (hca.fderiv_apply ℝ v)
  have haC : MemLp a 2 (volume.restrict C) := MemLp.mono_measure Measure.restrict_le_self ha2
  have hdC : MemLp (fun x => fderiv ℝ a x v) 2 (volume.restrict C) :=
    MemLp.mono_measure Measure.restrict_le_self hd2
  exact ⟨haC.star.integrable_mul hb, hdC.star.integrable_mul hb⟩

/-- The cut-off test pairing and its directional-derivative pairing with a
square-integrable field converge to the pairings of the original test. -/
theorem test_pairing_limits (he : ContDiffOn ℝ ∞ e e.source)
    (hi : ContDiffOn ℝ ∞ e.symm e.target) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ U) (hse : tsupport φ ⊆ e.source)
    (hψ : MemLp ψ 2 (volume.restrict U)) (v : Covector) :
    Tendsto (fun ε : ℝ => ∫ x in tsupport φ, star (test e ε φ x) * ψ x)
      (𝓝[>] 0) (𝓝 (∫ x in tsupport φ, star (φ x) * ψ x)) ∧
    Tendsto (fun ε : ℝ => ∫ x in tsupport φ, star (fderiv ℝ (test e ε φ) x v) * ψ x)
      (𝓝[>] 0) (𝓝 (∫ x in tsupport φ, star (fderiv ℝ φ x v) * ψ x)) := by
  have hK : IsCompact (tsupport φ) := hc
  have hi1 : ContDiffOn ℝ 1 e.symm e.target := hi.of_le (by simp)
  have hψK : MemLp ψ 2 (volume.restrict (tsupport φ)) :=
    MemLp.mono_measure (Measure.restrict_mono_set volume hs) hψ
  have P := smooth_pairing hφ hc hψK v
  have h1 := cutoff_limit hi1 hK.measurableSet hse P.1
  have h2 := cutoff_limit hi1 hK.measurableSet hse P.2
  constructor
  · simpa only [test, star_smul, star_trivial, smul_mul_assoc] using h1
  · obtain ⟨B, hB⟩ := hφ.continuous.bounded_above_of_compact_support hc
    have hF : MemLp (fun x => star (φ x) * ψ x) 2 (volume.restrict (tsupport φ)) := by
      refine hψK.of_le_mul (c := B)
        (hφ.continuous.aestronglyMeasurable.star.mul hψK.aestronglyMeasurable)
        (Eventually.of_forall fun x => ?_)
      rw [norm_mul, norm_star]
      exact mul_le_mul_of_nonneg_right (hB x) (norm_nonneg _)
    have hdec := derivative_pairing_decay he hi hK hse hF v
    have hsum := hdec.add h2
    rw [zero_add] at hsum
    refine hsum.congr' ?_
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with ε hε
    have hia : IntegrableOn (fun x => fderiv ℝ (cutoff e ε) x v • (star (φ x) * ψ x))
        (tsupport φ) volume :=
      memLp_one_iff_integrable.1 ((memLp_cutoff_derivative he hε.1 hε.2 hK hse v).smul hF)
    have hcont : ContinuousOn (cutoff e ε) (tsupport φ) :=
      (contDiffOn_cutoff he hε.1 hε.2).continuousOn.mono hse
    have hic : IntegrableOn (fun x => cutoff e ε x • (star (fderiv ℝ φ x v) * ψ x))
        (tsupport φ) volume := by
      refine P.2.norm.mono' ((hcont.aestronglyMeasurable hK.measurableSet).smul
        P.2.aestronglyMeasurable) (Eventually.of_forall fun x => ?_)
      have hb := cutoff_mem_Icc (e := e) hε.1 hε.2 x
      rw [norm_smul, Real.norm_of_nonneg hb.1]
      exact mul_le_of_le_one_left (norm_nonneg _) hb.2
    rw [← integral_add hia hic]
    refine setIntegral_congr_fun hK.measurableSet fun x hx => ?_
    rw [directional_test hε.1 hε.2 he (hse hx) (hφ.differentiable (by simp) x) v]
    simp only [star_add, star_smul, star_trivial, add_mul, smul_mul_assoc]

/-- Square-integrable field and classical directional derivative, with
differentiability only away from the points the chart sends to the coordinate
axis, give the weak directional-derivative identity across those points. -/
theorem weak_directional_identity (he : ContDiffOn ℝ ∞ e e.source)
    (hi : ContDiffOn ℝ ∞ e.symm e.target) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ U) (hse : tsupport φ ⊆ e.source)
    (hψ : MemLp ψ 2 (volume.restrict U))
    (hdiff : ∀ x ∈ U ∩ e.source, ¬ ((e x) 2 = 0 ∧ (e x) 3 = 0) → DifferentiableAt ℝ ψ x)
    (v : Covector) (hD : MemLp (fun x => fderiv ℝ ψ x v) 2 (volume.restrict U)) :
    Integrable (fun x => star (fderiv ℝ φ x v) * ψ x) volume ∧
    Integrable (fun x => star (φ x) * fderiv ℝ ψ x v) volume ∧
    (∫ x, star (fderiv ℝ φ x v) * ψ x) = -(∫ x, star (φ x) * fderiv ℝ ψ x v) := by
  have hψK : MemLp ψ 2 (volume.restrict (tsupport φ)) :=
    MemLp.mono_measure (Measure.restrict_mono_set volume hs) hψ
  have hDK : MemLp (fun x => fderiv ℝ ψ x v) 2 (volume.restrict (tsupport φ)) :=
    MemLp.mono_measure (Measure.restrict_mono_set volume hs) hD
  have Pψ := smooth_pairing hφ hc hψK v
  have PD := smooth_pairing hφ hc hDK v
  have hi' := supported_pair (tsupport_fderiv_apply_subset ℝ v) Pψ.2
  have hj := supported_pair (Subset.rfl : tsupport φ ⊆ tsupport φ) PD.1
  refine ⟨hi'.1, hj.1, ?_⟩
  have hleft := (test_pairing_limits he hi hφ hc hs hse hψ v).2
  have hright := ((test_pairing_limits he hi hφ hc hs hse hD v).1).neg
  have heq : ∀ᶠ ε : ℝ in 𝓝[>] 0,
      (∫ x in tsupport φ, star (fderiv ℝ (test e ε φ) x v) * ψ x) =
        -(∫ x in tsupport φ, star (test e ε φ x) * fderiv ℝ ψ x v) := by
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with ε hε
    have Hε := test_data hε.1 hε.2 he hφ hc hse
    have hηs : tsupport (test e ε φ) ⊆ tsupport φ := Hε.2.2.1
    have hηd : tsupport (fun x => fderiv ℝ (test e ε φ) x v) ⊆ tsupport φ :=
      (tsupport_fderiv_apply_subset ℝ v).trans hηs
    have Qψ := smooth_pairing Hε.1 Hε.2.1 hψK v
    have QD := smooth_pairing Hε.1 Hε.2.1 hDK v
    have hL := supported_pair hηd Qψ.2
    have hR := supported_pair hηs QD.1
    have hP := supported_pair hηs Qψ.1
    have hconj (x : Covector) :
        fderiv ℝ (fun y => conj (test e ε φ y)) x v = star (fderiv ℝ (test e ε φ) x v) :=
      ActionDensity.fderiv_conj_apply (Hε.1.differentiable (by simp) x) v
    have hfi : Integrable (fun x =>
        fderiv ℝ (fun y => conj (test e ε φ y)) x v * ψ x) volume := by
      simpa only [hconj] using hL.1
    have hcs : tsupport (fun x => conj (test e ε φ x)) ⊆ tsupport (test e ε φ) :=
      tsupport_comp_subset (g := Complex.conjCLE) (map_zero _) _
    have H := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable hfi hR.1 hP.1
      (fun x _ => Complex.conjCLE.toContinuousLinearMap.differentiableAt.comp x
        (Hε.1.differentiable (by simp) x))
      (fun x hx => hdiff x ⟨hs (hηs (hcs hx)), hse (hηs (hcs hx))⟩ (Hε.2.2.2 x (hcs hx)))
    simp only [hconj] at H
    rw [hL.2, hR.2]
    exact (neg_neg _).symm.trans (congrArg Neg.neg H.symm)
  have H := tendsto_nhds_unique_of_eventuallyEq hleft hright heq
  rw [hi'.2, hj.2] at H
  exact H

end FoliationQM.AdaptedChartWeakDerivative
