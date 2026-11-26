module

public import FoliationQM.CoordinateCutoffTestLimit
public import FoliationQM.ActionDensity
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

/-!
# Actual weak directional derivatives across the coordinate nodal axis

Source: v13 `eq:log_cutoff_l2_bound` and its following distributional
derivative argument, component kinds C and D. The constructed compact tests
avoid the literal flat axis, so genuine integration by parts applies with
only off-axis differentiability of the field. The proved full test-pairing
limits then give the original weak identity. A supplied L2 differential
representative is transferred through the actual null axis. Hilbert Sobolev
membership, curved nodal geometry and metric-weighted PDE extension are separate.
-/

@[expose] public section
noncomputable section

namespace FoliationQM.CoordinateOffAxisWeakDerivative

open Filter MeasureTheory Set SmoothCoordinateTubeCutoff CoordinateCutoffTestLimit
open scoped ContDiff Topology ComplexConjugate

private theorem supported_pair {a b : Covector → ℂ} {C : Set Covector}
    (hs : tsupport a ⊆ C) (hi : IntegrableOn (fun x => star (a x) * b x) C volume) :
    Integrable (fun x => star (a x) * b x) volume ∧
    (∫ x in C, star (a x) * b x) = ∫ x, star (a x) * b x := by
  have hz : ∀ x, x ∉ C → star (a x) * b x = 0 := by
    intro x hx
    have hxa : x ∉ tsupport a := fun ha => hx (hs ha)
    simp only [image_eq_zero_of_notMem_tsupport hxa, star_zero, zero_mul]
  exact ⟨hi.integrable_of_forall_notMem_eq_zero hz,
    setIntegral_eq_integral_of_forall_compl_eq_zero hz⟩

/-- Off-axis differentiability and actual local L2 field/derivative data give genuinely integrable ambient test pairings and the weak directional derivative identity across the literal coordinate axis. -/
theorem weak_directional_identity {φ ψ : Covector → ℂ} {U : Set Covector}
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ U)
    (hψ : MemLp ψ 2 (volume.restrict U))
    (hdiff : ∀ x ∈ U \ {y : Covector | y 2 = 0 ∧ y 3 = 0}, DifferentiableAt ℝ ψ x)
    (v : Covector)
    (hD : MemLp (fun x => fderiv ℝ ψ x v) 2 (volume.restrict U)) :
    Integrable (fun x => star (fderiv ℝ φ x v) * ψ x) volume ∧
    Integrable (fun x => star (φ x) * fderiv ℝ ψ x v) volume ∧
    (∫ x, star (fderiv ℝ φ x v) * ψ x) = -(∫ x, star (φ x) * fderiv ℝ ψ x v) := by
  have Hψ := test_pairing_data hφ hc hs hψ v
  have HD := test_pairing_data hφ hc hs hD v
  have hi := supported_pair (tsupport_fderiv_apply_subset ℝ v) Hψ.2.1
  have hj := supported_pair (Subset.rfl : tsupport φ ⊆ tsupport φ) HD.1
  refine ⟨hi.1, hj.1, ?_⟩
  have hleft := (test_pairing_limits hφ hc hs hψ v).2
  have hright := ((test_pairing_limits hφ hc hs hD v).1).neg
  have heq : ∀ᶠ ε : ℝ in 𝓝[>] 0,
      (∫ x in tsupport φ, star (fderiv ℝ (CoordinateCutoffTests.test ε φ) x v) * ψ x) =
        -(∫ x in tsupport φ, star (CoordinateCutoffTests.test ε φ x) * fderiv ℝ ψ x v) := by
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with ε hε
    have Hε := CoordinateCutoffTests.test_data hε.1 hε.2 hφ hc hs
    have hηs : tsupport (CoordinateCutoffTests.test ε φ) ⊆ tsupport φ :=
      fun x hx => (Hε.2.2.1 hx).1
    have hηd : tsupport (fun x => fderiv ℝ (CoordinateCutoffTests.test ε φ) x v) ⊆
        tsupport φ := (tsupport_fderiv_apply_subset ℝ v).trans hηs
    have hL := supported_pair hηd (Hψ.2.2 hε.1 hε.2).2
    have hR := supported_pair hηs (HD.2.2 hε.1 hε.2).1
    have hP := supported_pair hηs (Hψ.2.2 hε.1 hε.2).1
    have hconj (x : Covector) :
        fderiv ℝ (fun y => conj (CoordinateCutoffTests.test ε φ y)) x v =
          star (fderiv ℝ (CoordinateCutoffTests.test ε φ) x v) :=
      ActionDensity.fderiv_conj_apply (Hε.1.differentiable (by simp) x) v
    have hfi : Integrable (fun x =>
        fderiv ℝ (fun y => conj (CoordinateCutoffTests.test ε φ y)) x v * ψ x) volume := by
      simpa only [hconj] using hL.1
    have hcs : tsupport (fun x => conj (CoordinateCutoffTests.test ε φ x)) ⊆
        tsupport (CoordinateCutoffTests.test ε φ) :=
      tsupport_comp_subset (g := Complex.conjCLE) (map_zero _) _
    have H := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable hfi hR.1 hP.1
      (fun x _ => Complex.conjCLE.toContinuousLinearMap.differentiableAt.comp x
        (Hε.1.differentiable (by simp) x))
      (fun x hx => hdiff x (Hε.2.2.2 (hcs hx)))
    simp only [hconj] at H
    rw [hL.2, hR.2]
    exact (neg_neg _).symm.trans (congrArg Neg.neg H.symm)
  have H := tendsto_nhds_unique_of_eventuallyEq hleft hright heq
  rw [hi.2, hj.2] at H
  exact H

/-- An actual L2 continuous-linear differential representative agreeing with the classical differential off the axis supplies the same ambient weak identity; its values on the null axis need no classical interpretation. -/
theorem weak_of_representative {φ ψ : Covector → ℂ} {U : Set Covector}
    {G : Covector → Covector →L[ℝ] ℂ}
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ U)
    (hψ : MemLp ψ 2 (volume.restrict U)) (hG : MemLp G 2 (volume.restrict U))
    (hderiv : ∀ x ∈ U \ {y : Covector | y 2 = 0 ∧ y 3 = 0}, HasFDerivAt ψ (G x) x)
    (v : Covector) :
    Integrable (fun x => star (fderiv ℝ φ x v) * ψ x) volume ∧
    Integrable (fun x => star (φ x) * G x v) volume ∧
    (∫ x, star (fderiv ℝ φ x v) * ψ x) = -(∫ x, star (φ x) * G x v) := by
  have hψC : MemLp ψ 2 (volume.restrict (tsupport φ)) :=
    MemLp.mono_measure (Measure.restrict_mono_set volume hs) hψ
  have hGC : MemLp G 2 (volume.restrict (tsupport φ)) :=
    MemLp.mono_measure (Measure.restrict_mono_set volume hs) hG
  have hGv : MemLp (fun x => G x v) 2 (volume.restrict (tsupport φ)) :=
    (ContinuousLinearMap.apply ℝ ℂ v).comp_memLp' hGC
  have haxis : ∀ᵐ x : Covector ∂volume, ¬ (x 2 = 0 ∧ x 3 = 0) :=
    measure_eq_zero_iff_ae_notMem.mp axis_null
  have hEq : (fun x => fderiv ℝ ψ x v) =ᵐ[volume.restrict (tsupport φ)] fun x => G x v := by
    filter_upwards [ae_restrict_mem hc.measurableSet, ae_restrict_of_ae haxis] with x hx hn
    exact congrArg (fun L : Covector →L[ℝ] ℂ => L v) (hderiv x ⟨hs hx, hn⟩).fderiv
  have hDC : MemLp (fun x => fderiv ℝ ψ x v) 2 (volume.restrict (tsupport φ)) :=
    MemLp.ae_eq hEq.symm hGv
  have H := weak_directional_identity hφ hc (Subset.rfl : tsupport φ ⊆ tsupport φ) hψC
    (fun x hx => (hderiv x ⟨hs hx.1, hx.2⟩).differentiableAt) v hDC
  have hpair : (fun x => star (φ x) * fderiv ℝ ψ x v) =ᵐ[volume]
      fun x => star (φ x) * G x v := by
    filter_upwards [haxis] with x hn
    by_cases hx : x ∈ tsupport φ
    · rw [(hderiv x ⟨hs hx, hn⟩).fderiv]
    · simp only [image_eq_zero_of_notMem_tsupport hx, star_zero, zero_mul]
  refine ⟨H.1, H.2.1.congr hpair, ?_⟩
  rw [← integral_congr_ae hpair]
  exact H.2.2

end FoliationQM.CoordinateOffAxisWeakDerivative
