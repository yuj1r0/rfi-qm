module

public import FoliationQM.OpenIntegrationByParts

/-!
# Complex derivative transfer for compact interior tests

Source: v13 `cor:schrodinger`, kinds C and D. Genuine ambient-volume
integration by parts moves one or two actual constant-direction derivatives
onto a smooth compact test. The background is C² only at points of the
comparison set. Support containment permits restriction to that set without
openness or boundary regularity. Both sides have genuine integrability.
-/

@[expose] public section
noncomputable section

namespace FoliationQM.CompactComplexGreen

open MeasureTheory PolarSecondDifferential OpenIntegrationByParts
open scoped ComplexConjugate ContDiff

/-- A constant directional derivative of a globally smooth complex test is globally smooth. -/
theorem contDiff_directional_test {η : Covector → ℂ} (hη : ContDiff ℝ ∞ η)
    (v : Covector) : ContDiff ℝ ∞ (directionalDerivative η v) :=
  (hη.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

/-- The actual second constant-direction derivative of a smooth test remains globally smooth. -/
theorem contDiff_second_test {η : Covector → ℂ} (hη : ContDiff ℝ ∞ η)
    (v : Covector) : ContDiff ℝ ∞ (secondDirectionalDerivative η v) :=
  contDiff_directional_test (contDiff_directional_test hη v) v

/-- The actual second directional derivative vanishes off the original closed support, without a regularity premise. -/
theorem tsupport_second_subset (η : Covector → ℂ) (v : Covector) :
    tsupport (secondDirectionalDerivative η v) ⊆ tsupport η :=
  (tsupport_fderiv_apply_subset ℝ v).trans (tsupport_fderiv_apply_subset ℝ v)

variable {U : Set Covector} {η u : Covector → ℂ}

/-- Both first-transfer products are genuinely integrable over ambient volume under local C² background regularity. -/
theorem integrable_first_pairings (hη : ContDiff ℝ ∞ η)
    (hu : ∀ x ∈ U, ContDiffAt ℝ 2 u x) (hc : HasCompactSupport η)
    (hs : tsupport η ⊆ U) (v : Covector) :
    Integrable (fun x => conj (η x) * directionalDerivative u v x) ∧
      Integrable (fun x => conj (directionalDerivative η v x) * u x) := by
  constructor
  · exact integrable_conj_mul_local hη.continuous
      (fun x hx => (contDiffAt_directionalDerivative (hu x (hs hx)) v).continuousAt) hc
  · exact integrable_conj_mul_local (contDiff_directional_test hη v).continuous
      (fun x hx => (hu x (hs (tsupport_fderiv_apply_subset ℝ v hx))).continuousAt)
      (hc.fderiv_apply ℝ v)

/-- Both second-transfer products are genuinely integrable, with the same local C² field and compact test. -/
theorem integrable_second_pairings (hη : ContDiff ℝ ∞ η)
    (hu : ∀ x ∈ U, ContDiffAt ℝ 2 u x) (hc : HasCompactSupport η)
    (hs : tsupport η ⊆ U) (v : Covector) :
    Integrable (fun x => conj (η x) * secondDirectionalDerivative u v x) ∧
      Integrable (fun x => conj (secondDirectionalDerivative η v x) * u x) := by
  constructor
  · exact integrable_second_derivative_pair_local (hη.of_le (by simp)) hu hc hs v
  · exact integrable_conj_mul_local (contDiff_second_test hη v).continuous
      (fun x hx => (hu x (hs (tsupport_second_subset η v hx))).continuousAt)
      ((hc.fderiv_apply ℝ v).fderiv_apply ℝ v)

private theorem first_transfer_global (hη : ContDiff ℝ ∞ η)
    (hu : ∀ x ∈ U, ContDiffAt ℝ 2 u x) (hc : HasCompactSupport η)
    (hs : tsupport η ⊆ U) (v : Covector) :
    (∫ x, conj (η x) * directionalDerivative u v x) =
      -(∫ x, conj (directionalDerivative η v x) * u x) := by
  have hconj : ContDiff ℝ ∞ (fun x => conj (η x)) :=
    Complex.conjCLE.toContinuousLinearMap.contDiff.comp hη
  have hder (x : Covector) :
      fderiv ℝ (fun y => conj (η y)) x v = conj (directionalDerivative η v x) :=
    ActionDensity.fderiv_conj_apply (hη.differentiable (by simp) x) v
  have hi := integrable_first_pairings hη hu hc hs v
  have hleft : Integrable (fun x => fderiv ℝ (fun y => conj (η y)) x v * u x) := by
    simp_rw [hder]
    exact hi.2
  have hproduct : Integrable (fun x => conj (η x) * u x) :=
    integrable_conj_mul_local hη.continuous (fun x hx => (hu x (hs hx)).continuousAt) hc
  have he := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable hleft hi.1 hproduct
    (fun x _ => hconj.differentiable (by simp) x)
    (fun x hx => (hu x (hs
      ((tsupport_comp_subset (g := fun z : ℂ => conj z) (map_zero _) η) hx))).differentiableAt
        (by norm_num))
  simpa only [hder, directionalDerivative] using he

/-- One actual derivative transfers to the compact test with a minus sign; support alone permits restriction to U. -/
theorem first_transfer (hη : ContDiff ℝ ∞ η)
    (hu : ∀ x ∈ U, ContDiffAt ℝ 2 u x) (hc : HasCompactSupport η)
    (hs : tsupport η ⊆ U) (v : Covector) :
    (∫ x in U, conj (η x) * directionalDerivative u v x) =
      -(∫ x in U, conj (directionalDerivative η v x) * u x) := by
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
    simp [image_eq_zero_of_notMem_tsupport (fun ht => hx (hs ht))]),
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
      have hn : x ∉ tsupport (directionalDerivative η v) :=
        fun ht => hx (hs (tsupport_fderiv_apply_subset ℝ v ht))
      simp [image_eq_zero_of_notMem_tsupport hn])]
  exact first_transfer_global hη hu hc hs v

/-- Two actual derivatives transfer with a positive sign, using only C² background regularity and no open-set premise. -/
theorem second_transfer (hη : ContDiff ℝ ∞ η)
    (hu : ∀ x ∈ U, ContDiffAt ℝ 2 u x) (hc : HasCompactSupport η)
    (hs : tsupport η ⊆ U) (v : Covector) :
    (∫ x in U, conj (η x) * secondDirectionalDerivative u v x) =
      ∫ x in U, conj (secondDirectionalDerivative η v x) * u x := by
  have hpair := integral_derivative_pair_eq_local (hη.of_le (by simp)) hu hc hs v
  have hfirst := first_transfer_global (contDiff_directional_test hη v) hu
    (hc.fderiv_apply ℝ v) ((tsupport_fderiv_apply_subset ℝ v).trans hs) v
  have he : (∫ x, conj (η x) * secondDirectionalDerivative u v x) =
      ∫ x, conj (secondDirectionalDerivative η v x) * u x :=
    neg_injective (hpair.symm.trans hfirst)
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
    simp [image_eq_zero_of_notMem_tsupport (fun ht => hx (hs ht))]),
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
      have hn : x ∉ tsupport (secondDirectionalDerivative η v) :=
        fun ht => hx (hs (tsupport_second_subset η v ht))
      simp [image_eq_zero_of_notMem_tsupport hn])]
  exact he

end FoliationQM.CompactComplexGreen
