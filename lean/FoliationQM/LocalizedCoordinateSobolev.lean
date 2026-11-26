module

public import FoliationQM.CoordinateAxisZeroExtension
public import FoliationQM.ProductTubeCoordinates
public import FoliationQM.FiniteBasisSobolevCriterion
public import FoliationQM.ActionDensity
public import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator

/-!
# Actual Sobolev membership of coordinate localizations

Source: v13 `thm:wallstrom` Part (c), component kinds C and D.
Local coordinate L² data and the compact-test weak identity imply actual
distributional derivatives of every smooth compact localization. The genuine
volume-preserving map to the Hilbert product gives standard Bessel H¹.
All three product-rule pairings are separately integrable; Lp representatives
are compared almost everywhere. No differentiability on the axis is assumed.
-/

@[expose] public section
noncomputable section

namespace FoliationQM.LocalizedCoordinateSobolev

open MeasureTheory Set RNCCoordinateConnection ProductTubeCoordinates
open scoped ContDiff Topology ENNReal SchwartzMap LineDeriv

local notation "Space" => WithLp 2 (ℂ × ℂ)

private theorem inverse_volume_preserving :
    MeasurePreserving coordinates.symm volume volume := by
  exact MeasurePreserving.symm coordinates.toHomeomorph.toMeasurableEquiv
    volume_preserving

private theorem memLp_directional {K : Set Covector} {u : Covector → ℂ}
    (hD : ∀ i : Fin 4, MemLp (fun x => fderiv ℝ u x (axis i)) 2 (volume.restrict K))
    (v : Covector) : MemLp (fun x => fderiv ℝ u x v) 2 (volume.restrict K) := by
  have hb (i : Fin 4) : (fun j : Fin 4 => if i = j then (1 : ℝ) else 0) = axis i := by
    funext j
    simp [axis, Pi.single_apply, eq_comm]
  have he (x : Covector) : fderiv ℝ u x v =
      ∑ i : Fin 4, v i • fderiv ℝ u x (axis i) := by
    simpa only [hb, ContinuousLinearMap.coe_coe] using
      LinearMap.pi_apply_eq_sum_univ (fderiv ℝ u x).toLinearMap v
  simp_rw [he]
  exact memLp_finsetSum Finset.univ (fun i _ => (hD i).const_smul (v i))

private theorem memLp_localized {K : Set Covector} {u a : Covector → ℂ}
    (hK : MeasurableSet K) (hu : MemLp u 2 (volume.restrict K))
    (ha : Continuous a) (hc : HasCompactSupport a) (hs : tsupport a ⊆ K) :
    MemLp (fun x => a x * u x) 2 volume := by
  have hi : MemLp (K.indicator u) 2 volume :=
    (memLp_indicator_iff_restrict hK.nullMeasurableSet).mpr hu
  have hp : MemLp (fun x => a x * K.indicator u x) 2 volume :=
    (ha.memLp_top_of_hasCompactSupport hc volume).fun_mul hi
  convert hp using 1
  funext x
  by_cases hx : x ∈ K
  · rw [indicator_of_mem hx]
  · rw [indicator_of_notMem hx, image_eq_zero_of_notMem_tsupport (fun h => hx (hs h))]
    simp only [zero_mul]

/-- Genuine compact-test weak derivatives give the actual L² distributional
product rule after localization and volume-preserving Hilbert coordinates. -/
theorem localized_distributional_derivative {K : Set Covector} {u η : Covector → ℂ}
    (hK : MeasurableSet K) (hu : MemLp u 2 (volume.restrict K))
    (hDu : ∀ i : Fin 4, MemLp (fun x => fderiv ℝ u x (axis i)) 2 (volume.restrict K))
    (hweak : ∀ {φ : Covector → ℂ}, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ K → ∀ v : Covector,
      Integrable (fun x => star (fderiv ℝ φ x v) * u x) volume ∧
      Integrable (fun x => star (φ x) * fderiv ℝ u x v) volume ∧
      (∫ x, star (fderiv ℝ φ x v) * u x) =
        -(∫ x, star (φ x) * fderiv ℝ u x v))
    (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η) (hsη : tsupport η ⊆ K) :
    ∃ hf : MemLp (fun y : Space => η (coordinates.symm y) * u (coordinates.symm y))
        2 volume, ∀ w : Space,
      ∃ hg : MemLp (fun y : Space =>
          fderiv ℝ η (coordinates.symm y) (coordinates.symm w) * u (coordinates.symm y) +
          η (coordinates.symm y) * fderiv ℝ u (coordinates.symm y) (coordinates.symm w))
          2 volume,
        ∂_{w} (hf.toLp _ : 𝓢'(Space, ℂ)) = (hg.toLp _ : 𝓢'(Space, ℂ)) := by
  let b : Covector → ℂ := fun x => η x * u x
  have hb : MemLp b 2 volume := memLp_localized hK hu hη.continuous hcη hsη
  have hf : MemLp (fun y : Space => b (coordinates.symm y)) 2 volume :=
    hb.comp_measurePreserving inverse_volume_preserving
  refine ⟨hf, ?_⟩
  intro w
  let v := coordinates.symm w
  let a : Covector → ℂ := fun x => fderiv ℝ η x v * u x
  let c : Covector → ℂ := fun x => η x * fderiv ℝ u x v
  have ha : MemLp a 2 volume := memLp_localized hK hu
    ((hη.continuous_fderiv_apply (by simp)).comp (continuous_id.prodMk continuous_const))
    (hcη.fderiv_apply ℝ v) ((tsupport_fderiv_apply_subset ℝ v).trans hsη)
  have hc : MemLp c 2 volume := memLp_localized hK (memLp_directional hDu v)
    hη.continuous hcη hsη
  have hg : MemLp (fun y : Space => a (coordinates.symm y) + c (coordinates.symm y))
      2 volume := (ha.add hc).comp_measurePreserving inverse_volume_preserving
  refine ⟨hg, ?_⟩
  ext Φ
  have hΦ : MemLp (fun x => Φ (coordinates x)) 2 volume :=
    (Φ.memLp 2 volume).comp_measurePreserving volume_preserving
  have hdΦ : MemLp (fun x => (∂_{w} Φ) (coordinates x)) 2 volume :=
    ((∂_{w} Φ).memLp 2 volume).comp_measurePreserving volume_preserving
  have hA : Integrable (fun x => a x * Φ (coordinates x)) volume := ha.integrable_mul hΦ
  have hB : Integrable (fun x => b x * (∂_{w} Φ) (coordinates x)) volume := hb.integrable_mul hdΦ
  have hC : Integrable (fun x => c x * Φ (coordinates x)) volume := hc.integrable_mul hΦ
  let t : Covector → ℂ := fun x => η x * Φ (coordinates x)
  have ht : ContDiff ℝ ∞ t := hη.mul ((Φ.smooth ⊤).comp coordinates.contDiff)
  have hct : HasCompactSupport t := hcη.mul_right
  have hst : tsupport t ⊆ K := tsupport_mul_subset_left.trans hsη
  have hstar : ContDiff ℝ ∞ (fun x => star (t x)) := by
    simpa only [Function.comp_def, Complex.conjCLE_apply, starRingEnd_apply] using
      Complex.conjCLE.contDiff.comp ht
  have hcstar : HasCompactSupport (fun x => star (t x)) :=
    hct.comp_left (g := fun z : ℂ => star z) (by simp)
  have hsstar : tsupport (fun x => star (t x)) ⊆ K :=
    (tsupport_comp_subset (g := fun z : ℂ => star z) (by simp) t).trans hst
  have hd (x : Covector) : fderiv ℝ (fun y => star (t y)) x v =
      star (fderiv ℝ η x v * Φ (coordinates x) + η x * (∂_{w} Φ) (coordinates x)) := by
    have he : fderiv ℝ (fun y => star (t y)) x v = star (fderiv ℝ t x v) := by
      simpa only [starRingEnd_apply] using
        ActionDensity.fderiv_conj_apply (ht.differentiable (by simp) x) v
    rw [he]
    congr 1
    have hpull : HasFDerivAt (fun y => Φ (coordinates y))
        ((fderiv ℝ Φ (coordinates x)).comp coordinates.toContinuousLinearMap) x := by
      simpa only [Function.comp_def, ContinuousLinearEquiv.coe_coe] using
        (Φ.hasFDerivAt (coordinates x)).comp x coordinates.hasFDerivAt
    have hprod := (hη.differentiable (by simp) x).hasFDerivAt.mul hpull
    change fderiv ℝ (η * (fun y => Φ (coordinates y))) x v = _
    rw [hprod.fderiv]
    simp only [add_apply, smul_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      v, ContinuousLinearEquiv.apply_symm_apply, SchwartzMap.lineDerivOp_apply_eq_fderiv,
      smul_eq_mul]
    ring
  have hi : (∫ x, a x * Φ (coordinates x)) +
      (∫ x, b x * (∂_{w} Φ) (coordinates x)) = -(∫ x, c x * Φ (coordinates x)) := by
    calc
      _ = ∫ x, a x * Φ (coordinates x) + b x * (∂_{w} Φ) (coordinates x) :=
        (integral_add hA hB).symm
      _ = ∫ x, star (fderiv ℝ (fun y => star (t y)) x v) * u x := by
        apply integral_congr_ae
        filter_upwards with x
        rw [hd]
        simp only [star_star]
        dsimp [a, b]
        ring
      _ = -(∫ x, star (star (t x)) * fderiv ℝ u x v) :=
        (hweak hstar hcstar hsstar v).2.2
      _ = -(∫ x, c x * Φ (coordinates x)) := by
        congr 1
        apply integral_congr_ae
        filter_upwards with x
        simp only [star_star]
        dsimp [t, c]
        ring
  have hp : -(∫ x, (∂_{w} Φ) (coordinates x) * b x) =
      ∫ x, Φ (coordinates x) * (a x + c x) := by
    have hr : -(∫ x, b x * (∂_{w} Φ) (coordinates x)) =
        (∫ x, a x * Φ (coordinates x)) + (∫ x, c x * Φ (coordinates x)) := by
      linear_combination -hi
    calc
      _ = -(∫ x, b x * (∂_{w} Φ) (coordinates x)) := by simp only [mul_comm]
      _ = _ := hr
      _ = ∫ x, a x * Φ (coordinates x) + c x * Φ (coordinates x) :=
        (integral_add hA hC).symm
      _ = _ := integral_congr_ae (Filter.Eventually.of_forall (fun x => by ring))
  calc
    _ = ∫ y, (-∂_{w} Φ) y * hf.toLp _ y := by
      rw [TemperedDistribution.lineDerivOp_apply_apply, Lp.toTemperedDistribution_apply]
      rfl
    _ = -(∫ y, (∂_{w} Φ) y * b (coordinates.symm y)) := by
      rw [← integral_neg]
      apply integral_congr_ae
      filter_upwards [hf.coeFn_toLp] with y hy
      simp only [neg_apply, hy, neg_mul]
    _ = -(∫ x, (∂_{w} Φ) (coordinates x) * b x) := by
      congr 1
      simpa only [ContinuousLinearEquiv.symm_apply_apply] using
        (volume_preserving.integral_comp
          coordinates.toHomeomorph.toMeasurableEquiv.measurableEmbedding
          (fun y => (∂_{w} Φ) y * b (coordinates.symm y))).symm
    _ = ∫ x, Φ (coordinates x) * (a x + c x) := hp
    _ = ∫ y, Φ y * (a (coordinates.symm y) + c (coordinates.symm y)) := by
      simpa only [ContinuousLinearEquiv.symm_apply_apply] using
        volume_preserving.integral_comp
          coordinates.toHomeomorph.toMeasurableEquiv.measurableEmbedding
          (fun y => Φ y * (a (coordinates.symm y) + c (coordinates.symm y)))
    _ = (hg.toLp _ : 𝓢'(Space, ℂ)) Φ := by
      rw [Lp.toTemperedDistribution_apply]
      apply integral_congr_ae
      filter_upwards [hg.coeFn_toLp] with y hy
      simp only [smul_eq_mul, hy]

/-- Every smooth compact localization of genuine local L² weak data belongs
to the actual Hilbert-domain Bessel H¹ space. -/
theorem localized_memSobolev {K : Set Covector} {u η : Covector → ℂ}
    (hK : MeasurableSet K) (hu : MemLp u 2 (volume.restrict K))
    (hDu : ∀ i : Fin 4, MemLp (fun x => fderiv ℝ u x (axis i)) 2 (volume.restrict K))
    (hweak : ∀ {φ : Covector → ℂ}, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ K → ∀ v : Covector,
      Integrable (fun x => star (fderiv ℝ φ x v) * u x) volume ∧
      Integrable (fun x => star (φ x) * fderiv ℝ u x v) volume ∧
      (∫ x, star (fderiv ℝ φ x v) * u x) =
        -(∫ x, star (φ x) * fderiv ℝ u x v))
    (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η) (hsη : tsupport η ⊆ K) :
    ∃ hf : MemLp (fun y : Space => η (coordinates.symm y) * u (coordinates.symm y))
        2 volume, TemperedDistribution.MemSobolev 1 2 (hf.toLp _ : 𝓢'(Space, ℂ)) := by
  obtain ⟨hf, hd⟩ := localized_distributional_derivative hK hu hDu hweak hη hcη hsη
  refine ⟨hf, ?_⟩
  let basis := stdOrthonormalBasis ℝ Space
  choose hg he using fun i => hd (basis i)
  exact FiniteBasisSobolevCriterion.memSobolev_one_of_lp_derivatives basis
    (hf.toLp _) (fun i => (hg i).toLp _) he

end FoliationQM.LocalizedCoordinateSobolev
