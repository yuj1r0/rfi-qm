module

public import FoliationQM.CoordinateCutoffTests
public import Mathlib.MeasureTheory.Function.Jacobian

/-!
# Compact tests away from a nodal set in an adapted chart

Source: v13 `thm:wallstrom` Part(c), the tests `χ_ε φ` following
`eq:log_cutoff_l2_bound`, component kinds C and D. For a smooth coordinate
chart `e`, the logarithmic cutoff is composed with the chart and multiplied
into a smooth compact test whose closed support lies in the chart source.
The product is globally smooth with compact support, its closed support avoids
every point the chart sends to the coordinate axis, and its differential is
the expected two-term sum. The set sent to the axis has zero volume.

The cutoff depends on the coordinate normal radius in the chart, not on the
auxiliary-metric normal distance of the source.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.AdaptedChartCutoffTests

open Filter MeasureTheory Set ProductTubeCoordinates SmoothCoordinateTubeCutoff RealLorentzFrame
open scoped ContDiff Topology

variable {e : OpenPartialHomeomorph Covector Covector} {ε : ℝ} {φ : Covector → ℂ}
  {x : Covector}

/-- The smooth logarithmic cutoff read through a coordinate chart. -/
def cutoff (e : OpenPartialHomeomorph Covector Covector) (ε : ℝ) : Covector → ℝ :=
  profile ε ∘ e

/-- A complex test multiplied by the chart cutoff. -/
def test (e : OpenPartialHomeomorph Covector Covector) (ε : ℝ) (φ : Covector → ℂ)
    (x : Covector) : ℂ :=
  cutoff e ε x • φ x

/-- The chart cutoff is smooth on the chart source. -/
theorem contDiffOn_cutoff (he : ContDiffOn ℝ ∞ e e.source) (h0 : 0 < ε) (h1 : ε < 1) :
    ContDiffOn ℝ ∞ (cutoff e ε) e.source :=
  (contDiff_profile h0 h1).comp_contDiffOn he

/-- The chart cutoff takes values in the unit interval. -/
theorem cutoff_mem_Icc (h0 : 0 < ε) (h1 : ε < 1) (x : Covector) :
    0 ≤ cutoff e ε x ∧ cutoff e ε x ≤ 1 :=
  (profile_spec h0 h1).2.2 (e x)

/-- Away from the points sent to the axis, the cutoff is eventually exactly one. -/
theorem eventually_cutoff_eq_one (hx : ¬ ((e x) 2 = 0 ∧ (e x) 3 = 0)) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), cutoff e ε x = 1 :=
  eventually_profile_eq_one hx

/-- The part of the chart source sent to the coordinate axis has zero volume. -/
theorem volume_axis_preimage (hi : ContDiffOn ℝ 1 e.symm e.target) :
    volume {x | x ∈ e.source ∧ (e x) 2 = 0 ∧ (e x) 3 = 0} = 0 := by
  have hdiff : DifferentiableOn ℝ e.symm (e.target ∩ {v | v 2 = 0 ∧ v 3 = 0}) :=
    (hi.differentiableOn one_ne_zero).mono inter_subset_left
  have hnull : volume (e.target ∩ {v : Covector | v 2 = 0 ∧ v 3 = 0}) = 0 :=
    measure_mono_null inter_subset_right axis_null
  refine measure_mono_null ?_
    (addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume hdiff hnull)
  rintro y ⟨hys, hy⟩
  exact ⟨e y, ⟨e.map_source hys, hy⟩, e.left_inv hys⟩

/-- The cut-off test is globally smooth with compact support inside the original
support, and its closed support contains no point sent to the coordinate axis. -/
theorem test_data (h0 : 0 < ε) (h1 : ε < 1) (he : ContDiffOn ℝ ∞ e e.source)
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ e.source) :
    ContDiff ℝ ∞ (test e ε φ) ∧ HasCompactSupport (test e ε φ) ∧
    tsupport (test e ε φ) ⊆ tsupport φ ∧
    ∀ y ∈ tsupport (test e ε φ), ¬ ((e y) 2 = 0 ∧ (e y) 3 = 0) := by
  have hsub : tsupport (test e ε φ) ⊆ tsupport φ :=
    tsupport_smul_subset_right (cutoff e ε) φ
  refine ⟨contDiff_iff_contDiffAt.2 fun y => ?_, ?_, hsub, ?_⟩
  · by_cases hy : y ∈ tsupport φ
    · exact ((contDiffOn_cutoff he h0 h1).contDiffAt (e.open_source.mem_nhds (hs hy))).smul
        hφ.contDiffAt
    · have hz : test e ε φ =ᶠ[𝓝 y] fun _ => 0 :=
        (notMem_tsupport_iff_eventuallyEq.mp hy).mono fun z hz => by
          simp only [test, hz, Pi.zero_apply, smul_zero]
      exact contDiffAt_const.congr_of_eventuallyEq hz
  · change HasCompactSupport (cutoff e ε • φ)
    exact hc.smul_left
  · intro y hy ha
    have hys : y ∈ e.source := hs (hsub hy)
    have hr : Continuous (fun z : Covector => ‖(coordinates z).snd‖) :=
      ((WithLp.sndL 2 ℝ ℂ ℂ).continuous.comp coordinates.continuous).norm
    have hz : (coordinates (e y)).snd = 0 :=
      show e y ∈ coordinates ⁻¹' {w : WithLp 2 (ℂ × ℂ) | w.snd = 0} from
        axis_preimage.symm ▸ ha
    have hlt : ‖(coordinates (e y)).snd‖ < ε ^ 2 := by
      rw [hz, norm_zero]
      exact sq_pos_of_pos h0
    have hev : ∀ᶠ z in 𝓝 y, ‖(coordinates (e z)).snd‖ < ε ^ 2 :=
      (hr.continuousAt.comp (e.continuousAt hys)).eventually (Iio_mem_nhds hlt)
    have hzero : test e ε φ =ᶠ[𝓝 y] 0 := hev.mono fun z hz => by
      have hp : profile ε (e z) = 0 := (profile_spec h0 h1).1 (e z) hz.le
      simp only [test, cutoff, Function.comp_apply, hp, zero_smul, Pi.zero_apply]
    exact (notMem_tsupport_iff_eventuallyEq.mpr hzero) hy

/-- On the chart source the directional derivative of the cut-off test is the
cutoff-derivative term plus the cut-off original derivative. -/
theorem directional_test (h0 : 0 < ε) (h1 : ε < 1) (he : ContDiffOn ℝ ∞ e e.source)
    (hx : x ∈ e.source) (hφ : DifferentiableAt ℝ φ x) (v : Covector) :
    fderiv ℝ (test e ε φ) x v =
      fderiv ℝ (cutoff e ε) x v • φ x + cutoff e ε x • fderiv ℝ φ x v := by
  have hχ : DifferentiableAt ℝ (cutoff e ε) x :=
    ((contDiffOn_cutoff he h0 h1).contDiffAt (e.open_source.mem_nhds hx)).differentiableAt
      (by simp)
  change fderiv ℝ (fun y => cutoff e ε y • φ y) x v = _
  rw [fderiv_fun_smul hχ hφ]
  simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply, add_comm]

end FoliationQM.AdaptedChartCutoffTests
