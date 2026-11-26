module

public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Tactic

/-!
# A smooth logarithmic radial cutoff

Source: v13 `eq:log_cutoff_wallstrom`, component kinds C and D. The fixed
smooth transition replaces the raw logarithmic ramp while retaining its exact
zero and one plateaus. Actual global smoothness includes the origin and both
positive junctions. Uniform derivative bounds, energy and geometry are separate.
-/

@[expose] public section
noncomputable section

namespace FoliationQM.SmoothLogarithmicCutoffProfile

open Filter Set
open scoped Topology ContDiff

/-- The fixed smooth transition of the logarithmic radius, extended by zero at nonpositive radii. -/
def profile (ε r : ℝ) : ℝ :=
  if r ≤ 0 then 0 else Real.smoothTransition (Real.log (r / ε ^ 2) / |Real.log ε|)

private theorem log_upper {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1) :
    Real.log (ε / ε ^ 2) = |Real.log ε| := by
  rw [Real.log_div h0.ne' (pow_ne_zero 2 h0.ne'), Real.log_pow,
    abs_of_neg (Real.log_neg h0 h1)]
  ring

/-- For 0 < ε < 1, the smooth profile is zero below ε², one above ε, and between zero and one at every real radius. -/
theorem profile_spec {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1) :
    (∀ r, r ≤ ε ^ 2 → profile ε r = 0) ∧
    (∀ r, ε ≤ r → profile ε r = 1) ∧
    ∀ r, 0 ≤ profile ε r ∧ profile ε r ≤ 1 := by
  have hs0 : 0 < ε ^ 2 := sq_pos_of_pos h0
  have hL : 0 < |Real.log ε| := abs_pos.mpr (Real.log_neg h0 h1).ne
  refine ⟨?_, ?_, ?_⟩
  · intro r hr
    by_cases hr0 : r ≤ 0
    · simp only [profile, ite_eq_left hr0]
    have hrpos : 0 < r := lt_of_not_ge hr0
    have hlog : Real.log (r / ε ^ 2) ≤ 0 := Real.log_nonpos
      (div_nonneg hrpos.le hs0.le) ((div_le_one hs0).mpr hr)
    simp only [profile, ite_eq_right hr0]
    exact Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg hlog hL.le)
  · intro r hr
    have hrpos : 0 < r := h0.trans_le hr
    have hlog : |Real.log ε| ≤ Real.log (r / ε ^ 2) := by
      rw [← log_upper h0 h1]
      exact Real.log_le_log (div_pos h0 hs0) (div_le_div_of_nonneg_right hr hs0.le)
    simp only [profile, ite_eq_right (not_le.mpr hrpos)]
    exact Real.smoothTransition.one_of_one_le ((one_le_div hL).mpr hlog)
  · intro r
    by_cases hr : r ≤ 0
    · simp [profile, hr]
    simp only [profile, ite_eq_right hr]
    exact ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

/-- The actual smooth profile is infinitely differentiable on the whole real line, including the origin and both positive junctions. -/
theorem contDiff_profile {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1) :
    ContDiff ℝ ∞ (profile ε) := by
  apply contDiff_iff_contDiffAt.mpr
  intro r
  by_cases hr : 0 < r
  · have hi : ContDiffAt ℝ ∞ (fun y : ℝ => Real.log (y / ε ^ 2) / |Real.log ε|) r :=
      ((contDiffAt_id.div_const (ε ^ 2)).log
        (div_ne_zero hr.ne' (pow_ne_zero 2 h0.ne'))).div_const _
    have hc := Real.smoothTransition.contDiffAt.comp r hi
    apply hc.congr_of_eventuallyEq
    filter_upwards [eventually_gt_nhds hr] with y hy
    simp only [profile, ite_eq_right (not_le.mpr hy), Function.comp_apply]
  · have hrlt : r < ε ^ 2 := (le_of_not_gt hr).trans_lt (sq_pos_of_pos h0)
    apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
    filter_upwards [eventually_lt_nhds hrlt] with y hy
    exact (profile_spec h0 h1).1 y hy.le

/-- At every positive radius, including both junctions, the actual derivative is the fixed transition derivative divided by r times the absolute logarithm. -/
theorem hasDerivAt_profile {ε r : ℝ} (h0 : 0 < ε) (h1 : ε < 1) (hr : 0 < r) :
    HasDerivAt (profile ε)
      (deriv Real.smoothTransition (Real.log (r / ε ^ 2) / |Real.log ε|) /
        (r * |Real.log ε|)) r := by
  have hL : |Real.log ε| ≠ 0 := abs_ne_zero.mpr (Real.log_neg h0 h1).ne
  have hi := (((hasDerivAt_id r).div_const (ε ^ 2)).log
    (div_ne_zero hr.ne' (pow_ne_zero 2 h0.ne'))).div_const |Real.log ε|
  simp only [id_eq] at hi
  have he : (1 / ε ^ 2 / (r / ε ^ 2)) / |Real.log ε| =
      1 / (r * |Real.log ε|) := by
    field_simp [h0.ne', hr.ne', hL]
  rw [he] at hi
  have ht := ((Real.smoothTransition.contDiff (n := 1)).differentiable_one
    (Real.log (r / ε ^ 2) / |Real.log ε|)).hasDerivAt
  have hd := ht.comp r hi
  simp only [mul_one_div] at hd
  apply hd.congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds hr] with y hy
  simp only [profile, ite_eq_right (not_le.mpr hy), Function.comp_apply]

/-- The support of the actual scalar derivative lies in the closed transition annulus; outside it the profile is locally constant. -/
theorem support_deriv_subset {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1) :
    Function.support (deriv (profile ε)) ⊆ Icc (ε ^ 2) ε := by
  intro r hr
  change deriv (profile ε) r ≠ 0 at hr
  by_contra hmem
  apply hr
  by_cases hlo : r < ε ^ 2
  · have hd : HasDerivAt (profile ε) 0 r := by
      apply (hasDerivAt_const r (0 : ℝ)).congr_of_eventuallyEq
      filter_upwards [eventually_lt_nhds hlo] with y hy
      exact (profile_spec h0 h1).1 y hy.le
    exact hd.deriv
  · have hhi : ε < r := lt_of_not_ge (fun h => hmem ⟨le_of_not_gt hlo, h⟩)
    have hd : HasDerivAt (profile ε) 0 r := by
      apply (hasDerivAt_const r (1 : ℝ)).congr_of_eventuallyEq
      filter_upwards [eventually_gt_nhds hhi] with y hy
      exact (profile_spec h0 h1).2.1 y hy.le
    exact hd.deriv

/-- At any fixed positive radius the actual smooth cutoff is eventually exactly one as ε tends to zero through positive values. -/
theorem eventually_profile_eq_one {r : ℝ} (hr : 0 < r) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), profile ε r = 1 := by
  filter_upwards [self_mem_nhdsWithin,
    nhdsWithin_le_nhds (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num)),
    nhdsWithin_le_nhds (eventually_lt_nhds hr)] with ε h0 h1 hε
  exact (profile_spec h0 h1).2.1 r hε.le

end FoliationQM.SmoothLogarithmicCutoffProfile
