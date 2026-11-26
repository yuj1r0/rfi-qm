module

public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Topology.Piecewise
public import Mathlib.Topology.Order.OrderClosed
public import Mathlib.Tactic

/-!
# The literal logarithmic radial cutoff

Source: v13 `eq:log_cutoff_wallstrom`, component kinds C and D. The raw
piecewise profile is continuous, bounded between zero and one, and has its
actual logarithmic derivative on the open transition interval. Derivatives
at the two junctions, a smooth replacement and tubular geometry are separate.
-/

@[expose] public section
noncomputable section

namespace FoliationQM.LogarithmicCutoffProfile

open Filter Set
open scoped Topology

/-- The literal radial profile: zero below ε², logarithmic between ε² and ε, and one above ε when 0 < ε < 1. -/
def profile (ε r : ℝ) : ℝ :=
  if r ≤ ε ^ 2 then 0 else if r < ε then Real.log (r / ε ^ 2) / |Real.log ε| else 1

private theorem log_upper {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1) :
    Real.log (ε / ε ^ 2) = |Real.log ε| := by
  rw [Real.log_div h0.ne' (pow_ne_zero 2 h0.ne'), Real.log_pow,
    abs_of_neg (Real.log_neg h0 h1)]
  ring

/-- For 0 < ε < 1, the three literal region values hold and the actual profile stays between zero and one at every real radius. -/
theorem profile_spec {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1) :
    (∀ r, r ≤ ε ^ 2 → profile ε r = 0) ∧
    (∀ r, ε ^ 2 < r → r < ε → profile ε r = Real.log (r / ε ^ 2) / |Real.log ε|) ∧
    (∀ r, ε ≤ r → profile ε r = 1) ∧
    ∀ r, 0 ≤ profile ε r ∧ profile ε r ≤ 1 := by
  have hs : ε ^ 2 < ε := by
    simpa only [pow_two, mul_one] using mul_lt_mul_of_pos_left h1 h0
  have hs0 : 0 < ε ^ 2 := sq_pos_of_pos h0
  have hL : 0 < |Real.log ε| := abs_pos.mpr (Real.log_neg h0 h1).ne
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro r hr
    simp only [profile, ite_eq_left hr]
  · intro r hr0 hr1
    simp only [profile, ite_eq_right (not_le.mpr hr0), ite_eq_left hr1]
  · intro r hr
    simp only [profile, ite_eq_right (not_le.mpr (hs.trans_le hr)), ite_eq_right (not_lt.mpr hr)]
  · intro r
    by_cases hr0 : r ≤ ε ^ 2
    · simp [profile, hr0]
    by_cases hr1 : r < ε
    · have hr : 0 < r := hs0.trans (lt_of_not_ge hr0)
      have hlo : 0 ≤ Real.log (r / ε ^ 2) :=
        Real.log_nonneg ((le_div_iff₀ hs0).mpr (by simpa using (le_of_not_ge hr0)))
      have hup : Real.log (r / ε ^ 2) ≤ |Real.log ε| := by
        rw [← log_upper h0 h1]
        exact Real.log_le_log (div_pos hr hs0)
          (div_le_div_of_nonneg_right hr1.le hs0.le)
      simp only [profile, ite_eq_right hr0, ite_eq_left hr1]
      exact ⟨div_nonneg hlo hL.le, (div_le_one hL).mpr hup⟩
    · simp [profile, hr0, hr1]

/-- The actual piecewise profile is continuous on the whole real line, including both logarithmic junctions. -/
theorem continuous_profile {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1) :
    Continuous (profile ε) := by
  have hs : ε ^ 2 < ε := by
    simpa only [pow_two, mul_one] using mul_lt_mul_of_pos_left h1 h0
  have hs0 : 0 < ε ^ 2 := sq_pos_of_pos h0
  have hL : |Real.log ε| ≠ 0 := abs_ne_zero.mpr (Real.log_neg h0 h1).ne
  have hl : ContinuousOn (fun r : ℝ => Real.log (r / ε ^ 2) / |Real.log ε|)
      {r | ε ^ 2 ≤ r} := by
    intro r hr
    have hr0 : r / ε ^ 2 ≠ 0 := div_ne_zero (ne_of_gt (hs0.trans_le hr)) hs0.ne'
    exact (((continuousAt_id.div_const (ε ^ 2)).log hr0).div_const _).continuousWithinAt
  have hi : ContinuousOn
      (fun r : ℝ => if r < ε then Real.log (r / ε ^ 2) / |Real.log ε| else 1)
      {r | ε ^ 2 ≤ r} := by
    apply ContinuousOn.if
    · intro r hr
      have he : r = ε := frontier_lt_subset_eq continuous_id continuous_const hr.2
      subst r
      exact (div_eq_one_iff_eq hL).mpr (log_upper h0 h1)
    · exact hl.mono inter_subset_left
    · exact continuousOn_const
  change Continuous (fun r : ℝ => if r ≤ ε ^ 2 then 0 else
    if r < ε then Real.log (r / ε ^ 2) / |Real.log ε| else 1)
  apply continuous_if_le continuous_id continuous_const continuousOn_const hi
  intro r hr
  change r = ε ^ 2 at hr
  subst r
  simp only [ite_eq_left hs, div_self hs0.ne', Real.log_one, zero_div]

/-- Away from the two junctions, the actual derivative is 1/(r |log ε|) on the open transition interval and zero on the two constant regions. -/
theorem hasDerivAt_profile {ε r : ℝ} (h0 : 0 < ε) (h1 : ε < 1)
    (hne0 : r ≠ ε ^ 2) (hne1 : r ≠ ε) :
    HasDerivAt (profile ε)
      (if ε ^ 2 < r ∧ r < ε then 1 / (r * |Real.log ε|) else 0) r := by
  have hs : ε ^ 2 < ε := by
    simpa only [pow_two, mul_one] using mul_lt_mul_of_pos_left h1 h0
  by_cases hr0 : r < ε ^ 2
  · rw [ite_eq_right (fun h => (not_lt_of_ge hr0.le) h.1)]
    apply (hasDerivAt_const r (0 : ℝ)).congr_of_eventuallyEq
    filter_upwards [eventually_lt_nhds hr0] with y hy
    simp only [profile, ite_eq_left hy.le]
  have hr0' : ε ^ 2 < r := lt_of_le_of_ne (le_of_not_gt hr0) hne0.symm
  by_cases hr1 : r < ε
  · rw [ite_eq_left ⟨hr0', hr1⟩]
    have hs0 : ε ^ 2 ≠ 0 := pow_ne_zero 2 h0.ne'
    have hr : r ≠ 0 := ne_of_gt ((sq_pos_of_pos h0).trans hr0')
    have hd := (((hasDerivAt_id r).div_const (ε ^ 2)).log
      (div_ne_zero hr hs0)).div_const |Real.log ε|
    have he : (1 / ε ^ 2 / (r / ε ^ 2)) / |Real.log ε| =
        1 / (r * |Real.log ε|) := by
      field_simp
    simp only [id_eq] at hd
    rw [he] at hd
    apply hd.congr_of_eventuallyEq
    filter_upwards [eventually_gt_nhds hr0', eventually_lt_nhds hr1] with y hy0 hy1
    simp only [profile, ite_eq_right (not_le.mpr hy0), ite_eq_left hy1]
  · rw [ite_eq_right (not_and.mpr (fun _ => hr1))]
    have hr1' : ε < r := lt_of_le_of_ne (le_of_not_gt hr1) hne1.symm
    apply (hasDerivAt_const r (1 : ℝ)).congr_of_eventuallyEq
    filter_upwards [eventually_gt_nhds hr1'] with y hy
    simp only [profile, ite_eq_right (not_le.mpr (hs.trans hy)), ite_eq_right (not_lt.mpr hy.le)]

/-- At each fixed positive radius the actual profile is eventually exactly one as ε tends to zero through positive values. -/
theorem eventually_profile_eq_one {r : ℝ} (hr : 0 < r) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), profile ε r = 1 := by
  filter_upwards [self_mem_nhdsWithin,
    nhdsWithin_le_nhds (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num)),
    nhdsWithin_le_nhds (eventually_lt_nhds hr)] with ε h0 h1 hε
  exact (profile_spec h0 h1).2.2.1 r hε.le

end FoliationQM.LogarithmicCutoffProfile
