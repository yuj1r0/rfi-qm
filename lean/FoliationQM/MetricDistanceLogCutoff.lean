module

public import FoliationQM.LogarithmicCutoffProfile
public import Mathlib.Topology.MetricSpace.HausdorffDistance
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# The logarithmic cutoff as a function of the distance to the nodal set

Source: v13 `eq:log_cutoff_wallstrom` and the pointwise bound of
`eq:log_cutoff_l2_bound`, "`|dχ_ε|_h ≤ C / (r |ln ε|)`" with
`r = dist_h(x, 𝒩)`, component kinds C and D. In any metric space, in
particular a manifold with the distance of an auxiliary Riemannian metric,
the literal cutoff `χ_ε(x) = χ_ε(dist(x, 𝒩))` has the three region values of
the source display, takes values in `[0, 1]`, is continuous, vanishes on a
neighbourhood of the closure of `𝒩`, equals one at each point at positive
distance once `ε` is small, and satisfies

`|χ_ε(x) - χ_ε(y)| ≤ dist(x, y) / (r |ln ε|)`

whenever both points are at distance at least `r > 0` from `𝒩`. This is the
metric form of the pointwise gradient bound, with constant one.

The cutoff is Lipschitz, not smooth. Its differential, the volume of the
tubular shells and the resulting `L²` estimate in distance form are not
addressed; the smooth cutoffs used in the proofs of the weak identities are
functions of the normal radius of adapted charts.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.MetricDistanceLogCutoff

open Filter Set Metric LogarithmicCutoffProfile
open scoped Topology

/-- The logarithm is `1/ρ`-Lipschitz on `[ρ, ∞)`. -/
theorem abs_log_sub_log_le {a b ρ : ℝ} (hρ : 0 < ρ) (ha : ρ ≤ a) (hb : ρ ≤ b) :
    |Real.log a - Real.log b| ≤ |a - b| / ρ := by
  have key : ∀ {u v : ℝ}, ρ ≤ v → v ≤ u → |Real.log u - Real.log v| ≤ |u - v| / ρ := by
    intro u v hv huv
    have hv0 : 0 < v := hρ.trans_le hv
    have hu0 : 0 < u := hv0.trans_le huv
    have h1 : 0 ≤ Real.log u - Real.log v := sub_nonneg.mpr (Real.log_le_log hv0 huv)
    rw [abs_of_nonneg h1, abs_of_nonneg (sub_nonneg.mpr huv), ← Real.log_div hu0.ne' hv0.ne']
    calc Real.log (u / v) ≤ u / v - 1 := Real.log_le_sub_one_of_pos (div_pos hu0 hv0)
      _ = (u - v) / v := by field_simp
      _ ≤ (u - v) / ρ := div_le_div_of_nonneg_left (sub_nonneg.mpr huv) hρ hv
  rcases le_total b a with h | h
  · exact key hb h
  · rw [abs_sub_comm, abs_sub_comm a b]
    exact key ha h

variable {ε : ℝ}

/-- At positive radius the literal profile is the logarithmic ramp clamped to
`[0, 1]`. -/
theorem profile_eq_clamp (h0 : 0 < ε) (h1 : ε < 1) {r : ℝ} (hr : 0 < r) :
    profile ε r = max 0 (min 1 (Real.log (r / ε ^ 2) / |Real.log ε|)) := by
  have hs0 : 0 < ε ^ 2 := sq_pos_of_pos h0
  have hL : 0 < |Real.log ε| := abs_pos.mpr (Real.log_neg h0 h1).ne
  obtain ⟨hz, hm, ho, hrange⟩ := profile_spec h0 h1
  by_cases hr0 : r ≤ ε ^ 2
  · have hq : Real.log (r / ε ^ 2) / |Real.log ε| ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg
        (Real.log_nonpos (div_pos hr hs0).le ((div_le_one hs0).mpr hr0)) hL.le
    rw [hz r hr0, min_eq_right (hq.trans zero_le_one), max_eq_left hq]
  by_cases hr1 : r < ε
  · have hval := hm r (lt_of_not_ge hr0) hr1
    have hb := hrange r
    rw [hval] at hb ⊢
    rw [min_eq_right hb.2, max_eq_right hb.1]
  · have hre : ε ≤ r := le_of_not_gt hr1
    have hup : Real.log (ε / ε ^ 2) = |Real.log ε| := by
      rw [Real.log_div h0.ne' (pow_ne_zero 2 h0.ne'), Real.log_pow,
        abs_of_neg (Real.log_neg h0 h1)]
      push_cast
      ring
    have hq : 1 ≤ Real.log (r / ε ^ 2) / |Real.log ε| := by
      rw [le_div_iff₀ hL, one_mul, ← hup]
      exact Real.log_le_log (div_pos h0 hs0) (div_le_div_of_nonneg_right hre hs0.le)
    rw [ho r hre, min_eq_left hq, max_eq_right zero_le_one]

/-- The profile has slope at most `1 / (ρ |ln ε|)` on `[ρ, ∞)`. -/
theorem abs_profile_sub_le (h0 : 0 < ε) (h1 : ε < 1) {a b ρ : ℝ} (hρ : 0 < ρ) (ha : ρ ≤ a)
    (hb : ρ ≤ b) : |profile ε a - profile ε b| ≤ |a - b| / (ρ * |Real.log ε|) := by
  have hs0 : 0 < ε ^ 2 := sq_pos_of_pos h0
  have hL : 0 < |Real.log ε| := abs_pos.mpr (Real.log_neg h0 h1).ne
  have ha0 : 0 < a := hρ.trans_le ha
  have hb0 : 0 < b := hρ.trans_le hb
  rw [profile_eq_clamp h0 h1 ha0, profile_eq_clamp h0 h1 hb0]
  have hclamp : ∀ u v : ℝ, |max 0 (min 1 u) - max 0 (min 1 v)| ≤ |u - v| := by
    intro u v
    rw [max_comm 0, max_comm 0]
    refine (abs_max_sub_max_le_abs _ _ _).trans ?_
    refine (abs_min_sub_min_le_max 1 u 1 v).trans ?_
    simp
  refine (hclamp _ _).trans ?_
  rw [← sub_div, abs_div, abs_abs, Real.log_div ha0.ne' hs0.ne', Real.log_div hb0.ne' hs0.ne',
    sub_sub_sub_cancel_right, div_le_div_iff₀ hL (mul_pos hρ hL)]
  have h := abs_log_sub_log_le hρ ha hb
  rw [le_div_iff₀ hρ] at h
  nlinarith [abs_nonneg (a - b)]

variable {X : Type*} [PseudoMetricSpace X] {N : Set X}

/-- The logarithmic cutoff as a function of the distance to a set. -/
def cutoff (N : Set X) (ε : ℝ) (x : X) : ℝ := profile ε (infDist x N)

/-- The three region values of the source display, and the range. -/
theorem cutoff_spec (h0 : 0 < ε) (h1 : ε < 1) (x : X) :
    (infDist x N ≤ ε ^ 2 → cutoff N ε x = 0) ∧
    (ε ^ 2 < infDist x N → infDist x N < ε →
      cutoff N ε x = Real.log (infDist x N / ε ^ 2) / |Real.log ε|) ∧
    (ε ≤ infDist x N → cutoff N ε x = 1) ∧ 0 ≤ cutoff N ε x ∧ cutoff N ε x ≤ 1 :=
  ⟨(profile_spec h0 h1).1 _, (profile_spec h0 h1).2.1 _, (profile_spec h0 h1).2.2.1 _,
    (profile_spec h0 h1).2.2.2 _⟩

/-- The distance cutoff is continuous. -/
theorem continuous_cutoff (h0 : 0 < ε) (h1 : ε < 1) : Continuous (cutoff N ε) :=
  (continuous_profile h0 h1).comp (continuous_infDist_pt N)

/-- The distance cutoff vanishes on a neighbourhood of every point of the
closure of the set. -/
theorem eventually_cutoff_eq_zero (h0 : 0 < ε) (h1 : ε < 1) {x : X} (hx : x ∈ closure N) :
    ∀ᶠ y in 𝓝 x, cutoff N ε y = 0 := by
  have hzero : infDist x N = 0 := infDist_zero_of_mem_closure hx
  have hc : ContinuousAt (fun y => infDist y N) x := (continuous_infDist_pt N).continuousAt
  have hev : ∀ᶠ y in 𝓝 x, infDist y N < ε ^ 2 :=
    hc.eventually (gt_mem_nhds (by show infDist x N < ε ^ 2; rw [hzero]; exact sq_pos_of_pos h0))
  filter_upwards [hev] with y hy
  exact (profile_spec h0 h1).1 _ hy.le

/-- At a point at positive distance the cutoff is eventually one as `ε → 0`. -/
theorem eventually_cutoff_eq_one {x : X} (hx : 0 < infDist x N) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), cutoff N ε x = 1 :=
  eventually_profile_eq_one hx

/-- The metric form of the pointwise gradient bound: between two points at
distance at least `ρ` from the set the cutoff varies by at most
`dist / (ρ |ln ε|)`. -/
theorem abs_cutoff_sub_le (h0 : 0 < ε) (h1 : ε < 1) {ρ : ℝ} (hρ : 0 < ρ) {x y : X}
    (hx : ρ ≤ infDist x N) (hy : ρ ≤ infDist y N) :
    |cutoff N ε x - cutoff N ε y| ≤ dist x y / (ρ * |Real.log ε|) := by
  have hL : 0 < |Real.log ε| := abs_pos.mpr (Real.log_neg h0 h1).ne
  refine (abs_profile_sub_le h0 h1 hρ hx hy).trans ?_
  refine div_le_div_of_nonneg_right ?_ (mul_pos hρ hL).le
  rw [abs_le]
  constructor
  · have h := infDist_le_infDist_add_dist (s := N) (x := y) (y := x)
    rw [dist_comm] at h
    linarith
  · have h := infDist_le_infDist_add_dist (s := N) (x := x) (y := y)
    linarith

end FoliationQM.MetricDistanceLogCutoff
