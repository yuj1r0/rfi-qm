module

public import FoliationQM.MetricDistanceLogCutoff
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Congr

/-!
# The differential of the logarithmic cutoff of a Lipschitz distance function

Source: v13 `eq:log_cutoff_l2_bound`, the pointwise bound
"`|dχ_ε|_h ≤ C / (r |ln ε|)`" on the transition annulus, component kinds C
and D. Let `r` be a real function on a normed space that is Lipschitz near a
point `x` with constant `L`, and `χ_ε = χ_ε ∘ r` the literal logarithmic
cutoff of `eq:log_cutoff_wallstrom` as a function of `r`. Then the Fréchet
differential of `χ_ε` at `x` satisfies

* `‖dχ_ε(x)‖ ≤ L / (r(x) |ln ε|)` where `r(x) > 0`;
* `dχ_ε(x) = 0` where `r(x) < ε²` or `r(x) > ε`;

and hence `‖dχ_ε(x)‖² ≤ (L/|ln ε|)² r(x)⁻²` on the annulus
`ε² ≤ r(x) ≤ ε` and zero off it.

The cutoff is Lipschitz, not smooth, and need not be differentiable at every
point. The statements hold at every point because the Fréchet differential is
zero by convention where it does not exist; by Rademacher's theorem the
exceptional set has measure zero in finite dimension. The integral of the
bound over the annulus is separate.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.LipschitzLogCutoff

open Filter Set Metric LogarithmicCutoffProfile MetricDistanceLogCutoff
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] {r : E → ℝ} {x : E} {L ε : ℝ}

/-- A function Lipschitz near a point is continuous there. -/
theorem continuousAt_of_lip (hlip : ∀ᶠ y in 𝓝 x, |r y - r x| ≤ L * ‖y - x‖) :
    ContinuousAt r x := by
  have h0 : Tendsto (fun y => L * ‖y - x‖) (𝓝 x) (𝓝 0) := by
    have : Tendsto (fun y : E => ‖y - x‖) (𝓝 x) (𝓝 0) := tendsto_norm_sub_self x
    simpa using this.const_mul L
  have h1 : Tendsto (fun y => r y - r x) (𝓝 x) (𝓝 0) :=
    squeeze_zero_norm' (hlip.mono fun y hy => by rwa [Real.norm_eq_abs]) h0
  have h2 := h1.add_const (r x)
  simpa [ContinuousAt] using h2

variable [NormedSpace ℝ E]

/-- The pointwise gradient bound: at a point at positive distance the
differential of the cutoff has norm at most `L / (r |ln ε|)`. -/
theorem norm_fderiv_le (h0 : 0 < ε) (h1 : ε < 1) (hL : 0 ≤ L)
    (hlip : ∀ᶠ y in 𝓝 x, |r y - r x| ≤ L * ‖y - x‖) (hr : 0 < r x) :
    ‖fderiv ℝ (fun y => profile ε (r y)) x‖ ≤ L / (r x * |Real.log ε|) := by
  have hℓ : 0 < |Real.log ε| := abs_pos.mpr (Real.log_neg h0 h1).ne
  have hcont := continuousAt_of_lip hlip
  have hstep : ∀ ρ, 0 < ρ → ρ < r x →
      ‖fderiv ℝ (fun y => profile ε (r y)) x‖ ≤ L / (ρ * |Real.log ε|) := by
    intro ρ hρ hρr
    refine norm_fderiv_le_of_lip' ℝ (by positivity) ?_
    filter_upwards [hlip, hcont.eventually (lt_mem_nhds hρr)] with y hy hyρ
    rw [Real.norm_eq_abs]
    calc |profile ε (r y) - profile ε (r x)|
        ≤ |r y - r x| / (ρ * |Real.log ε|) := abs_profile_sub_le h0 h1 hρ hyρ.le hρr.le
      _ ≤ L * ‖y - x‖ / (ρ * |Real.log ε|) := by gcongr
      _ = L / (ρ * |Real.log ε|) * ‖y - x‖ := by ring
  set a : ℝ := ‖fderiv ℝ (fun y => profile ε (r y)) x‖ with hadef
  rw [le_div_iff₀ (by positivity)]
  by_contra hcon
  have hgt : L < a * (r x * |Real.log ε|) := not_le.mp hcon
  have ha : 0 < a := by
    by_contra hna
    have : a = 0 := le_antisymm (not_lt.mp hna) (norm_nonneg _)
    rw [this, zero_mul] at hgt
    linarith
  have hq : L / (a * |Real.log ε|) < r x := by
    rw [div_lt_iff₀ (by positivity)]
    nlinarith
  set ρ : ℝ := (L / (a * |Real.log ε|) + r x) / 2 with hρdef
  have hρ0 : 0 < ρ := by
    have : 0 ≤ L / (a * |Real.log ε|) := by positivity
    rw [hρdef]
    linarith
  have hρr : ρ < r x := by rw [hρdef]; linarith
  have hρq : L / (a * |Real.log ε|) < ρ := by rw [hρdef]; linarith
  have h2 := hstep ρ hρ0 hρr
  rw [le_div_iff₀ (by positivity)] at h2
  rw [div_lt_iff₀ (by positivity)] at hρq
  nlinarith

/-- Inside the inner radius the differential of the cutoff vanishes. -/
theorem fderiv_eq_zero_of_lt (h0 : 0 < ε) (h1 : ε < 1) (hcont : ContinuousAt r x)
    (hr : r x < ε ^ 2) : fderiv ℝ (fun y => profile ε (r y)) x = 0 := by
  have he : (fun y => profile ε (r y)) =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
    filter_upwards [hcont.eventually (gt_mem_nhds hr)] with y hy
    exact (profile_spec h0 h1).1 _ hy.le
  rw [he.fderiv_eq]
  simp

/-- Outside the outer radius the differential of the cutoff vanishes. -/
theorem fderiv_eq_zero_of_gt (h0 : 0 < ε) (h1 : ε < 1) (hcont : ContinuousAt r x)
    (hr : ε < r x) : fderiv ℝ (fun y => profile ε (r y)) x = 0 := by
  have he : (fun y => profile ε (r y)) =ᶠ[𝓝 x] fun _ => (1 : ℝ) := by
    filter_upwards [hcont.eventually (lt_mem_nhds hr)] with y hy
    exact (profile_spec h0 h1).2.2.1 _ hy.le
  rw [he.fderiv_eq]
  simp

/-- The squared differential of the cutoff is at most
`(L/|ln ε|)² r⁻²` on the annulus `ε² ≤ r ≤ ε` and vanishes off it. -/
theorem norm_fderiv_sq_le (h0 : 0 < ε) (h1 : ε < 1) (hL : 0 ≤ L)
    (hlip : ∀ᶠ y in 𝓝 x, |r y - r x| ≤ L * ‖y - x‖) :
    ‖fderiv ℝ (fun y => profile ε (r y)) x‖ ^ 2 ≤
      {z | ε ^ 2 ≤ r z ∧ r z ≤ ε}.indicator
        (fun z => (L / |Real.log ε|) ^ 2 * (r z)⁻¹ ^ 2) x := by
  have hℓ : 0 < |Real.log ε| := abs_pos.mpr (Real.log_neg h0 h1).ne
  have hcont := continuousAt_of_lip hlip
  by_cases hx : ε ^ 2 ≤ r x ∧ r x ≤ ε
  · rw [indicator_of_mem (show x ∈ {z | ε ^ 2 ≤ r z ∧ r z ≤ ε} from hx)]
    have hr : 0 < r x := (sq_pos_of_pos h0).trans_le hx.1
    have hb := norm_fderiv_le h0 h1 hL hlip hr
    calc ‖fderiv ℝ (fun y => profile ε (r y)) x‖ ^ 2
        ≤ (L / (r x * |Real.log ε|)) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hb 2
      _ = (L / |Real.log ε|) ^ 2 * (r x)⁻¹ ^ 2 := by
          field_simp
  · rw [indicator_of_notMem (show x ∉ {z | ε ^ 2 ≤ r z ∧ r z ≤ ε} from hx)]
    rcases not_and_or.mp hx with hlt | hgt
    · rw [fderiv_eq_zero_of_lt h0 h1 hcont (not_le.mp hlt)]
      simp
    · rw [fderiv_eq_zero_of_gt h0 h1 hcont (not_le.mp hgt)]
      simp

end FoliationQM.LipschitzLogCutoff
