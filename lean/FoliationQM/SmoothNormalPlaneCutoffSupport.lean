module

public import FoliationQM.SmoothNormalPlaneCutoff
public import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
# Compact support and integrability for the actual normal-plane cutoff

Source: v13 `eq:log_cutoff_wallstrom` and `eq:log_cutoff_l2_bound`, component
kinds C and D. Actual smoothness and derivative support give genuine global
integrability of the derivative energy. The deficit is supported in the open
outer ball. The plane energy formula and tubular geometry remain separate.
-/

@[expose] public section
noncomputable section

namespace FoliationQM.SmoothNormalPlaneCutoffSupport

open MeasureTheory Set
open scoped ContDiff
open SmoothNormalPlaneCutoff

/-- The actual plane derivative-square energy is continuous, compactly supported and genuinely integrable with respect to complex Lebesgue volume. -/
theorem derivative_energy_data {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1) :
    Continuous (fun z : ℂ => ‖fderiv ℝ (profile ε) z‖ ^ 2) ∧
    HasCompactSupport (fun z : ℂ => ‖fderiv ℝ (profile ε) z‖ ^ 2) ∧
    Integrable (fun z : ℂ => ‖fderiv ℝ (profile ε) z‖ ^ 2) volume := by
  have hcont : Continuous (fun z : ℂ => ‖fderiv ℝ (profile ε) z‖ ^ 2) :=
    (((contDiff_profile h0 h1).continuous_fderiv (by simp)).norm).pow 2
  have hcompact : HasCompactSupport (fun z : ℂ => ‖fderiv ℝ (profile ε) z‖ ^ 2) := by
    apply HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : ℂ) ε)
    intro z hz
    have hd : fderiv ℝ (profile ε) z ≠ 0 := by
      intro heq
      exact hz (by simp [heq])
    have hnorm := (support_fderiv_subset h0 h1 hd).2
    simpa only [Metric.mem_closedBall, dist_zero_right] using hnorm
  exact ⟨hcont, hcompact, hcont.integrable_of_hasCompactSupport hcompact⟩

/-- The actual deficit is supported in the open outer ball, has compact support, and is genuinely integrable with respect to complex Lebesgue volume. -/
theorem deficit_data {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1) :
    Function.support (fun z : ℂ => 1 - profile ε z) ⊆ Metric.ball 0 ε ∧
    HasCompactSupport (fun z : ℂ => 1 - profile ε z) ∧
    Integrable (fun z : ℂ => 1 - profile ε z) volume := by
  have hs : Function.support (fun z : ℂ => 1 - profile ε z) ⊆ Metric.ball 0 ε := by
    intro z hz
    have hnorm : ‖z‖ < ε := by
      by_contra hnot
      apply hz
      change 1 - profile ε z = 0
      rw [(profile_spec h0 h1).2.1 z (le_of_not_gt hnot), sub_self]
    simpa only [Metric.mem_ball, dist_zero_right] using hnorm
  have hcompact : HasCompactSupport (fun z : ℂ => 1 - profile ε z) :=
    HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : ℂ) ε)
      (hs.trans Metric.ball_subset_closedBall)
  have hcont : Continuous (fun z : ℂ => 1 - profile ε z) :=
    continuous_const.sub (contDiff_profile h0 h1).continuous
  exact ⟨hs, hcompact, hcont.integrable_of_hasCompactSupport hcompact⟩

end FoliationQM.SmoothNormalPlaneCutoffSupport
