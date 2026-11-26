module

public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Topology.Order.Compact
public import Mathlib.Tactic

/-!
# A uniform bound for the fixed smooth transition

Source: v13 `eq:log_cutoff_l2_bound`, component kinds C and D. Compactness
bounds the actual derivative of the fixed transition on [0,1]; constant
germs give zero derivative outside this interval. The resulting constant
is independent of every cutoff radius.
-/

@[expose] public section
noncomputable section

namespace FoliationQM.SmoothTransitionDerivativeBound

open Filter Set
open scoped Topology

/-- The actual derivative of the fixed smooth transition has one nonnegative global bound, obtained from compactness and its constant exterior germs. -/
theorem exists_uniform_derivative_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, |deriv Real.smoothTransition x| ≤ C := by
  have hc : Continuous (fun x : ℝ => |deriv Real.smoothTransition x|) :=
    (Real.smoothTransition.contDiff (n := 1)).continuous_deriv_one.abs
  obtain ⟨B, hB⟩ := isCompact_Icc.bddAbove_image hc.continuousOn
    (K := Icc (0 : ℝ) 1)
  refine ⟨max B 0, le_max_right _ _, fun x => ?_⟩
  by_cases hx0 : x < 0
  · have hd : HasDerivAt Real.smoothTransition 0 x := by
      apply (hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq
      filter_upwards [eventually_lt_nhds hx0] with y hy
      exact Real.smoothTransition.zero_of_nonpos hy.le
    simpa only [hd.deriv, abs_zero] using (le_max_right B 0)
  by_cases hx1 : 1 < x
  · have hd : HasDerivAt Real.smoothTransition 0 x := by
      apply (hasDerivAt_const x (1 : ℝ)).congr_of_eventuallyEq
      filter_upwards [eventually_gt_nhds hx1] with y hy
      exact Real.smoothTransition.one_of_one_le hy.le
    simpa only [hd.deriv, abs_zero] using (le_max_right B 0)
  exact (hB ⟨x, ⟨le_of_not_gt hx0, le_of_not_gt hx1⟩, rfl⟩).trans (le_max_left _ _)

end FoliationQM.SmoothTransitionDerivativeBound
