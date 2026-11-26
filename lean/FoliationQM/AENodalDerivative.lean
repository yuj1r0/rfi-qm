module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.TangentCone.DimOne
public import Mathlib.Topology.Order.LeftRightNhds
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass

/-!
# Actual derivatives vanish almost everywhere on level sets

Sources: v13 thm:uncertainty, eq:p_var_decomp and eq:cramer_rao,
analytic component kinds C and D. Outside the countable set of points
isolated on the right in a level set, derivative uniqueness forces every
actual derivative to vanish. The result applies to complex wave nodes through
their real normed-space structure. The conclusion is almost everywhere;
no pointwise vanishing rule at every zero is asserted.
-/

@[expose] public section
noncomputable section

namespace FoliationQM.AENodalDerivative

open MeasureTheory Set Filter
open scoped Topology

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- On almost every point of any level set, every actual derivative is zero.
No measurability or completeness assumption on the function or target is needed. -/
theorem ae_level_set_derivative_eq_zero
    (μ : Measure ℝ) [NullSingletonClass μ] (u : ℝ → F) (c : F) :
    ∀ᵐ x ∂μ, u x = c → ∀ d : F, HasDerivAt u d x → d = 0 := by
  let s : Set ℝ := {x | u x = c}
  have hcount : {x ∈ s | 𝓝[s ∩ Ioi x] x = ⊥}.Countable :=
    countable_setOfPred_isolated_right_within
  filter_upwards [hcount.ae_notMem μ] with x hxA
  intro hx d hd
  have hnb : 𝓝[s ∩ Ioi x] x ≠ ⊥ := by
    intro hbot
    exact hxA ⟨hx, hbot⟩
  let t : Set ℝ := s ∩ Ioi x
  have hdiff : t \ {x} = t := by simp [t]
  have hunique : UniqueDiffWithinAt ℝ t x := by
    rw [uniqueDiffWithinAt_iff_accPt, accPt_principal_iff_nhdsWithin, hdiff]
    exact neBot_iff.mpr hnb
  have hzero : HasDerivWithinAt u 0 t x :=
    (hasDerivWithinAt_const x t c).congr (fun _ hy => hy.1) hx
  exact UniqueDiffWithinAt.eq_deriv t hunique hd.hasDerivWithinAt hzero

/-- An actual almost-everywhere derivative field vanishes almost everywhere
where the original function equals the supplied level, including level zero. -/
theorem ae_derivative_zero_on_level_set
    (μ : Measure ℝ) [NullSingletonClass μ] {u v : ℝ → F} (c : F)
    (hd : ∀ᵐ x ∂μ, HasDerivAt u (v x) x) :
    ∀ᵐ x ∂μ, u x = c → v x = 0 := by
  filter_upwards [ae_level_set_derivative_eq_zero μ u c, hd] with x hx hdx
  exact fun hux => hx hux (v x) hdx

end FoliationQM.AENodalDerivative
