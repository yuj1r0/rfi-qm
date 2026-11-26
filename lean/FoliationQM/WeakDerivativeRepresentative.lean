module

public import FoliationQM.ComplexIntervalPrimitive
public import FoliationQM.WeakDerivativeConstancy
public import FoliationQM.SobolevWeakDerivative

/-!
# Actual locally absolutely continuous representatives of weak derivatives

Sources: v13 eq:cramer_rao, thm:uncertainty and eq:p_var_decomp.
Kinds C and D, analytic components. A genuine weak derivative is integrated
once, and the actual zero weak derivative theorem supplies one complex
constant. The resulting representative is continuous, locally absolutely
continuous and has the given derivative almost everywhere. Classical
differentiability is asserted for this constructed representative only.
-/

@[expose] public section
noncomputable section

namespace FoliationQM.WeakDerivativeRepresentative

open MeasureTheory Filter
open scoped ContDiff

variable {f g : ℝ → ℂ}

/-- A genuine weak derivative determines its original function, up to one
constant and null-set replacement, by the actual interval primitive. -/
theorem exists_ae_eq_const_add_primitive
    (h : SobolevWeakDerivative.HasWeakDerivative f g) :
    ∃ C : ℂ, f =ᵐ[volume] fun x => C + ComplexIntervalPrimitive.primitive g x := by
  let G := ComplexIntervalPrimitive.primitive g
  have hG : SobolevWeakDerivative.HasWeakDerivative G g :=
    ⟨(ComplexIntervalPrimitive.continuous_primitive h.locallyIntegrable_right).locallyIntegrable,
      h.locallyIntegrable_right,
      ComplexIntervalPrimitive.integral_test h.locallyIntegrable_right⟩
  have hlocal : LocallyIntegrable (fun x => f x - G x) volume := by
    exact (h.locallyIntegrable_left.sub hG.locallyIntegrable_left).congr
      (Filter.Eventually.of_forall fun _ => rfl)
  have hzero : ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∫ x, deriv φ x • (f x - G x)) = 0 := by
    intro φ hφ hs
    have hpair : (∫ x, deriv φ x • f x) = ∫ x, deriv φ x • G x :=
      neg_injective ((h.integral_test φ hφ hs).symm.trans (hG.integral_test φ hφ hs))
    simp_rw [smul_sub]
    rw [integral_sub (h.integrable_deriv_test_smul hφ hs)
      (hG.integrable_deriv_test_smul hφ hs), hpair, sub_self]
  obtain ⟨C, hC⟩ :=
    WeakDerivativeConstancy.exists_ae_const_of_test_derivative_eq_zero hlocal hzero
  refine ⟨C, ?_⟩
  filter_upwards [hC] with x hx
  exact sub_eq_iff_eq_add.mp hx

/-- The actual primitive construction produces a continuous, locally absolutely
continuous representative with the true derivative almost everywhere. -/
theorem exists_locally_ac_representative
    (h : SobolevWeakDerivative.HasWeakDerivative f g) :
    ∃ u : ℝ → ℂ, u =ᵐ[volume] f ∧ Continuous u ∧
      (∀ a b, AbsolutelyContinuousOnInterval u a b) ∧
      (∀ᵐ x ∂volume, HasDerivAt u (g x) x) := by
  obtain ⟨C, hC⟩ := exists_ae_eq_const_add_primitive h
  refine ⟨fun x => C + ComplexIntervalPrimitive.primitive g x, hC.symm,
    continuous_const.add (ComplexIntervalPrimitive.continuous_primitive
      h.locallyIntegrable_right), ?_, ?_⟩
  · intro a b
    have hconst : AbsolutelyContinuousOnInterval (fun _ : ℝ => C) a b :=
      (contDiff_const : ContDiff ℝ 1 (fun _ : ℝ => C)).contDiffOn.absolutelyContinuousOnInterval
    exact hconst.fun_add
      (ComplexIntervalPrimitive.absolutelyContinuousOnInterval_primitive
        h.locallyIntegrable_right a b)
  · filter_upwards [ComplexIntervalPrimitive.ae_hasDerivAt_primitive
      h.locallyIntegrable_right] with x hx
    exact hx.const_add C

end FoliationQM.WeakDerivativeRepresentative
