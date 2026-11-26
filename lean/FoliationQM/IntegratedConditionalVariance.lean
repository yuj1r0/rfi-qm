module

public import FoliationQM.TwoParticleFisher

/-!
# Global first-particle Fisher variance decomposition

For v13 `prop:fisher_excess`, finite joint score squares yield finite
first-particle marginal and excess integrals on the full spatial slices.
Fubini supplies the fiber identity almost everywhere, while the nonnegative
conditional variance controls both terms when the remaining variable is integrated.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.IntegratedConditionalVariance

open MeasureTheory LorentzCoordinates TwoParticleMarginals MarginalDifferentiation
open JointScoreRegularity ConditionalScoreCentering FisherNormalization ObserverGaussianFisher
open TwoParticleFisher
open scoped BigOperators

variable {f : Spatial × Spatial → ℝ}

/-- The joint density times the squared conditional score trace is continuous. -/
theorem continuous_excessDensity (H : Regular f) : Continuous (excessDensity f) :=
  H.smooth.continuous.mul (continuous_finsetSum _ fun i _ => (continuous_conditionalScore H (axes i)).pow 2)

/-- The first marginal weighted score trace is continuous on the whole spatial slice. -/
theorem continuous_marginal_trace (H : Regular f) : Continuous (traceIntegrand (left f) axes) :=
  (contDiff_left H).continuous.mul
    (continuous_finsetSum _ fun i _ => (continuous_marginalScore H (axes i)).pow 2)

/-- The original finite first-coordinate joint square integrals give an
integrable marginal Fisher trace and an integrable six-dimensional excess.
The three-direction joint trace is exactly their sum. -/
theorem first_trace_decomposition (H : Regular f)
    (hi : ∀ i, Integrable (fun z : Spatial × Spatial => f z * firstScore f z.1 z.2 (axes i) ^ 2)) :
    Integrable (traceIntegrand (left f) axes) ∧ Integrable (excessDensity f) ∧
      (∫ z : Spatial × Spatial, f z * ∑ i, firstScore f z.1 z.2 (axes i) ^ 2) =
        fisherTrace (left f) axes volume + ∫ z, excessDensity f z := by
  let J := fun z : Spatial × Spatial => f z * ∑ i, firstScore f z.1 z.2 (axes i) ^ 2
  have hJ : Integrable J := by
    simp only [J, Finset.mul_sum]
    exact integrable_finsetSum _ (fun i _ => hi i)
  have hfib : ∀ᵐ x, ∀ i, Integrable (fun y => f (x,y) * firstScore f x y (axes i) ^ 2) :=
    ae_all_iff.mpr fun i => (hi i).prod_right_ae
  have hsplit := hfib.mono fun x hx => first_fiber_trace H x hx
  have hnon (x : Spatial) : 0 ≤ ∫ y, excessDensity f (x,y) :=
    integral_nonneg fun y => excessDensity_nonneg _ (H.pos (x,y)).le
  have hm : Integrable (traceIntegrand (left f) axes) := by
    apply hJ.integral_prod_left.mono' (continuous_marginal_trace H).aestronglyMeasurable
    filter_upwards [hsplit] with x hx
    change ‖traceIntegrand (left f) axes x‖ ≤ ∫ y, J (x,y)
    rw [Real.norm_of_nonneg (traceIntegrand_nonneg _ _ (marginal_pos H x).le)]
    exact (le_add_of_nonneg_right (hnon x)).trans_eq hx.2.symm
  have he : Integrable (fun x => ∫ y, excessDensity f (x,y)) := by
    apply (hJ.integral_prod_left.sub hm).congr
    filter_upwards [hsplit] with x hx
    change (∫ y, J (x,y)) - traceIntegrand (left f) axes x = _
    exact sub_eq_of_eq_add' hx.2
  have hE : Integrable (excessDensity f) := by
    apply (integrable_prod_iff (continuous_excessDensity H).aestronglyMeasurable).mpr
    refine ⟨hsplit.mono fun _ hx => hx.1, ?_⟩
    simpa only [Real.norm_of_nonneg (excessDensity_nonneg _ (H.pos _).le)] using he
  refine ⟨hm, hE, ?_⟩
  calc
    _ = ∫ x, ∫ y, J (x,y) := integral_prod J hJ
    _ = ∫ x, traceIntegrand (left f) axes x + ∫ y, excessDensity f (x,y) :=
      integral_congr_ae (hsplit.mono fun _ hx => hx.2)
    _ = fisherTrace (left f) axes volume + ∫ x, ∫ y, excessDensity f (x,y) := integral_add hm he
    _ = _ := congrArg (fisherTrace (left f) axes volume + ·) (integral_prod _ hE).symm

end FoliationQM.IntegratedConditionalVariance
