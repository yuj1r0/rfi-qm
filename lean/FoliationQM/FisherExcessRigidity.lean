module

public import FoliationQM.IntegratedTwoParticleFisher
public import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# Zero Fisher excess and vanishing conditional scores

In v13 Proposition `prop:fisher_excess`, the correlation excess is a
positive physical coefficient times the integral of a nonnegative sum
of three squared conditional scores against the joint density. Its
vanishing is equivalent to vanishing of all three coordinates almost
everywhere. Continuity on the full spatial product upgrades this to
vanishing at every pair of positions.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.FisherExcessRigidity

open MeasureTheory LorentzCoordinates MarginalDifferentiation TwoParticleFisher
open ConditionalScoreCentering ObserverGaussianFisher

variable {f : Spatial × Spatial → ℝ} {hbar m₁ m₂ : ℝ}

/-- At a positive-density pair the local excess is zero precisely when all
three conditioning-coordinate scores vanish there. -/
theorem excessDensity_zero_iff {z : Spatial × Spatial} (hp : 0 < f z) :
    excessDensity f z = 0 ↔ ∀ i, condScore f z.1 z.2 (axes i) = 0 := by
  simp only [excessDensity, mul_eq_zero, hp.ne', false_or,
    Fintype.sum_eq_zero_iff_of_nonneg (fun i => sq_nonneg (condScore f z.1 z.2 (axes i))),
    funext_iff, Pi.zero_apply, sq_eq_zero_iff]

private theorem excess_zero_iff_density_ae (H : Regular f) (hh : 0 < hbar)
    (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hJ : Integrable (jointDensity hbar m₁ m₂ f)) :
    excess hbar m₁ f = 0 ↔ excessDensity f =ᵐ[volume] 0 := by
  have hi := (IntegratedConditionalVariance.first_trace_decomposition H
    (JointFisherFiniteness.coordinates H hh hm₁ hm₂ hJ).1).2.1
  simp only [excess, mul_eq_zero, (coefficient_pos hh hm₁).ne', false_or]
  exact integral_eq_zero_iff_of_nonneg_ae
    (.of_forall fun z => excessDensity_nonneg z (H.pos z).le) hi

/-- The finite physical excess vanishes exactly when every coordinate of the
conditioning score vanishes almost everywhere on six-dimensional volume. -/
theorem excess_zero_iff_ae (H : Regular f) (hh : 0 < hbar)
    (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hJ : Integrable (jointDensity hbar m₁ m₂ f)) :
    excess hbar m₁ f = 0 ↔
      ∀ᵐ z : Spatial × Spatial, ∀ i, condScore f z.1 z.2 (axes i) = 0 := by
  rw [excess_zero_iff_density_ae H hh hm₁ hm₂ hJ]
  exact ⟨fun h => h.mono fun z hz => (excessDensity_zero_iff (H.pos z)).mp hz,
    fun h => h.mono fun z hz => (excessDensity_zero_iff (H.pos z)).mpr hz⟩

/-- Under full spatial volume, continuity of the local excess upgrades the
almost-everywhere condition to exact vanishing at every pair of positions. -/
theorem excess_zero_iff_everywhere (H : Regular f) (hh : 0 < hbar)
    (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hJ : Integrable (jointDensity hbar m₁ m₂ f)) :
    excess hbar m₁ f = 0 ↔ ∀ x y i, condScore f x y (axes i) = 0 := by
  constructor
  · intro hz x y
    have he := (excess_zero_iff_density_ae H hh hm₁ hm₂ hJ).mp hz
    have h := Measure.eq_of_ae_eq he (IntegratedConditionalVariance.continuous_excessDensity H)
      continuous_zero
    exact (excessDensity_zero_iff (H.pos (x,y))).mp (congrFun h (x,y))
  · intro h
    exact (excess_zero_iff_ae H hh hm₁ hm₂ hJ).mpr (.of_forall fun z => h z.1 z.2)

/-- In the manuscript's gradient notation the same criterion is vanishing of
the vector-valued conditional log gradient almost everywhere on the joint slice. -/
theorem excess_zero_iff_gradient_ae (H : Regular f) (hh : 0 < hbar)
    (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hJ : Integrable (jointDensity hbar m₁ m₂ f)) :
    excess hbar m₁ f = 0 ↔ ∀ᵐ z : Spatial × Spatial,
      ConditionalScoreVector.gradient (fun u => Real.log (TwoParticleMarginals.conditional f u z.2))
        z.1 = 0 := by
  rw [excess_zero_iff_ae H hh hm₁ hm₂ hJ]
  exact ⟨fun h => h.mono fun _ hz => funext hz, fun h => h.mono fun _ hz => congrFun hz⟩

end FoliationQM.FisherExcessRigidity
