module

public import FoliationQM.JointFisherFiniteness
public import FoliationQM.IntegratedConditionalVariance

/-!
# The integrated inverse-mass-weighted Fisher decomposition

The only energy finiteness hypothesis is integrability of the physical joint
Fisher density. Fubini supplies the finite fibers and all three terms of the
source equation are genuine finite integrals.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.IntegratedTwoParticleFisher

open MeasureTheory LorentzCoordinates TwoParticleMarginals MarginalDifferentiation
open JointScoreRegularity FisherNormalization ObserverGaussianFisher TwoParticleFisher
open scoped BigOperators

variable {f : Spatial × Spatial → ℝ} {hbar m₁ m₂ : ℝ}

/-- The expected conditional single-particle energy is integrable against the first marginal. -/
theorem conditional_energy_integrable (H : Regular f) (hh : 0 < hbar)
    (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hJ : Integrable (jointDensity hbar m₁ m₂ f)) :
    Integrable (fun x => left f x * singleEnergy hbar m₂ (conditional f x)) := by
  obtain ⟨_, ht⟩ := JointFisherFiniteness.traces H hh hm₁ hm₂ hJ
  apply (ht.integral_prod_left.const_mul (coefficient hbar m₂)).congr
  apply Filter.Eventually.of_forall
  intro x
  change coefficient hbar m₂ * (∫ y, f (x,y) * ∑ i, secondScore f x y (axes i) ^ 2) = _
  rw [ConditionalScoreDecomposition.integral_second_trace H axes x]
  unfold singleEnergy
  ring

/-- Integrated v13 Fisher equation on the full product of the two spatial slices. -/
theorem joint_energy_eq (H : Regular f) (hh : 0 < hbar)
    (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hJ : Integrable (jointDensity hbar m₁ m₂ f)) :
    jointEnergy hbar m₁ m₂ f = singleEnergy hbar m₁ (left f) +
      (∫ x, left f x * singleEnergy hbar m₂ (conditional f x)) + excess hbar m₁ f := by
  have hv := IntegratedConditionalVariance.first_trace_decomposition H
    (JointFisherFiniteness.coordinates H hh hm₁ hm₂ hJ).1
  have hc := conditional_energy_integrable H hh hm₁ hm₂ hJ
  have hm := hv.1.const_mul (coefficient hbar m₁)
  have he := hv.2.1.integral_prod_left.const_mul (coefficient hbar m₁)
  have hmc : Integrable (fun x => coefficient hbar m₁ * traceIntegrand (left f) axes x +
      left f x * singleEnergy hbar m₂ (conditional f x)) := hm.add hc
  unfold jointEnergy excess
  change (∫ z, jointDensity hbar m₁ m₂ f z ∂volume.prod volume) = _
  rw [integral_prod _ hJ]
  calc
    _ = ∫ x, coefficient hbar m₁ * traceIntegrand (left f) axes x +
        left f x * singleEnergy hbar m₂ (conditional f x) +
        coefficient hbar m₁ * ∫ y, excessDensity f (x,y) := by
          apply integral_congr_ae
          filter_upwards [JointFisherFiniteness.fiber_coordinates_ae H hh hm₁ hm₂ hJ] with x hx
          exact weighted_fiber H x hbar m₁ m₂ hx.1 hx.2
    _ = _ := by
      rw [integral_add hmc he, integral_add hm hc, integral_const_mul, integral_const_mul]
      rw [← integral_prod _ hv.2.1]
      rfl

/-- The integrated conditional-score contribution is nonnegative. -/
theorem excess_nonneg (H : Regular f) (hh : 0 < hbar) (hm : 0 < m₁) :
    0 ≤ excess hbar m₁ f :=
  mul_nonneg (coefficient_pos hh hm).le (integral_nonneg fun z => excessDensity_nonneg z (H.pos z).le)

end FoliationQM.IntegratedTwoParticleFisher
