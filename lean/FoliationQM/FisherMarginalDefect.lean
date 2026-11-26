module

public import FoliationQM.IntegratedTwoParticleFisher
public import FoliationQM.FisherParticleExchange

/-!
# The difference between joint and marginal Fisher energies

The conditional expectation of the second particle's Fisher energy in
v13 Proposition `prop:fisher_excess` exceeds its marginal Fisher energy
by the conditional-score term for the opposite conditioning order. After
Fubini and the exchange of particles, the difference between the joint
energy and the two marginal energies contains one such term for each
particle, with its own inverse-mass coefficient.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.FisherMarginalDefect

open MeasureTheory LorentzCoordinates TwoParticleMarginals MarginalDifferentiation
open JointScoreRegularity FisherNormalization ObserverGaussianFisher TwoParticleFisher
open scoped BigOperators

variable {f : Spatial × Spatial → ℝ} {hbar m₁ m₂ : ℝ}

/-- The second-coordinate joint trace splits into the right marginal's Fisher
trace and the excess integral for conditioning on the second coordinate.
Both terms are integrable under finite second-coordinate square integrals. -/
theorem second_trace_decomposition (H : Regular f)
    (h₂ : ∀ i, Integrable (fun z : Spatial × Spatial => f z * secondScore f z.1 z.2 (axes i) ^ 2)) :
    Integrable (traceIntegrand (right f) axes) ∧ Integrable (excessDensity (swap f)) ∧
      (∫ z : Spatial × Spatial, f z * ∑ i, secondScore f z.1 z.2 (axes i) ^ 2) =
        fisherTrace (right f) axes volume + ∫ z, excessDensity (swap f) z := by
  obtain ⟨hm,he,hs⟩ := IntegratedConditionalVariance.first_trace_decomposition H.swap
    (fun i => (FisherParticleExchange.integrable_first_square_swap f (axes i)).mpr (h₂ i))
  exact ⟨hm, he, (FisherParticleExchange.integral_first_trace_swap f).symm.trans hs⟩

/-- The expected conditional energy equals the unconditional right marginal energy
plus the correlation excess in the exchanged conditioning order. -/
theorem conditional_energy_eq (H : Regular f) (hh : 0 < hbar)
    (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hJ : Integrable (jointDensity hbar m₁ m₂ f)) :
    (∫ x, left f x * singleEnergy hbar m₂ (conditional f x)) =
      singleEnergy hbar m₂ (right f) + excess hbar m₂ (swap f) := by
  have ht := (JointFisherFiniteness.traces H hh hm₁ hm₂ hJ).2
  have hd := (second_trace_decomposition H (JointFisherFiniteness.coordinates H hh hm₁ hm₂ hJ).2).2.2
  let t := fun z : Spatial × Spatial => f z * ∑ i, secondScore f z.1 z.2 (axes i) ^ 2
  calc
    _ = ∫ x, coefficient hbar m₂ * ∫ y, t (x,y) := by
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro x
      dsimp only [t]
      rw [ConditionalScoreDecomposition.integral_second_trace H axes x]
      unfold singleEnergy
      ring
    _ = coefficient hbar m₂ * ∫ z, t z := by
      rw [integral_const_mul, ← integral_prod t ht]
      rfl
    _ = _ := by rw [show (∫ z, t z) = _ from hd]; exact mul_add _ _ _

/-- Subtracting the two actual marginal Fisher energies from the finite joint
energy leaves exactly the two nonnegative conditional-score contributions. -/
theorem joint_energy_eq (H : Regular f) (hh : 0 < hbar)
    (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hJ : Integrable (jointDensity hbar m₁ m₂ f)) :
    jointEnergy hbar m₁ m₂ f = singleEnergy hbar m₁ (left f) + singleEnergy hbar m₂ (right f) +
      excess hbar m₁ f + excess hbar m₂ (swap f) := by
  rw [IntegratedTwoParticleFisher.joint_energy_eq H hh hm₁ hm₂ hJ,
    conditional_energy_eq H hh hm₁ hm₂ hJ]
  ring

end FoliationQM.FisherMarginalDefect
