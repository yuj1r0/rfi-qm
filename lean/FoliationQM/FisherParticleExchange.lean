module

public import FoliationQM.TwoParticleFisher

/-!
# Exchanging particles in the inverse-mass-weighted Fisher integral

For v13 `eq:fisher_2p_main` and `prop:fisher_excess`, interchanging the
two spatial coordinates exchanges their scores. The corresponding
interchange of the physical masses preserves both joint Fisher integrability
and the integral against six-dimensional Lebesgue measure.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.FisherParticleExchange

open MeasureTheory LorentzCoordinates TwoParticleMarginals JointScoreRegularity
open ObserverGaussianFisher TwoParticleFisher
open scoped BigOperators

/-- Swapping labels and their masses pulls back the actual Fisher density
along the spatial coordinate exchange. -/
theorem jointDensity_swap (hbar m₁ m₂ : ℝ) (f : Spatial × Spatial → ℝ) :
    jointDensity hbar m₂ m₁ (swap f) = swap (jointDensity hbar m₁ m₂ f) := by
  funext z
  exact add_comm _ _

/-- The swapped physical integrand is integrable exactly when the original is. -/
theorem integrable_jointDensity_swap (hbar m₁ m₂ : ℝ) (f : Spatial × Spatial → ℝ) :
    Integrable (jointDensity hbar m₂ m₁ (swap f)) ↔ Integrable (jointDensity hbar m₁ m₂ f) := by
  rw [jointDensity_swap]
  exact integrable_swap_iff

/-- Exchanging the particle coordinates and their physical mass labels leaves
the integrated joint Fisher energy invariant. -/
theorem jointEnergy_swap (hbar m₁ m₂ : ℝ) (f : Spatial × Spatial → ℝ) :
    jointEnergy hbar m₂ m₁ (swap f) = jointEnergy hbar m₁ m₂ f := by
  simp only [jointEnergy, jointDensity_swap hbar m₁ m₂ f, integral_swap]

/-- Square-integrability of each directional first score after label exchange
is equivalent to square-integrability of the original directional second score. -/
theorem integrable_first_square_swap (f : Spatial × Spatial → ℝ) (v : Spatial) :
    Integrable (fun z : Spatial × Spatial => swap f z * firstScore (swap f) z.1 z.2 v ^ 2) ↔
      Integrable (fun z : Spatial × Spatial => f z * secondScore f z.1 z.2 v ^ 2) :=
  integrable_swap_iff (f := fun z : Spatial × Spatial => f z * secondScore f z.1 z.2 v ^ 2)

/-- The integrated three-axis first trace for the exchanged density is exactly
the original integrated three-axis second trace. -/
theorem integral_first_trace_swap (f : Spatial × Spatial → ℝ) :
    (∫ z : Spatial × Spatial, swap f z * ∑ i, firstScore (swap f) z.1 z.2 (axes i) ^ 2) =
      ∫ z : Spatial × Spatial, f z * ∑ i, secondScore f z.1 z.2 (axes i) ^ 2 :=
  integral_swap (fun z : Spatial × Spatial => f z * ∑ i, secondScore f z.1 z.2 (axes i) ^ 2)

end FoliationQM.FisherParticleExchange
