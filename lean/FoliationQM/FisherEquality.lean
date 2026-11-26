module

public import FoliationQM.FisherExcessRigidity
public import FoliationQM.ConditionalDensityRigidity
public import FoliationQM.FisherSuperadditivity

/-!
# Equality in the spatial Fisher bound

On the connected spatial slices the first conditional excess detects
exactly failure of density factorization. The opposite conditioning order
then gives the same criterion for saturation of the two-marginal inequality.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.FisherEquality

open MeasureTheory LorentzCoordinates TwoParticleMarginals MarginalDifferentiation TwoParticleFisher

variable {f : Spatial × Spatial → ℝ} {hbar m₁ m₂ : ℝ}
variable (H : Regular f) (hh : 0 < hbar) (hm₁ : 0 < m₁) (hm₂ : 0 < m₂)
variable (hJ : Integrable (jointDensity hbar m₁ m₂ f))
include H hh hm₁ hm₂ hJ

/-- The physical first conditional excess vanishes exactly at product spatial densities. -/
theorem excess_zero_iff_factorization :
    excess hbar m₁ f = 0 ↔ ∀ x y, f (x,y) = left f x * right f y :=
  (FisherExcessRigidity.excess_zero_iff_everywhere H hh hm₁ hm₂ hJ).trans
    (ConditionalDensityRigidity.coordinates_zero_iff_factorization H)

/-- Equality with the sum of the two physical marginal energies characterizes pointwise independence. -/
theorem equality_iff_factorization :
    jointEnergy hbar m₁ m₂ f = singleEnergy hbar m₁ (left f) + singleEnergy hbar m₂ (right f) ↔
      ∀ x y, f (x,y) = left f x * right f y := by
  rw [FisherSuperadditivity.equality_iff_both_zero H hh hm₁ hm₂ hJ]
  have hi := (FisherParticleExchange.integrable_jointDensity_swap hbar m₁ m₂ f).mpr hJ
  constructor
  · exact fun h => (excess_zero_iff_factorization H hh hm₁ hm₂ hJ).mp h.1
  · intro hf
    refine ⟨(excess_zero_iff_factorization H hh hm₁ hm₂ hJ).mpr hf,
      (excess_zero_iff_factorization H.swap hh hm₂ hm₁ hi).mpr ?_⟩
    exact fun x y => (hf y x).trans (mul_comm _ _)

/-- Strict superadditivity characterizes the failure of spatial density factorization. -/
theorem strict_iff_not_factorized :
    singleEnergy hbar m₁ (left f) + singleEnergy hbar m₂ (right f) < jointEnergy hbar m₁ m₂ f ↔
      ¬ ∀ x y, f (x,y) = left f x * right f y := by
  rw [← equality_iff_factorization H hh hm₁ hm₂ hJ]
  exact (FisherSuperadditivity.marginal_lower_bound H hh hm₁ hm₂ hJ).lt_iff_ne.trans ne_comm

/-- The first conditional excess is positive exactly for a nonfactorized density. -/
theorem excess_pos_iff_not_factorized :
    0 < excess hbar m₁ f ↔ ¬ ∀ x y, f (x,y) = left f x * right f y := by
  rw [← excess_zero_iff_factorization H hh hm₁ hm₂ hJ]
  exact (IntegratedTwoParticleFisher.excess_nonneg H hh hm₁).lt_iff_ne.trans ne_comm

end FoliationQM.FisherEquality
