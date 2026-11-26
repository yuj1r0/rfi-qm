module

public import FoliationQM.FisherMarginalDefect

/-!
# Superadditivity of the two-particle Fisher energy

Decomposing the joint energy in both particle orders gives the complete
nonnegative defect. Saturation requires both conditional score variances
to vanish. The strict inequality can already be tested by their signs.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.FisherSuperadditivity

open MeasureTheory LorentzCoordinates TwoParticleMarginals MarginalDifferentiation TwoParticleFisher

variable {f : Spatial × Spatial → ℝ} {hbar m₁ m₂ : ℝ}
variable (H : Regular f) (hh : 0 < hbar) (hm₁ : 0 < m₁) (hm₂ : 0 < m₂)
variable (hJ : Integrable (jointDensity hbar m₁ m₂ f))
include H hh hm₁ hm₂ hJ

/-- Averaging the conditional energy bounds the unconditional energy of the second marginal. -/
theorem conditional_lower_bound :
    singleEnergy hbar m₂ (right f) ≤ ∫ x, left f x * singleEnergy hbar m₂ (conditional f x) := by
  rw [FisherMarginalDefect.conditional_energy_eq H hh hm₁ hm₂ hJ]
  exact le_add_of_nonneg_right (IntegratedTwoParticleFisher.excess_nonneg H.swap hh hm₂)

/-- The joint inverse-mass-weighted Fisher energy dominates the sum of its two marginal energies. -/
theorem marginal_lower_bound :
    singleEnergy hbar m₁ (left f) + singleEnergy hbar m₂ (right f) ≤ jointEnergy hbar m₁ m₂ f := by
  rw [FisherMarginalDefect.joint_energy_eq H hh hm₁ hm₂ hJ]
  linarith [IntegratedTwoParticleFisher.excess_nonneg H hh hm₁,
    IntegratedTwoParticleFisher.excess_nonneg H.swap hh hm₂]

/-- Saturation of the marginal bound is equivalent to zero conditional excess in each particle order. -/
theorem equality_iff_both_zero :
    jointEnergy hbar m₁ m₂ f = singleEnergy hbar m₁ (left f) + singleEnergy hbar m₂ (right f) ↔
      excess hbar m₁ f = 0 ∧ excess hbar m₂ (swap f) = 0 := by
  rw [FisherMarginalDefect.joint_energy_eq H hh hm₁ hm₂ hJ]
  have h₁ := IntegratedTwoParticleFisher.excess_nonneg H hh hm₁
  have h₂ := IntegratedTwoParticleFisher.excess_nonneg H.swap hh hm₂
  constructor
  · intro he
    constructor <;> linarith
  · rintro ⟨h₁', h₂'⟩
    rw [h₁', h₂', add_zero, add_zero]

/-- The marginal bound is strict exactly when at least one ordered excess is positive. -/
theorem strict_iff_either_pos :
    singleEnergy hbar m₁ (left f) + singleEnergy hbar m₂ (right f) < jointEnergy hbar m₁ m₂ f ↔
      0 < excess hbar m₁ f ∨ 0 < excess hbar m₂ (swap f) := by
  have h₁ := IntegratedTwoParticleFisher.excess_nonneg H hh hm₁
  have h₂ := IntegratedTwoParticleFisher.excess_nonneg H.swap hh hm₂
  rw [FisherMarginalDefect.joint_energy_eq H hh hm₁ hm₂ hJ]
  constructor
  · intro he
    by_cases hp : 0 < excess hbar m₁ f
    · exact Or.inl hp
    · exact Or.inr (by linarith)
  · rintro (hp | hp) <;> linarith

end FoliationQM.FisherSuperadditivity
