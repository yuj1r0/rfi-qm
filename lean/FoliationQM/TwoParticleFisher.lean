module

public import FoliationQM.ConditionalVariance
public import FoliationQM.ConditionalScoreDecomposition
public import FoliationQM.ObserverGaussianFisher

/-!
# The inverse-mass-weighted spatial Fisher functional

Definitions follow v13 lines 1199–1216 using the three laboratory axes
in each copy of space. The fiber identity sums the marginal variance
decomposition before integrating over the retained coordinate.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.TwoParticleFisher

open MeasureTheory LorentzCoordinates TwoParticleMarginals MarginalDifferentiation
open JointScoreRegularity ConditionalScoreCentering FisherNormalization ObserverGaussianFisher
open scoped BigOperators

/-- Source coefficient for one particle of mass m. -/
def coefficient (hbar m : ℝ) : ℝ := hbar^2 / (8*m)

/-- The physical joint integrand with the two positive inverse-mass coefficients. -/
def jointDensity (hbar m₁ m₂ : ℝ) (f : Spatial × Spatial → ℝ) (z : Spatial × Spatial) : ℝ :=
  coefficient hbar m₁ * (f z * ∑ i, firstScore f z.1 z.2 (axes i) ^ 2) +
  coefficient hbar m₂ * (f z * ∑ i, secondScore f z.1 z.2 (axes i) ^ 2)

/-- The physical joint Fisher functional integrated over six-dimensional Lebesgue space. -/
def jointEnergy (hbar m₁ m₂ : ℝ) (f : Spatial × Spatial → ℝ) : ℝ :=
  ∫ z, jointDensity hbar m₁ m₂ f z

/-- Single-particle energy with the same Planck constant and the corresponding mass. -/
def singleEnergy (hbar m : ℝ) (r : Spatial → ℝ) : ℝ :=
  coefficient hbar m * fisherTrace r axes volume

/-- Squared spatial conditioning score, weighted with the original joint density. -/
def excessDensity (f : Spatial × Spatial → ℝ) (z : Spatial × Spatial) : ℝ :=
  f z * ∑ i, condScore f z.1 z.2 (axes i) ^ 2

/-- The spatial-amplitude correlation excess for the first conditioning variable. -/
def excess (hbar m₁ : ℝ) (f : Spatial × Spatial → ℝ) : ℝ :=
  coefficient hbar m₁ * ∫ z, excessDensity f z

/-- Strictly positive source parameters give a strictly positive energy coefficient. -/
theorem coefficient_pos {hbar m : ℝ} (hh : 0 < hbar) (hm : 0 < m) :
    0 < coefficient hbar m := div_pos (sq_pos_of_pos hh) (by positivity)

/-- Nonnegative joint density makes the local squared conditional-score term nonnegative. -/
theorem excessDensity_nonneg {f : Spatial × Spatial → ℝ} (z : Spatial × Spatial) (hf : 0 ≤ f z) :
    0 ≤ excessDensity f z := mul_nonneg hf (Finset.sum_nonneg (fun _ _ => sq_nonneg _))

/-- At every finite Fisher fiber the full three-coordinate first score square
splits into the marginal trace density and the conditional excess integral. -/
theorem first_fiber_trace {f : Spatial × Spatial → ℝ} (H : Regular f) (x : Spatial)
    (hi : ∀ i, Integrable (fun y => f (x,y) * firstScore f x y (axes i) ^ 2)) :
    Integrable (fun y => excessDensity f (x,y)) ∧
      (∫ y, f (x,y) * ∑ i, firstScore f x y (axes i) ^ 2) =
        traceIntegrand (left f) axes x + ∫ y, excessDensity f (x,y) := by
  have he i := ConditionalVariance.integrable_conditional_square H x (axes i) (hi i)
  have hf i := ConditionalVariance.fiber_variance H x (axes i) (hi i)
  have hsum := congrArg (fun a : Fin 3 → ℝ => ∑ i, a i) (funext hf)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
  simp only [excessDensity, Finset.mul_sum]
  exact ⟨integrable_finsetSum _ (fun i _ => he i), by
    rw [integral_finsetSum _ (fun i _ => hi i), integral_finsetSum _ (fun i _ => he i)]
    exact hsum⟩

/-- On each fiber with finite joint coordinate squares, the full physical integrand
splits with the printed first and second inverse-mass coefficients. -/
theorem weighted_fiber {f : Spatial × Spatial → ℝ} (H : Regular f) (x : Spatial) (hbar m₁ m₂ : ℝ)
    (h₁ : ∀ i, Integrable (fun y => f (x,y) * firstScore f x y (axes i) ^ 2))
    (h₂ : ∀ i, Integrable (fun y => f (x,y) * secondScore f x y (axes i) ^ 2)) :
    (∫ y, jointDensity hbar m₁ m₂ f (x,y)) =
      coefficient hbar m₁ * traceIntegrand (left f) axes x +
      left f x * singleEnergy hbar m₂ (conditional f x) +
      coefficient hbar m₁ * ∫ y, excessDensity f (x,y) := by
  have hi₁ : Integrable (fun y => f (x,y) * ∑ i, firstScore f x y (axes i) ^ 2) := by
    simp only [Finset.mul_sum]
    exact integrable_finsetSum _ (fun i _ => h₁ i)
  have hi₂ : Integrable (fun y => f (x,y) * ∑ i, secondScore f x y (axes i) ^ 2) := by
    simp only [Finset.mul_sum]
    exact integrable_finsetSum _ (fun i _ => h₂ i)
  unfold jointDensity singleEnergy
  rw [integral_add (hi₁.const_mul _) (hi₂.const_mul _), integral_const_mul, integral_const_mul,
    (first_fiber_trace H x h₁).2, ConditionalScoreDecomposition.integral_second_trace H axes x]
  ring

end FoliationQM.TwoParticleFisher
