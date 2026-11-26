module

public import FoliationQM.ConditionalScoreDecomposition

/-!
# Conditional variance of the first-particle translation score

At a fixed first-particle position x, v13 `prop:fisher_excess` splits
the second moment of the first-particle score into a marginal square
and a conditional score variance. The joint square on this fiber
supplies finiteness of the conditional square. Its cross term integrates
to zero because the conditional law is normalized.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.ConditionalVariance

open LorentzCoordinates MeasureTheory TwoParticleMarginals MarginalDifferentiation
open FisherNormalization JointScoreRegularity ConditionalScoreCentering

variable {f : Spatial × Spatial → ℝ}

private theorem square_split (H : Regular f) (x y v : Spatial) :
    f (x,y) * firstScore f x y v ^ 2 =
      f (x,y) * score (left f) x v ^ 2 +
        2 * (f (x,y) * score (left f) x v * condScore f x y v) +
        f (x,y) * condScore f x y v ^ 2 := by
  rw [ConditionalScoreDecomposition.first H]
  ring

/-- The finite directional joint square on a single fiber already implies
integrability there of the squared conditional score with the same joint weight. -/
theorem integrable_conditional_square (H : Regular f) (x v : Spatial)
    (hi : Integrable (fun y => f (x,y) * firstScore f x y v ^ 2)) :
    Integrable (fun y => f (x,y) * condScore f x y v ^ 2) := by
  have hm := (H.left_fiber x).mul_const (score (left f) x v ^ 2)
  have hc := (ConditionalScoreVector.centered_observable H (fun u => score (left f) u v) x v).1
  apply (hi.sub (hm.add (hc.const_mul 2))).congr
  apply Filter.Eventually.of_forall
  intro y
  change f (x,y) * firstScore f x y v ^ 2 - (_ + _) = _
  linarith only [square_split H x y v]

/-- The joint second moment on this fiber equals the marginal square plus
the nonnegative conditional variance, both with their original density weights. -/
theorem fiber_variance (H : Regular f) (x v : Spatial)
    (hi : Integrable (fun y => f (x,y) * firstScore f x y v ^ 2)) :
    (∫ y, f (x,y) * firstScore f x y v ^ 2) = left f x * score (left f) x v ^ 2 +
      ∫ y, f (x,y) * condScore f x y v ^ 2 := by
  have hm := (H.left_fiber x).mul_const (score (left f) x v ^ 2)
  obtain ⟨hc, hz⟩ := ConditionalScoreVector.centered_observable H (fun u => score (left f) u v) x v
  have hsum : Integrable (fun y => f (x,y) * score (left f) x v ^ 2 +
      2 * (f (x,y) * score (left f) x v * condScore f x y v)) := hm.add (hc.const_mul 2)
  simp_rw [square_split H]
  rw [integral_add hsum (integrable_conditional_square H x v hi), integral_add hm (hc.const_mul 2),
    integral_const_mul, integral_mul_const, hz, mul_zero, add_zero]
  rfl

/-- The conditional directional variance is nonnegative for every fiber. -/
theorem conditional_square_nonneg (H : Regular f) (x v : Spatial) :
    0 ≤ ∫ y, f (x,y) * condScore f x y v ^ 2 :=
  integral_nonneg fun y => mul_nonneg (H.pos (x,y)).le (sq_nonneg _)

/-- The marginal directional square is bounded by the fiber's original joint second moment. -/
theorem marginal_square_le (H : Regular f) (x v : Spatial)
    (hi : Integrable (fun y => f (x,y) * firstScore f x y v ^ 2)) :
    left f x * score (left f) x v ^ 2 ≤ ∫ y, f (x,y) * firstScore f x y v ^ 2 := by
  rw [fiber_variance H x v hi]
  exact le_add_of_nonneg_right (conditional_square_nonneg H x v)

/-- The marginal attains the fiber bound precisely when the conditional
directional score vanishes almost everywhere on that fiber. -/
theorem fiber_equality_iff (H : Regular f) (x v : Spatial)
    (hi : Integrable (fun y => f (x,y) * firstScore f x y v ^ 2)) :
    (∫ y, f (x,y) * firstScore f x y v ^ 2) = left f x * score (left f) x v ^ 2 ↔
      ∀ᵐ y, condScore f x y v = 0 := by
  rw [fiber_variance H x v hi, add_eq_left,
    integral_eq_zero_iff_of_nonneg_ae (.of_forall fun y =>
      mul_nonneg (H.pos (x,y)).le (sq_nonneg (condScore f x y v))) (integrable_conditional_square H x v hi)]
  constructor
  · intro h
    filter_upwards [h] with y hy
    exact sq_eq_zero_iff.mp ((mul_eq_zero.mp hy).resolve_left (H.pos (x,y)).ne')
  · intro h
    filter_upwards [h] with y hy
    simp [hy]

end FoliationQM.ConditionalVariance
