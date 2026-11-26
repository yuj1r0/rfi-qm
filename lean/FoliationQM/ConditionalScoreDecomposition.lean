module

public import FoliationQM.JointScoreRegularity
public import FoliationQM.ConditionalScoreVector
public import FoliationQM.ObserverFisherProduct

/-!
# Coordinate score identities for the two-particle Fisher functional

In v13 Proposition `prop:fisher_excess`, variation of the conditioning
coordinate differentiates both factors of the joint density. Variation
of the second coordinate differentiates only the conditional law. On
each fiber its Fisher trace recovers the second-particle contribution
with the first marginal as weight. Finite direction families include the
three standard spatial axes.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.ConditionalScoreDecomposition

open MeasureTheory LorentzCoordinates TwoParticleMarginals MarginalDifferentiation
open FisherNormalization JointScoreRegularity ConditionalScoreCentering
open scoped BigOperators

variable {f : Spatial × Spatial → ℝ}

/-- The first-particle joint score is the sum of the marginal score and the
conditional score in the conditioning coordinate. -/
theorem first (H : Regular f) (x y v : Spatial) :
    firstScore f x y v = score (left f) x v + condScore f x y v := by
  have hc : DifferentiableAt ℝ (fun u => conditional f u y) x :=
    ((contDiff_conditional H).comp (contDiff_prodMk_left y)).differentiable (by decide) x
  have he : (fun u => f (u,y)) = fun u => left f u * conditional f u y :=
    funext fun u => factorization f u y (marginal_pos H u)
  unfold firstScore condScore
  rw [he, ObserverFisherProduct.score_mul ((left_hasFDerivAt H x).differentiableAt)
    hc (marginal_pos H x) (conditional_pos H x y), add_comm]

/-- Holding the first coordinate fixed makes its marginal a constant: the
joint score in the second coordinate is exactly the score of the normalized fiber. -/
theorem second (H : Regular f) (x y v : Spatial) :
    secondScore f x y v = score (conditional f x) y v := by
  have hd : DifferentiableAt ℝ (fun u => f (x,u)) y :=
    (H.smooth.comp (contDiff_prodMk_right x)).differentiable (by decide) y
  exact (score_normalizedDensity hd (H.pos _) (marginal_pos H x) v).symm

/-- The full finite sum of first-particle squared scores splits into marginal,
mixed, and conditional terms at each pair of positions. -/
theorem first_sum_sq (H : Regular f) {n : ℕ} (axes : Fin n → Spatial) (x y : Spatial) :
    (∑ i, firstScore f x y (axes i) ^ 2) =
      (∑ i, score (left f) x (axes i) ^ 2) +
      2 * (∑ i, score (left f) x (axes i) * condScore f x y (axes i)) +
      ∑ i, condScore f x y (axes i) ^ 2 := by
  simp_rw [first H]
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The joint second-particle trace integrand is exactly the marginal times
the Fisher trace integrand of its normalized second-coordinate law. -/
theorem second_trace_integrand (H : Regular f) {n : ℕ} (axes : Fin n → Spatial)
    (x y : Spatial) :
    f (x,y) * ∑ i, secondScore f x y (axes i) ^ 2 =
      left f x * traceIntegrand (conditional f x) axes y := by
  simp only [second H, traceIntegrand, ← mul_assoc]
  exact congrArg (· * _) (factorization f x y (marginal_pos H x))

/-- Finiteness of the second-particle trace on a fiber is equivalent to
finiteness of the conditional Fisher trace integrand there. -/
theorem integrable_second_trace_iff (H : Regular f) {n : ℕ} (axes : Fin n → Spatial)
    (x : Spatial) :
    Integrable (fun y => f (x,y) * ∑ i, secondScore f x y (axes i) ^ 2) ↔
      Integrable (traceIntegrand (conditional f x) axes) := by
  simp_rw [second_trace_integrand H axes x]
  exact integrable_const_mul_iff (isUnit_iff_ne_zero.mpr (marginal_pos H x).ne') _

/-- Integrating in the second coordinate produces the first marginal times
the genuine conditional Fisher trace for any finite family of directions. -/
theorem integral_second_trace (H : Regular f) {n : ℕ} (axes : Fin n → Spatial) (x : Spatial) :
    (∫ y, f (x,y) * ∑ i, secondScore f x y (axes i) ^ 2) =
      left f x * fisherTrace (conditional f x) axes volume := by
  simp_rw [second_trace_integrand H axes x]
  exact integral_const_mul _ _

end FoliationQM.ConditionalScoreDecomposition
