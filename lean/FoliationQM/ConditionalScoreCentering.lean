module

public import FoliationQM.MarginalDifferentiation

/-!
# Zero mean of the conditional score

For v13 `prop:fisher_excess` (equations `eq:conditional_bayes` and
`eq:cond_norm`), the derivative is taken in the conditioning particle's
position. The normalized second-particle law has unit mass for every
such position. Its integral derivative is justified from the actual
marginal derivative and integrable fiber terms in the quotient rule.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.ConditionalScoreCentering

open MeasureTheory LorentzCoordinates FisherNormalization TwoParticleMarginals MarginalDifferentiation

/-- The first-coordinate score of the normalized conditional law, with its outcome fixed. -/
def condScore (f : Spatial × Spatial → ℝ) (x y v : Spatial) : ℝ :=
  score (fun u => conditional f u y) x v

/-- The first-coordinate derivative of the conditional density in direction v. -/
def condD (f : Spatial × Spatial → ℝ) (x y v : Spatial) : ℝ :=
  fderiv ℝ (fun u => conditional f u y) x v

variable {f : Spatial × Spatial → ℝ}

private theorem positive_left (H : Regular f) (x : Spatial) : 0 < left f x :=
  left_pos f x (H.left_fiber x) (fun y => H.pos (x,y))

private theorem differentiable_conditional (H : Regular f) (x y : Spatial) :
    DifferentiableAt ℝ (fun u => conditional f u y) x := by
  simpa only [conditional, div_eq_mul_inv, Pi.mul_def, Pi.inv_def, Function.comp_def] using
    ((H.smooth.comp (contDiff_prodMk_left y)).differentiable (by decide) x).mul
      ((left_hasFDerivAt H x).differentiableAt.inv (positive_left H x).ne')

/-- The quotient derivative retains a correction for the change of the normalizing
marginal. Both terms are evaluated at the same conditioning point x. -/
theorem condD_eq (H : Regular f) (x y v : Spatial) :
    condD f x y v = leftD f x y v / left f x -
      f (x,y) * (fderiv ℝ (left f) x v / (left f x) ^ 2) := by
  have hfun : (fun u => f (u,y)) = fun u => left f u * conditional f u y :=
    funext fun u => factorization f u y (positive_left H u)
  have hl := (contDiff_left H).differentiable (by decide) x
  have hc := differentiable_conditional H x y
  have he : leftD f x y v = left f x * condD f x y v + conditional f x y * fderiv ℝ (left f) x v := by
    rw [leftD, hfun]
    change (fderiv ℝ (left f * fun u => conditional f u y) x) v = _
    rw [(hl.hasFDerivAt.mul hc.hasFDerivAt).fderiv]
    rfl
  rw [he, conditional]
  field_simp [(positive_left H x).ne']
  ring

/-- The normalized conditional density times its logarithmic score is its actual derivative. -/
theorem conditional_mul_condScore (H : Regular f) (x y v : Spatial) :
    conditional f x y * condScore f x y v = condD f x y v := by
  have hp : 0 < conditional f x y := div_pos (H.pos _) (positive_left H x)
  rw [condScore, score_eq (differentiable_conditional H x y) hp, condD]
  field_simp

/-- The derivative of the normalized density is integrable on every second-particle fiber. -/
theorem integrable_condD (H : Regular f) (x v : Spatial) : Integrable (fun y => condD f x y v) := by
  simp_rw [condD_eq H]
  exact ((integrable_leftD_apply H x v).div_const _).sub ((H.left_fiber x).mul_const _)

/-- The score is integrable against the actual conditional density on each fiber. -/
theorem integrable_conditional_score (H : Regular f) (x v : Spatial) :
    Integrable (fun y => conditional f x y * condScore f x y v) := by
  simp_rw [conditional_mul_condScore H]
  exact integrable_condD H x v

/-- Integrating the two terms in the quotient derivative cancels the marginal derivative exactly. -/
theorem integral_condD (H : Regular f) (x v : Spatial) : (∫ y, condD f x y v) = 0 := by
  simp_rw [condD_eq H]
  rw [integral_sub ((integrable_leftD_apply H x v).div_const _) ((H.left_fiber x).mul_const _),
    integral_div, integral_mul_const, ← left_fderiv_apply H x v]
  change fderiv ℝ (left f) x v / left f x -
    left f x * (fderiv ℝ (left f) x v / left f x ^ 2) = 0
  field_simp [(positive_left H x).ne']
  ring

/-- Differentiation commutes with conditional normalization in every conditioning direction. -/
theorem derivative_under_conditional_integral (H : Regular f) (x v : Spatial) :
    (∫ y, condD f x y v) = fderiv ℝ (fun u => ∫ y, conditional f u y) x v := by
  have he : (fun u => ∫ y, conditional f u y) = fun _ => (1 : ℝ) :=
    funext fun u => integral_conditional f u (H.left_fiber u) (positive_left H u)
  rw [he, integral_condD H x v]
  simp

/-- The mean first-coordinate conditional score is zero in each spatial direction. -/
theorem integral_conditional_score (H : Regular f) (x v : Spatial) :
    (∫ y, conditional f x y * condScore f x y v) = 0 := by
  simp_rw [conditional_mul_condScore H]
  exact integral_condD H x v

end FoliationQM.ConditionalScoreCentering
