module

public import FoliationQM.ConditionalScoreDecomposition
public import FoliationQM.TranslationFisherMatrix

/-!
# Vanishing conditional scores and factorization of the spatial density

In the equality case of v13 `prop:fisher_excess`, the first-coordinate
conditional score vanishes in all three directions. Each conditional
density is then constant in its conditioning position. Integrating
the joint density over that position identifies the constant with the
actual second marginal. The conclusion concerns the spatial probability
density at a fixed time.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.ConditionalDensityRigidity

open MeasureTheory LorentzCoordinates TwoParticleMarginals MarginalDifferentiation
open JointScoreRegularity ConditionalScoreCentering FisherNormalization ObserverGaussianFisher

variable {f : Spatial × Spatial → ℝ}

/-- Vanishing of the three conditional axis scores forces each conditional law
to equal the actual right marginal, independently of the conditioning position. -/
theorem conditional_eq_right_of_scores (H : Regular f)
    (hz : ∀ x y i, condScore f x y (axes i) = 0) (x y : Spatial) :
    conditional f x y = right f y := by
  have hs : ∀ u v : Spatial, condScore f u y v = 0 := by
    intro u v
    rw [condScore, TranslationFisherMatrix.score_coords]
    exact Finset.sum_eq_zero fun i _ => mul_eq_zero_of_right _ (hz u y i)
  have hd : ∀ u, fderiv ℝ (fun a => conditional f a y) u = 0 := by
    intro u
    ext v
    change condD f u y v = 0
    rw [← conditional_mul_condScore H, hs, mul_zero]
  have hc : ∀ u : Spatial, conditional f u y = conditional f x y := fun u =>
    is_const_of_fderiv_eq_zero (((contDiff_conditional H).comp
      (contDiff_prodMk_left y)).differentiable (by decide)) hd u x
  have hmass : (∫ u, left f u) = 1 := (integral_left f H.integrable).trans H.mass_one
  have he (u : Spatial) : f (u,y) = left f u * conditional f x y :=
    (factorization f u y (marginal_pos H u)).trans (congrArg (left f u * ·) (hc u))
  unfold right
  simp_rw [he]
  rw [integral_mul_const, hmass, one_mul]

/-- A density equal to the product of its marginals has zero conditional
score in every spatial direction. -/
theorem all_scores_zero_of_factorization (H : Regular f)
    (h : ∀ x y, f (x,y) = left f x * right f y) (x y v : Spatial) :
    condScore f x y v = 0 := by
  have he : (fun u => conditional f u y) = fun _ => right f y := by
    funext u
    rw [conditional, h]
    field_simp [(marginal_pos H u).ne']
  rw [condScore, he]
  simp [score]

/-- For the regular positive joint law on the whole spatial product, all
conditional coordinate scores vanish precisely when the two actual marginal
densities multiply to the joint density everywhere. -/
theorem coordinates_zero_iff_factorization (H : Regular f) :
    (∀ x y i, condScore f x y (axes i) = 0) ↔
      (∀ x y, f (x,y) = left f x * right f y) := by
  constructor
  · intro hz x y
    rw [factorization f x y (marginal_pos H x), conditional_eq_right_of_scores H hz]
  · exact fun h x y i => all_scores_zero_of_factorization H h x y (axes i)

/-- Almost-everywhere and pointwise equality with the product of the
actual marginals agree for the continuous joint and marginal densities
on full six-dimensional Lebesgue space. -/
theorem factorization_iff_ae (H : Regular f) :
    (∀ x y, f (x,y) = left f x * right f y) ↔
      ∀ᵐ z : Spatial × Spatial, f z = left f z.1 * right f z.2 := by
  constructor
  · exact fun h => Filter.Eventually.of_forall fun z => h z.1 z.2
  · intro ha x y
    have he : f = fun z => left f z.1 * right f z.2 :=
      Measure.eq_of_ae_eq ha H.smooth.continuous
        (((contDiff_left H).continuous.comp continuous_fst).mul
          ((contDiff_right H).continuous.comp continuous_snd))
    exact congrFun he (x,y)

end FoliationQM.ConditionalDensityRigidity
