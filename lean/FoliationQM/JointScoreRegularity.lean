module

public import FoliationQM.MarginalDifferentiation

/-!
# Partial spatial scores and differentiation of their marginal

At a fixed observer time the two spatial scores in v13's Fisher-excess
identity differentiate the logarithm of the joint density in the two
coordinate directions. Integration of the density times the first score
gives the actual directional derivative of the first marginal at every
fiber covered by the derivative-envelope hypotheses.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.JointScoreRegularity

open MeasureTheory LorentzCoordinates TwoParticleMarginals MarginalDifferentiation
open FisherNormalization

/-- Logarithmic score in the first spatial variable, with the second held fixed. -/
def firstScore (f : Spatial × Spatial → ℝ) (x y v : Spatial) : ℝ :=
  score (fun u => f (u,y)) x v

/-- Logarithmic score in the second spatial variable, with the first held fixed. -/
def secondScore (f : Spatial × Spatial → ℝ) (x y v : Spatial) : ℝ :=
  score (fun u => f (x,u)) y v

/-- Swapping the spatial variables transports the first score to the second. -/
theorem firstScore_swap (f : Spatial × Spatial → ℝ) (x y v : Spatial) :
    firstScore (swap f) y x v = secondScore f x y v := rfl

/-- Swapping the spatial variables transports the second score to the first. -/
theorem secondScore_swap (f : Spatial × Spatial → ℝ) (x y v : Spatial) :
    secondScore (swap f) y x v = firstScore f x y v := rfl

variable {f : Spatial × Spatial → ℝ}

/-- Positivity and integrability of each fiber make its marginal strictly positive. -/
theorem marginal_pos (H : Regular f) (x : Spatial) : 0 < left f x :=
  left_pos _ x (H.left_fiber x) (fun y => H.pos (x,y))

/-- The joint conditional quotient is strictly positive at every pair. -/
theorem conditional_pos (H : Regular f) (x y : Spatial) : 0 < conditional f x y :=
  div_pos (H.pos _) (marginal_pos H x)

/-- The actual conditional quotient is jointly C¹ in both spatial arguments. -/
theorem contDiff_conditional (H : Regular f) :
    ContDiff ℝ 1 (fun z : Spatial × Spatial => conditional f z.1 z.2) :=
  H.smooth.div ((contDiff_left H).comp contDiff_fst) (fun z => (marginal_pos H z.1).ne')

private theorem continuous_firstScore_of (hs : ContDiff ℝ 1 f) (hp : ∀ z, 0 < f z)
    (v : Spatial) : Continuous (fun z : Spatial × Spatial => firstScore f z.1 z.2 v) :=
  (continuous_leftD (hs.log fun z => (hp z).ne')).clm_apply (g := fun _ => v) continuous_const

/-- The first score in a fixed direction is jointly continuous. -/
theorem continuous_firstScore (H : Regular f) (v : Spatial) :
    Continuous (fun z : Spatial × Spatial => firstScore f z.1 z.2 v) :=
  continuous_firstScore_of H.smooth H.pos v

/-- The second score in a fixed direction is jointly continuous. -/
theorem continuous_secondScore (H : Regular f) (v : Spatial) :
    Continuous (fun z : Spatial × Spatial => secondScore f z.1 z.2 v) :=
  (continuous_firstScore H.swap v).comp (continuous_snd.prodMk continuous_fst)

/-- The first marginal's directional score is continuous throughout the spatial slice. -/
theorem continuous_marginalScore (H : Regular f) (v : Spatial) :
    Continuous (fun x => score (left f) x v) :=
  (((contDiff_left H).log fun x => (marginal_pos H x).ne').continuous_fderiv
    (by decide)).clm_apply (g := fun _ => v) continuous_const

/-- The right marginal also has continuous directional score. -/
theorem continuous_rightScore (H : Regular f) (v : Spatial) :
    Continuous (fun y => score (right f) y v) := continuous_marginalScore H.swap v

/-- The conditional score obtained by differentiating in the conditioning
coordinate is jointly continuous. -/
theorem continuous_conditionalScore (H : Regular f) (v : Spatial) :
    Continuous (fun z : Spatial × Spatial => score (fun u => conditional f u z.2) z.1 v) :=
  continuous_firstScore_of (contDiff_conditional H) (fun z => conditional_pos H z.1 z.2) v

/-- The two joint scores, and the marginal and conditional scores lifted to
the joint slice, are all Borel measurable. -/
theorem measurable_scores (H : Regular f) (v : Spatial) :
    Measurable (fun z : Spatial × Spatial => firstScore f z.1 z.2 v) ∧
    Measurable (fun z : Spatial × Spatial => secondScore f z.1 z.2 v) ∧
    Measurable (fun z : Spatial × Spatial => score (left f) z.1 v) ∧
    Measurable (fun z : Spatial × Spatial => score (fun u => conditional f u z.2) z.1 v) :=
  ⟨(continuous_firstScore H v).measurable, (continuous_secondScore H v).measurable,
    ((continuous_marginalScore H v).comp continuous_fst).measurable,
    (continuous_conditionalScore H v).measurable⟩

/-- Multiplication by the joint density recovers the directional derivative in x. -/
theorem weighted_firstScore (H : Regular f) (x y v : Spatial) :
    f (x,y) * firstScore f x y v = leftD f x y v := by
  have hd : DifferentiableAt ℝ (fun u => f (u,y)) x :=
    (H.smooth.comp (contDiff_prodMk_left y)).differentiable (by decide) x
  rw [firstScore, score_eq hd (H.pos (x,y))]
  unfold leftD
  field_simp [(H.pos (x,y)).ne']

/-- The density-weighted score is integrable on each second-coordinate fiber. -/
theorem integrable_weighted_firstScore (H : Regular f) (x v : Spatial) :
    Integrable (fun y => f (x,y) * firstScore f x y v) := by
  simpa only [weighted_firstScore H] using integrable_leftD_apply H x v

/-- The fiber integral of the weighted score is the actual derivative of the marginal. -/
theorem integral_weighted_firstScore_eq_fderiv (H : Regular f) (x v : Spatial) :
    (∫ y, f (x,y) * firstScore f x y v) = fderiv ℝ (left f) x v := by
  simp only [weighted_firstScore H, left_fderiv_apply H]

/-- The integrated weighted first score equals the marginal times its own score. -/
theorem integral_weighted_firstScore (H : Regular f) (x v : Spatial) :
    (∫ y, f (x,y) * firstScore f x y v) = left f x * score (left f) x v := by
  rw [integral_weighted_firstScore_eq_fderiv H, score_eq
    ((contDiff_left H).differentiable (by decide) x) (marginal_pos H x)]
  field_simp [(marginal_pos H x).ne']

end FoliationQM.JointScoreRegularity
