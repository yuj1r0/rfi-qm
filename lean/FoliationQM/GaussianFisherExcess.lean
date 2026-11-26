module

public import FoliationQM.GaussianConditionalVariance
public import FoliationQM.TwoParticleFisher

/-!
# Physical Fisher excess of the sheared Gaussian

The conditioning score has trace three at each first-particle position.
Integrating against its unit-mass marginal gives the explicit spatial
correlation excess, with both physical joint Fisher terms integrable.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.GaussianFisherExcess

open MeasureTheory LorentzCoordinates TwoParticleGaussianModel TwoParticleMarginals TwoParticleFisher
open GaussianConditionalCentering GaussianConditionalVariance ConditionalScoreCentering
open FisherNormalization ObserverGaussianFisher JointScoreRegularity

/-- The physical excess density on each fiber integrates to three times the first marginal. -/
theorem fiber_excessDensity (x : Spatial) : (∫ y, excessDensity joint (x,y)) = gaussian 1 x * 3 := by
  have h (y : Spatial) : excessDensity joint (x,y) = gaussian 1 x *
      (conditional joint x y * ∑ i, (condScore joint x y (axes i))^2) := by
    rw [excessDensity, conditional_eq, joint, mul_assoc]
  simp_rw [h, integral_const_mul, GaussianConditionalVariance.trace]

/-- The joint density weighted by the squared conditional score has integral three over ℝ⁶. -/
theorem integral_excessDensity : (∫ z, excessDensity joint z) = 3 := by
  change (∫ z, excessDensity joint z ∂(volume.prod volume)) = 3
  rw [integral_prod (excessDensity joint) GaussianConditionalVariance.joint_trace_integrable]
  simp only [fiber_excessDensity, integral_mul_const, integral_gaussian one_pos, one_mul]

/-- The unscaled trace gives exactly three times the first particle's printed Fisher coefficient. -/
theorem excess_eq (hbar m₁ : ℝ) : excess hbar m₁ joint = 3 * coefficient hbar m₁ := by
  rw [excess, integral_excessDensity, mul_comm]

/-- Positive physical parameters give a strictly positive excess for this correlated Gaussian. -/
theorem excess_pos {hbar m₁ : ℝ} (hh : 0 < hbar) (hm : 0 < m₁) :
    0 < excess hbar m₁ joint := by
  rw [excess_eq]
  exact mul_pos (by norm_num) (coefficient_pos hh hm)

/-- The first joint score combines the noise displacement and the negative marginal position. -/
theorem first_score (x y v : Spatial) :
    firstScore joint x y v = spatialDot (y - x) v - spatialDot x v := by
  have hg := (gaussian_smooth 1).differentiable (by simp)
  have hc (u : Spatial) := conditional_eq u y
  have h := conditional_first_score x y v
  simp only [hc] at h
  have hd : DifferentiableAt ℝ (fun u => gaussian 1 (y-u)) x :=
    (hg _).comp x ((differentiableAt_const y).sub differentiableAt_id)
  change score (fun u => gaussian 1 u * gaussian 1 (y-u)) x v = _
  rw [ObserverFisherProduct.score_mul (hg x) hd
    (gaussian_pos one_pos x) (gaussian_pos one_pos _) v, h, gaussian_score one_pos]
  ring

/-- The second joint score is the negative projection of the centered noise displacement. -/
theorem second_score (x y v : Spatial) : secondScore joint x y v = -spatialDot (y - x) v := by
  have hem : 0 < left joint x := left_eq ▸ gaussian_pos one_pos x
  have hd := (joint_smooth.comp (contDiff_prodMk_right x)).differentiable (by simp) y
  have h : score (conditional joint x) y v = secondScore joint x y v :=
    score_normalizedDensity hd (joint_pos _) hem v
  exact h.symm.trans (conditional_second_score x y v)

private theorem first_integrable (v : Spatial) :
    Integrable (fun z : Spatial × Spatial => joint z * (firstScore joint z.1 z.2 v)^2) := by
  have ha : Integrable (fun z : Spatial × Spatial => joint z * (spatialDot (z.2-z.1) v)^2) := by
    simpa only [condScore, conditional_first_score] using joint_direction_integrable v
  have hb : Integrable (fun z : Spatial × Spatial => joint z * (spatialDot z.1 v)^2) := by
    have hi := (measurePreserving_prod_sub volume volume).integrable_comp_of_integrable
      ((integrable_gaussian_direction v).mul_prod (gaussian_integrable one_pos))
    convert hi using 1
    funext z
    change (gaussian 1 z.1 * gaussian 1 (z.2-z.1)) * _ = (gaussian 1 z.1 * _) * gaussian 1 (z.2-z.1)
    ring
  simp only [first_score]
  apply ((ha.add hb).const_mul 2).mono'
  · apply Continuous.aestronglyMeasurable
    exact joint_smooth.continuous.mul (by unfold spatialDot; fun_prop)
  · filter_upwards with z
    change ‖joint z * (spatialDot (z.2-z.1) v - spatialDot z.1 v)^2‖ ≤
      2 * (joint z * (spatialDot (z.2-z.1) v)^2 + joint z * (spatialDot z.1 v)^2)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (joint_pos z).le (sq_nonneg _))]
    generalize spatialDot (z.2-z.1) v = a
    generalize spatialDot z.1 v = b
    nlinarith only [mul_nonneg (joint_pos z).le (sq_nonneg (a+b))]

/-- Both kinetic terms in the actual inverse-mass-weighted joint Fisher functional are integrable. -/
theorem jointDensity_integrable (hbar m₁ m₂ : ℝ) : Integrable (jointDensity hbar m₁ m₂ joint) := by
  have hs (v : Spatial) : Integrable (fun z : Spatial × Spatial => joint z * (secondScore joint z.1 z.2 v)^2) := by
    simpa only [second_score, neg_sq, condScore, conditional_first_score] using joint_direction_integrable v
  unfold jointDensity
  simp_rw [Finset.mul_sum]
  exact (integrable_finsetSum Finset.univ fun i _ => (first_integrable (axes i)).const_mul (coefficient hbar m₁)).add
    (integrable_finsetSum Finset.univ fun i _ => (hs (axes i)).const_mul (coefficient hbar m₂))

end FoliationQM.GaussianFisherExcess
