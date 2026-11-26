module

public import FoliationQM.GaussianFisherExcess

/-!
# Exact marginal superadditivity defect for the sheared Gaussian

Conditioning the first position on the second gives coordinate variance
one half. The corresponding first joint trace is six. The two marginals
have variances one and two, respectively.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.GaussianMarginalDefect

open MeasureTheory LorentzCoordinates TwoParticleGaussianModel TwoParticleMarginals TwoParticleFisher
open GaussianFisherExcess GaussianConditionalCentering ConditionalScoreCentering JointScoreRegularity
open FisherNormalization ObserverGaussianFisher

/-- The normalized spatial Gaussian has Fisher trace 3/σ² at any positive width. -/
theorem gaussian_trace {σ : ℝ} (hσ : 0 < σ) : fisherTrace (gaussian σ) axes volume = 3 / σ^2 := by
  change fisherTrace (normalizedDensity (GaussianSliceMoments.density σ) _) axes volume = _
  rw [fisherTrace_normalizedDensity ((GaussianSliceMoments.smooth_density σ).differentiable (by simp))
    (GaussianSliceMoments.density_pos σ) (GaussianSliceMoments.normalization_pos hσ) axes volume
    (gaussian_trace_integrable hσ), gaussian_trace_eq hσ]
  field_simp [(GaussianSliceMoments.normalization_pos hσ).ne']

private abbrev firstTraceDensity (z : Spatial × Spatial) :=
  joint z * ∑ i, (firstScore joint z.1 z.2 (axes i))^2

private abbrev secondTraceDensity (z : Spatial × Spatial) :=
  joint z * ∑ i, (secondScore joint z.1 z.2 (axes i))^2

private theorem second_eq_excess : secondTraceDensity = excessDensity joint := by
  funext z
  simp only [secondTraceDensity, excessDensity, second_score, condScore, conditional_first_score, neg_sq]

private theorem second_integrable : Integrable secondTraceDensity :=
  second_eq_excess ▸ GaussianConditionalVariance.joint_trace_integrable

private theorem first_integrable : Integrable firstTraceDensity := by
  have hsum := jointDensity_integrable 8 8 8
  have h : jointDensity 8 8 8 joint = firstTraceDensity + secondTraceDensity := by
    funext z
    simp [jointDensity, coefficient, firstTraceDensity, secondTraceDensity]
    ring
  rw [h] at hsum
  simpa only [add_sub_cancel_right] using hsum.sub second_integrable

private theorem first_reverse (x y v : Spatial) : firstScore joint x y v =
    score (gaussian (Real.sqrt (1/2))) (x - (1/2 : ℝ) • y) v := by
  rw [first_score, gaussian_score (Real.sqrt_pos.mpr (by norm_num)), Real.sq_sqrt (by norm_num)]
  simp only [spatialDot, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

private theorem first_trace_fiber (y : Spatial) :
    (∫ x, firstTraceDensity (x,y)) = gaussian (Real.sqrt 2) y * 6 := by
  have h (x : Spatial) : firstTraceDensity (x,y) = gaussian (Real.sqrt 2) y *
      traceIntegrand (gaussian (Real.sqrt (1/2))) axes (x - (1/2 : ℝ) • y) := by
    simp only [firstTraceDensity, traceIntegrand, first_reverse, joint_complete_square, mul_assoc]
  simp_rw [h, integral_const_mul, integral_sub_right_eq_self]
  change _ * fisherTrace _ _ volume = _
  rw [gaussian_trace (Real.sqrt_pos.mpr (by norm_num)), Real.sq_sqrt (by norm_num)]
  ring

/-- The first-particle part of the joint squared-score trace integrates to six on configuration space. -/
theorem joint_first_trace :
    (∫ z : Spatial × Spatial, joint z * ∑ i, (firstScore joint z.1 z.2 (axes i))^2) = 6 := by
  change (∫ z, firstTraceDensity z ∂(volume.prod volume)) = 6
  rw [integral_prod_symm firstTraceDensity first_integrable]
  simp only [first_trace_fiber, integral_mul_const, integral_gaussian (Real.sqrt_pos.mpr (by norm_num : (0:ℝ) < 2)), one_mul]

/-- The second-particle part of the joint squared-score trace integrates to three. -/
theorem joint_second_trace :
    (∫ z : Spatial × Spatial, joint z * ∑ i, (secondScore joint z.1 z.2 (axes i))^2) = 3 := by
  change (∫ z, secondTraceDensity z) = _
  rw [second_eq_excess, integral_excessDensity]

/-- Exact joint energy with the inverse-mass coefficient for each particle. -/
theorem jointEnergy_eq (hbar m₁ m₂ : ℝ) : jointEnergy hbar m₁ m₂ joint =
    6 * coefficient hbar m₁ + 3 * coefficient hbar m₂ := by
  unfold jointEnergy
  change (∫ z, coefficient hbar m₁ * firstTraceDensity z + coefficient hbar m₂ * secondTraceDensity z) = _
  rw [integral_add (first_integrable.const_mul _) (second_integrable.const_mul _), integral_const_mul, integral_const_mul]
  rw [show (∫ z, firstTraceDensity z) = 6 from joint_first_trace,
    show (∫ z, secondTraceDensity z) = 3 from joint_second_trace]
  ring

/-- The unit-variance first marginal contributes three times its physical coefficient. -/
theorem leftEnergy_eq (hbar m : ℝ) : singleEnergy hbar m (left joint) = 3 * coefficient hbar m := by
  rw [singleEnergy, left_eq, gaussian_trace one_pos]
  ring

/-- The variance-two second marginal contributes three halves times its physical coefficient. -/
theorem rightEnergy_eq (hbar m : ℝ) : singleEnergy hbar m (right joint) = (3/2) * coefficient hbar m := by
  rw [singleEnergy, right_eq, gaussian_trace (Real.sqrt_pos.mpr (by norm_num)), Real.sq_sqrt (by norm_num)]
  ring

/-- Exact difference between the joint energy and the sum of the two marginal energies. -/
theorem defect_eq (hbar m₁ m₂ : ℝ) :
    jointEnergy hbar m₁ m₂ joint - (singleEnergy hbar m₁ (left joint) + singleEnergy hbar m₂ (right joint)) =
      3 * coefficient hbar m₁ + (3/2) * coefficient hbar m₂ := by
  rw [jointEnergy_eq, leftEnergy_eq, rightEnergy_eq]
  ring

/-- The joint Fisher energy strictly exceeds the sum of its marginal energies at positive physical parameters. -/
theorem strict_superadditive {hbar m₁ m₂ : ℝ} (hh : 0 < hbar) (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) :
    singleEnergy hbar m₁ (left joint) + singleEnergy hbar m₂ (right joint) < jointEnergy hbar m₁ m₂ joint := by
  apply sub_pos.mp
  rw [defect_eq]
  exact add_pos (mul_pos (by norm_num) (coefficient_pos hh hm₁))
    (mul_pos (by norm_num) (coefficient_pos hh hm₂))

end FoliationQM.GaussianMarginalDefect
