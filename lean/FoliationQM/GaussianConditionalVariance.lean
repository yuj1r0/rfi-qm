module

public import FoliationQM.GaussianConditionalCentering
public import FoliationQM.ConditionalScoreCentering

/-!
# Conditional Gaussian score variance on each fiber

The sheared Gaussian has an identity covariance matrix in the conditioning
score on every fiber. The three laboratory axis variances sum to three.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.GaussianConditionalVariance

open MeasureTheory ProbabilityTheory LorentzCoordinates TwoParticleGaussianModel
open TwoParticleMarginals GaussianConditionalCentering ConditionalScoreCentering ObserverGaussianFisher

private abbrev pdf := gaussianPDFReal 0 1

private theorem gaussian_prod (z : Spatial) : gaussian 1 z = ∏ k, pdf (z k) := by
  simp only [gaussian, GaussianSliceMoments.density, GaussianSliceMoments.normalization, pdf,
    gaussianPDFReal, NNReal.coe_one, sub_zero, one_pow, mul_one, Fin.prod_univ_three]
  rw [show -speedSq z / 2 = -(z 0)^2 / 2 + -(z 1)^2 / 2 + -(z 2)^2 / 2 by
    unfold speedSq spatialDot; ring, Real.exp_add, Real.exp_add]
  ring

private theorem first_moment : (∫ t : ℝ, pdf t * t) = 0 := by
  have h := integral_id_gaussianReal (μ := 0) (v := 1)
  rw [integral_gaussianReal_eq_integral_smul one_ne_zero] at h
  exact h

private theorem second_moment : (∫ t : ℝ, pdf t * t^2) = 1 := by
  have h := variance_fun_id_gaussianReal (μ := 0) (v := 1)
  rw [variance_eq_integral measurable_id'.aemeasurable] at h
  simp only [integral_id_gaussianReal, sub_zero] at h
  rw [integral_gaussianReal_eq_integral_smul one_ne_zero] at h
  exact h

private def factor (i j k : Fin 3) (t : ℝ) : ℝ :=
  pdf t * (if k = i then t else 1) * (if k = j then t else 1)

private theorem integral_factor (i j k : Fin 3) :
    (∫ t, factor i j k t) = if (k = i ↔ k = j) then 1 else 0 := by
  by_cases hki : k = i <;> by_cases hkj : k = j
  · simpa only [factor, ite_eq_left hki, ite_eq_left hkj, ite_eq_left (iff_of_true hki hkj), mul_assoc, ← sq]
      using second_moment
  · have h : ¬ (k = i ↔ k = j) := fun h => hkj (h.mp hki)
    simpa only [factor, ite_eq_left hki, ite_eq_right hkj, ite_eq_right h, mul_one]
      using first_moment
  · have h : ¬ (k = i ↔ k = j) := fun h => hki (h.mpr hkj)
    simpa only [factor, ite_eq_right hki, ite_eq_left hkj, ite_eq_right h, mul_one]
      using first_moment
  · simpa only [factor, ite_eq_right hki, ite_eq_right hkj, ite_eq_left (iff_of_false hki hkj), mul_one]
      using integral_gaussianPDFReal_eq_one 0 (one_ne_zero : (1 : NNReal) ≠ 0)

/-- The spatial coordinate moments of the unit Gaussian form the identity matrix. -/
theorem coordinate_moment (i j : Fin 3) :
    (∫ z : Spatial, gaussian 1 z * z i * z j) = if i = j then 1 else 0 := by
  have hf (z : Spatial) : gaussian 1 z * z i * z j = ∏ k, factor i j k (z k) := by
    simp only [gaussian_prod, factor, Finset.prod_mul_distrib]
    simp
  simp_rw [hf, integral_fintype_prod_volume_eq_prod, integral_factor]
  fin_cases i <;> fin_cases j <;> norm_num [Fin.prod_univ_three]

private theorem integrable_coordinate_sq (i : Fin 3) :
    Integrable (fun z : Spatial => gaussian 1 z * (z i)^2) := by
  apply Integrable.of_integral_ne_zero
  simpa [pow_two, ← mul_assoc] using (coordinate_moment i i).trans_ne (by simp)

private theorem integrable_mixed (i j : Fin 3) :
    Integrable (fun z : Spatial => gaussian 1 z * z i * z j) :=
  ObserverFisherBilinear.integrable_weighted_mul (gaussian_smooth 1).continuous.aemeasurable
    (measurable_pi_apply i).aemeasurable (measurable_pi_apply j).aemeasurable
    (ae_of_all _ fun z => (gaussian_pos one_pos z).le) (integrable_coordinate_sq i) (integrable_coordinate_sq j)

private theorem directional_expansion (v z : Spatial) :
    gaussian 1 z * (spatialDot z v)^2 =
      ∑ i, ∑ j, (v i * v j) * (gaussian 1 z * z i * z j) := by
  simp only [Fin.sum_univ_three, spatialDot]
  ring

/-- The directional second moment of the standard spatial Gaussian is finite. -/
theorem integrable_gaussian_direction (v : Spatial) :
    Integrable (fun z => gaussian 1 z * (spatialDot z v)^2) := by
  simp_rw [directional_expansion]
  exact integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
    (integrable_mixed i j).const_mul _

/-- The standard Gaussian has second moment |v|² in the unnormalized direction v. -/
theorem gaussian_variance (v : Spatial) : (∫ z, gaussian 1 z * (spatialDot z v)^2) = speedSq v := by
  simp_rw [directional_expansion]
  have hm (i j : Fin 3) := (integrable_mixed i j).const_mul (v i * v j)
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hm i j))]
  simp_rw [integral_finsetSum _ (fun j _ => hm _ j), integral_const_mul, coordinate_moment]
  simp [Fin.sum_univ_three, speedSq, spatialDot]

/-- The conditional squared score is integrable for every conditioning position and direction. -/
theorem integrable_directional_variance (x v : Spatial) :
    Integrable (fun y => conditional joint x y * (condScore joint x y v)^2) := by
  simp only [condScore, conditional_first_score]
  simp only [conditional_eq]
  exact (integrable_gaussian_direction v).comp_sub_right x

/-- The conditional score variance in direction v is |v|² on every fiber. -/
theorem directional_variance (x v : Spatial) :
    (∫ y, conditional joint x y * (condScore joint x y v)^2) = speedSq v := by
  simp only [condScore, conditional_first_score]
  simp only [conditional_eq]
  exact (integral_sub_right_eq_self (fun z => gaussian 1 z * (spatialDot z v)^2) x).trans (gaussian_variance v)

/-- Summing the three conditional coordinate variances gives exactly three on every fiber. -/
theorem trace (x : Spatial) :
    (∫ y, conditional joint x y * ∑ i, (condScore joint x y (axes i))^2) = 3 := by
  simp_rw [Finset.mul_sum]
  rw [integral_finsetSum _ fun i _ => integrable_directional_variance x (axes i)]
  simp [directional_variance, Fin.sum_univ_three, axes, speedSq, spatialDot]
  norm_num

/-- The joint weight times a single squared conditional directional score is integrable on the product. -/
theorem joint_direction_integrable (v : Spatial) :
    Integrable (fun z : Spatial × Spatial => joint z * (condScore joint z.1 z.2 v)^2) := by
  simp only [condScore, conditional_first_score, joint, mul_assoc]
  exact (measurePreserving_prod_sub volume volume).integrable_comp_of_integrable
    ((gaussian_integrable one_pos).mul_prod (integrable_gaussian_direction v))

/-- The full joint excess integrand formed from the three squared scores is integrable. -/
theorem joint_trace_integrable :
    Integrable (fun z : Spatial × Spatial => joint z * ∑ i, (condScore joint z.1 z.2 (axes i))^2) := by
  simp_rw [Finset.mul_sum]
  exact integrable_finsetSum _ fun i _ => joint_direction_integrable (axes i)

end FoliationQM.GaussianConditionalVariance
