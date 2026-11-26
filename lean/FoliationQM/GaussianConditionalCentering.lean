module

public import FoliationQM.TwoParticleGaussianModel
public import FoliationQM.TranslationFisherMatrix
public import FoliationQM.GaussianMassShellMoments
public import FoliationQM.WeightedOsmoticCoercivity

/-!
# Conditional scores of the correlated two-particle Gaussian

For the conditional density G(y−x), the derivatives of the log density in
the conditioning and conditioned coordinates have opposite signs. Centering
at x gives an integrable odd first moment and hence zero conditional mean.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.GaussianConditionalCentering

open MeasureTheory LorentzCoordinates FisherNormalization TwoParticleGaussianModel TwoParticleMarginals

/-- The normalized Gaussian's directional log derivative at any positive width. -/
theorem gaussian_score {σ : ℝ} (hσ : 0 < σ) (x v : Spatial) :
    score (gaussian σ) x v = -spatialDot x v / σ^2 := by
  change score (normalizedDensity (GaussianSliceMoments.density σ) _) x v = _
  rw [score_normalizedDensity ((GaussianSliceMoments.smooth_density σ).differentiable (by simp) x)
    (GaussianSliceMoments.density_pos σ x) (GaussianSliceMoments.normalization_pos hσ), TranslationFisherMatrix.score_coords]
  have h (i : Fin 3) : score (GaussianSliceMoments.density σ) x (ObserverGaussianFisher.axes i) =
      -(x i) / σ^2 := congrFun (GaussianSliceMoments.score_eq σ x) i
  simp only [h, Fin.sum_univ_three, spatialDot]
  ring

private theorem log_gaussian_diff (x : Spatial) :
    DifferentiableAt ℝ (fun z => Real.log (gaussian 1 z)) x :=
  ((gaussian_smooth 1).differentiable (by simp) x).log (gaussian_pos one_pos x).ne'

/-- Moving the conditioning position in direction v gives the score (y−x)·v. -/
theorem conditional_first_score (x y v : Spatial) :
    score (fun u => conditional joint u y) x v = spatialDot (y - x) v := by
  have hd := (log_gaussian_diff (y - x)).hasFDerivAt.comp x
    ((hasFDerivAt_const y x).sub (hasFDerivAt_id x))
  change HasFDerivAt (fun u => Real.log (gaussian 1 (y - u))) _ x at hd
  simp only [score, conditional_eq, hd.fderiv, ContinuousLinearMap.comp_apply, zero_sub,
    neg_apply, ContinuousLinearMap.id_apply, map_neg]
  change -score (gaussian 1) (y - x) v = _
  simp [gaussian_score one_pos]

/-- Moving the conditioned position itself in direction v gives the opposite score. -/
theorem conditional_second_score (x y v : Spatial) :
    score (conditional joint x) y v = -spatialDot (y - x) v := by
  have hd := (log_gaussian_diff (y - x)).hasFDerivAt.comp y
    ((hasFDerivAt_id y).sub (hasFDerivAt_const x y))
  change HasFDerivAt (fun u => Real.log (gaussian 1 (u - x))) _ y at hd
  simp only [score, conditional_eq, hd.fderiv, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply, sub_zero]
  change score (gaussian 1) (y - x) v = _
  simp [gaussian_score one_pos]

private theorem integrable_first_moment (v : Spatial) :
    Integrable (fun z => gaussian 1 z * spatialDot z v) := by
  have hs : Integrable (fun z => euclideanSpeed z * gaussian 1 z) := by
    have h := (GaussianMassShellMoments.integrable_rate_pow_weight (by norm_num : (0:ℝ) < 1/2) 0 1).div_const
      (GaussianSliceMoments.normalization 1)
    convert h using 1
    ext z
    simp only [gaussian, GaussianSliceMoments.density, GaussianKGMode.rate, GaussianSpatialFourier.weight,
      euclideanSpeed, one_pow, mul_one, zero_pow (by decide : 2 ≠ 0), zero_add, pow_one, mul_div_assoc]
    ring_nf
  apply (hs.mul_const (euclideanSpeed v)).mono'
    (((gaussian_smooth 1).continuous.mul (by unfold spatialDot; fun_prop)).aestronglyMeasurable)
  filter_upwards with z
  change ‖gaussian 1 z * spatialDot z v‖ ≤ _
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (gaussian_pos one_pos z)]
  calc
    _ ≤ gaussian 1 z * (euclideanSpeed z * euclideanSpeed v) :=
      mul_le_mul_of_nonneg_left (WeightedOsmoticCoercivity.abs_spatialDot_le z v) (gaussian_pos one_pos z).le
    _ = _ := by ring

/-- The directional score in the conditioning position has a finite conditional first moment on each fiber. -/
theorem integrable_conditional_first_score (x v : Spatial) :
    Integrable (fun y => conditional joint x y * score (fun u => conditional joint u y) x v) := by
  simp only [conditional_first_score]
  simp only [conditional_eq]
  exact (integrable_first_moment v).comp_sub_right x

/-- The actual directional score in the first position has mean zero on every conditional fiber. -/
theorem mean_conditional_first_score (x v : Spatial) :
    (∫ y, conditional joint x y * score (fun u => conditional joint u y) x v) = 0 := by
  simp only [conditional_first_score]
  simp only [conditional_eq]
  let f (z : Spatial) := gaussian 1 z * spatialDot z v
  change (∫ y, f (y - x)) = 0
  rw [integral_sub_right_eq_self]
  have hodd (z : Spatial) : f (-z) = -(f z) := by
    have hg : gaussian 1 (-z) = gaussian 1 z := by
      simp [gaussian, GaussianSliceMoments.density, speedSq_eq_sum]
    simp [f, hg, spatialDot]
    ring
  have h := integral_neg_eq_self (μ := (volume : Measure Spatial)) f
  simp_rw [hodd] at h
  rw [integral_neg] at h
  linarith

end FoliationQM.GaussianConditionalCentering
