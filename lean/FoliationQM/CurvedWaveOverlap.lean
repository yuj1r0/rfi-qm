module

public import FoliationQM.CurvedHessianOverlap

/-!
# Scalar wave covariance on nonlinear chart overlaps

The covariant Hessian in arbitrary tangent directions is reconstructed
from its coordinate-axis values. The chart Jacobians then cancel in its
inverse-metric trace. This proves covariance of the divergence-form wave
for real scalars and for complex fields through their real projections.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.CurvedWaveOverlap

open LorentzMatrixGroup RNCCoordinateConnection RNCCoordinateVolumeChange CurvedHessianOverlap
  CurvedScalarAtlasOverlap CurvedWaveOperator CurvedWaveDivergence RNCHalfDensityJet
open scoped Topology Matrix.Norms.Operator
set_option backward.isDefEq.respectTransparency false

/-- The covariant Hessian in two arbitrary real directions is the bilinear form of its actual coordinate components. -/
theorem hess_form (g : Covector → Mat4) (f : Covector → ℝ) (x u v : Covector) :
    hess g f x u v = form (covariantHessian g f x) u v := by
  let C : Covector →L[ℝ] Covector →L[ℝ] ℝ :=
    ∑ k, fderiv ℝ f x (axis k) • form (christoffel g x k)
  have hc (a b : Covector) : C a b = fderiv ℝ f x (connection g x a b) := by
    rw [CurvedGradientCovariance.apply_components (fderiv ℝ f x) (connection g x a b)]
    simp only [C, sum_apply, smul_apply, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro k _
    rw [mul_comm, form_apply, connection_components]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hmap : fderiv ℝ (fderiv ℝ f) x - C = form (covariantHessian g f x) := by
    apply RNCRicciHalfDensity.bilinear_ext_axis
    intro i j
    simp only [sub_apply, hc, axis, form_basis]
    exact hess_axis g f x i j
  simpa only [sub_apply, hc, hess] using
    congrArg (fun L : Covector →L[ℝ] Covector →L[ℝ] ℝ => L u v) hmap

variable {g : Covector → Mat4} {φ : Covector → Covector} {x : Covector}

/-- The matrix of the real scalar covariant Hessian transforms by ordinary tensor congruence. -/
theorem hessianMatrix_pullback {f : Covector → ℝ} (hφ : ContDiffAt ℝ 2 φ x)
    (hg : DifferentiableAt ℝ g (φ x)) (hs : (g (φ x)).IsSymm)
    (hu : IsUnit (g (φ x)).det) (hJ : IsUnit (jacobianMatrix (fderiv ℝ φ x)).det)
    (hf : ContDiffAt ℝ 2 f (φ x)) :
    covariantHessian (pullMetric g φ (fderiv ℝ φ)) (f ∘ φ) x =
      pullMatrix (jacobianMatrix (fderiv ℝ φ x)) (covariantHessian g f (φ x)) := by
  ext i j
  rw [← hess_axis, hess_pullback hφ hg hs hu hJ hf, hess_form]
  have ha (v : Covector) : (jacobianMatrix (fderiv ℝ φ x)).mulVec v = fderiv ℝ φ x v :=
    LinearMap.toMatrix'_mulVec _ _
  rw [← ha, ← ha, RNCLorentzContraction.form_pullback]
  exact form_basis _ i j

private theorem pull_symmetric (G J : Mat4) (hs : G.IsSymm) : (pullMatrix J G).IsSymm := by
  simp [Matrix.IsSymm, pullMatrix, Matrix.transpose_mul, hs.eq, Matrix.mul_assoc]

private theorem pull_negative (hd : (g (φ x)).det < 0)
    (hJ : IsUnit (jacobianMatrix (fderiv ℝ φ x)).det) :
    (pullMetric g φ (fderiv ℝ φ) x).det < 0 := by
  rw [pullMetric, det_pullMatrix]
  exact mul_neg_of_pos_of_neg (sq_pos_of_ne_zero hJ.ne_zero) hd

/-- The real metric-divergence wave transforms as a scalar on every regular C² coordinate overlap. -/
theorem wave_pullback_real {f : Covector → ℝ} (hφ : ContDiffAt ℝ 2 φ x)
    (hg : DifferentiableAt ℝ g (φ x)) (hs : ∀ᶠ y in 𝓝 (φ x), (g y).IsSymm)
    (hd : (g (φ x)).det < 0) (hJ : IsUnit (jacobianMatrix (fderiv ℝ φ x)).det)
    (hf : ContDiffAt ℝ 2 f (φ x)) :
    wave (pullMetric g φ (fderiv ℝ φ)) (f ∘ φ) x = wave g f (φ x) := by
  have hs' : ∀ᶠ z in 𝓝 x, (pullMetric g φ (fderiv ℝ φ) z).IsSymm :=
    (hφ.continuousAt.eventually hs).mono fun z hz => pull_symmetric _ _ hz
  have hA : Matrix.IsSymm (covariantHessian g f (φ x)) := by
    ext i j
    exact hessian_symmetric hg hs hf j i
  have hM := hessianMatrix_pullback hφ hg hs.self_of_nhds (isUnit_iff_ne_zero.mpr hd.ne) hJ hf
  have hP : Matrix.IsSymm (covariantHessian (pullMetric g φ (fderiv ℝ φ)) (f ∘ φ) x) := by
    rw [hM]
    exact pull_symmetric _ _ hA
  rw [wave_eq_hessianTrace (differentiableAt_pullMetric hφ hg) hs' (pull_negative hd hJ) (hf.comp x hφ),
    wave_eq_hessianTrace hg hs hd hf]
  simp only [hessianTrace, smul_eq_mul]
  rw [contraction_trace _ _ hP, contraction_trace _ _ hA, hM]
  exact trace_pullback _ _ _ hJ

/-- Applying real and imaginary projections gives scalar covariance for the full complex wave. -/
theorem wave_pullback_complex {f : Covector → ℂ} (hφ : ContDiffAt ℝ 2 φ x)
    (hg : DifferentiableAt ℝ g (φ x)) (hs : ∀ᶠ y in 𝓝 (φ x), (g y).IsSymm)
    (hd : (g (φ x)).det < 0) (hJ : IsUnit (jacobianMatrix (fderiv ℝ φ x)).det)
    (hf : ContDiffAt ℝ 2 f (φ x)) :
    wave (pullMetric g φ (fderiv ℝ φ)) (f ∘ φ) x = wave g f (φ x) := by
  have hL (L : ℂ →L[ℝ] ℝ) : L (wave (pullMetric g φ (fderiv ℝ φ)) (f ∘ φ) x) = L (wave g f (φ x)) := by
    rw [← wave_clm L (differentiableAt_pullMetric hφ hg) (pull_negative hd hJ) (hf.comp x hφ),
      ← wave_clm L hg hd hf]
    exact wave_pullback_real (f := L ∘ f) hφ hg hs hd hJ (L.contDiff.contDiffAt.comp (φ x) hf)
  exact Complex.ext (hL Complex.reCLM) (hL Complex.imCLM)

/-- Replacing component representatives by equal germs preserves the full divergence-form operator. -/
theorem wave_germ {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {g' : Covector → Mat4} {f f' : Covector → F} (hg : g =ᶠ[𝓝 x] g') (hf : f =ᶠ[𝓝 x] f') :
    wave g f x = wave g' f' x := by
  have he (i : Fin 4) : (fun y => flux g f y i) =ᶠ[𝓝 x] fun y => flux g' f' y i := by
    filter_upwards [hg, hf.fderiv (𝕜 := ℝ)] with y hy hdy
    simp only [flux, coefficient, hy, hdy]
  simp only [wave, hg.self_of_nhds, fun i => (he i).fderiv_eq (𝕜 := ℝ)]

end FoliationQM.CurvedWaveOverlap
