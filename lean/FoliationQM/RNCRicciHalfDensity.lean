module

public import FoliationQM.RNCCoordinateCurvature
public import FoliationQM.RNCMetricCompatibilityDerivative
public import FoliationQM.RNCExpansionContraction

/-!
# Identifying the normal-coordinate half-density Hessian with Ricci

Differentiating metric compatibility expresses the trace of the metric Hessian
as twice the trace of a Christoffel derivative. The radial cyclic identity
expresses coordinate Ricci through the same traces. Symmetry of the actual
half-density Hessian fixes the coefficient and the sign in Lemma 9.1.
-/

@[expose] public section
noncomputable section
open scoped Matrix.Norms.Operator Topology
namespace FoliationQM.RNCRicciHalfDensity

open Asymptotics LorentzMatrixGroup RealLorentzFrame RNCCoordinateConnection RNCCoordinateCurvature
open RNCNormalChart RNCMetricCompatibilityDerivative RNCVolumeDensity RNCHalfDensityJet

variable {g : Covector → Mat4}

/-- Smoothness of the actual half-density near an orthonormal normal center, to the order of the metric. -/
theorem weight_contDiff (h : IsNormal g) {k : WithTop ℕ∞} (hg : ContDiffAt ℝ k g 0) :
    ContDiffAt ℝ k (metricWeight ∘ g) 0 :=
  (RNCMetricHalfDensity.weight_smooth (by rw [h.metric_center, eta_det]; norm_num) k).comp 0 hg

/-- The signed trace of the metric Hessian is twice the trace of the corresponding Christoffel derivative. -/
theorem metric_trace (h : IsNormal g) (hg : ContDiffAt ℝ 2 g 0) (a b : Fin 4) :
    (eta * fderiv ℝ (fderiv ℝ g) 0 (axis a) (axis b)).trace = 2 * traceGamma g 0 a b := by
  simp only [eta, Matrix.trace, Matrix.diag, Matrix.diagonal_mul, traceGamma, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [hessian_metric_diagonal h hg a b i]
  change sign i * (2 * sign i * _) = 2 * _
  ring_nf
  simp [sq, sign_sq, dGamma]

/-- The trace of a Christoffel derivative is twice the corresponding entry of the half-density Hessian. -/
theorem traceGamma_eq (h : IsNormal g) (hg : ContDiffAt ℝ 2 g 0) (a b : Fin 4) :
    traceGamma g 0 a b = 2 * fderiv ℝ (fderiv ℝ (metricWeight ∘ g)) 0 (axis a) (axis b) := by
  rw [weight_hessian h hg, metric_trace h hg]
  ring

/-- The actual metric fourth-root Hessian equals minus one sixth of the coordinate Ricci tensor in every pair of coordinate directions. -/
theorem mixed_hessian (h : IsNormal g) (hg : ContDiffAt ℝ 2 g 0) (a b : Fin 4) :
    fderiv ℝ (fderiv ℝ (metricWeight ∘ g)) 0 (axis a) (axis b) = -ricci g 0 a b / 6 := by
  have hs := (weight_contDiff h hg).isSymmSndFDerivAt (by simp) (axis b) (axis a)
  rw [ricci_center h hg, traceGamma_eq h hg, traceGamma_eq h hg, hs]
  ring

/-- The coordinate Ricci tensor at the normal center is symmetric. -/
theorem ricci_symmetric (h : IsNormal g) (hg : ContDiffAt ℝ 2 g 0) (a b : Fin 4) :
    ricci g 0 a b = ricci g 0 b a := by
  linarith [mixed_hessian h hg a b, mixed_hessian h hg b a,
    (weight_contDiff h hg).isSymmSndFDerivAt (by simp) (axis a) (axis b)]

/-- Equality on coordinate basis pairs determines a continuous bilinear map on the full real coordinate space. -/
theorem bilinear_ext_axis {A B : Covector →L[ℝ] Covector →L[ℝ] ℝ}
    (h : ∀ i j, A (axis i) (axis j) = B (axis i) (axis j)) : A = B := by
  ext u v
  conv_lhs => rw [show u = ∑ i, u i • axis i from pi_eq_sum_univ' u,
                  show v = ∑ j, v j • axis j from pi_eq_sum_univ' v]
  conv_rhs => rw [show u = ∑ i, u i • axis i from pi_eq_sum_univ' u,
                  show v = ∑ j, v j • axis j from pi_eq_sum_univ' v]
  simp only [map_sum, sum_apply, map_smul, smul_apply, h]

/-- The true fourth-root Hessian agrees as a full bilinear map with the quadratic normal-coordinate model formed from actual Ricci. -/
theorem full_hessian (h : IsNormal g) (hg : ContDiffAt ℝ 2 g 0) :
    fderiv ℝ (fderiv ℝ (metricWeight ∘ g)) 0 = hessian (ricci g 0) := by
  apply bilinear_ext_axis
  intro i j
  rw [mixed_hessian h hg, hessian_apply]
  change _ = -(form (ricci g 0) (Pi.single i 1) (Pi.single j 1) +
    form (ricci g 0) (Pi.single j 1) (Pi.single i 1)) / 12
  rw [form_basis (ricci g 0) i j, form_basis (ricci g 0) j i, ricci_symmetric h hg j i]
  ring

/-- The coordinate d'Alembertian of the actual positive fourth root at the center equals minus one sixth of the scalar curvature of the given metric. -/
theorem box_metricWeight (h : IsNormal g) (hg : ContDiffAt ℝ 2 g 0) :
    PolarSecondDifferential.box (metricWeight ∘ g) axis 0 = -scalar g 0 / 6 := by
  have hw : ContDiffAt ℝ 1 (fderiv ℝ (metricWeight ∘ g)) 0 :=
    (weight_contDiff h hg).fderiv_right (by decide)
  have hd (i : Fin 4) : PolarSecondDifferential.secondDirectionalDerivative (metricWeight ∘ g) (axis i) 0 =
      -ricci g 0 i i / 6 := by
    have he := (ContinuousLinearMap.apply ℝ ℝ (axis i)).hasFDerivAt.comp 0 hw.differentiableAt_one.hasFDerivAt
    exact (congrArg (fun L : Covector →L[ℝ] ℝ => L (axis i)) he.fderiv).trans (mixed_hessian h hg i i)
  rw [scalar_center h]
  simp only [PolarSecondDifferential.box, hd, scalarCurvature]
  ring

/-- In a C³ radial normal chart the actual metric fourth root has the v13 Ricci polynomial with a uniform cubic remainder. -/
theorem metricWeight_expansion (h : IsNormal g) (hg : ContDiffAt ℝ 3 g 0) :
    ((metricWeight ∘ g) - weight (ricci g 0)) =O[𝓝 0] fun y => ‖y‖ ^ 3 := by
  have hg₂ : ContDiffAt ℝ 2 g 0 := hg.of_le (by decide)
  have hd := hg.differentiableAt (by decide)
  have hj := RNCMetricHalfDensity.normal_value_gradient hd h.metric_center (metric_gradient_zero h hd)
  exact (RNCExpansionContraction.expansion_iff_jet (weight_contDiff h hg)).mpr
    ⟨hj.1, hj.2, full_hessian h hg₂⟩

end FoliationQM.RNCRicciHalfDensity
