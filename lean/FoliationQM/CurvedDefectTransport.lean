module

public import FoliationQM.CurvedPolarKG
public import FoliationQM.CurvedWaveOverlap
public import FoliationQM.CurvedRicciOverlap

/-!
# The computed quantum mass defect on nonlinear chart overlaps

Both terms in the actual defect are scalar: the metric-volume wave of the
amplitude and the computed scalar curvature. Their established coordinate
laws give pointwise and neighborhood covariance under a regular C³ change
of chart. Equal local representatives give the same computed defect.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.CurvedDefectTransport

open LorentzMatrixGroup RNCCoordinateVolumeChange CurvedScalarAtlasOverlap CurvedPolarKG
open scoped Topology Matrix.Norms.Operator

variable {φ : Covector → Covector} {g k : Covector → Mat4} {R A : Covector → ℝ}
  {x : Covector}

/-- The actual wave-and-curvature defect transforms as a scalar under a regular nonlinear chart transition. -/
theorem defect_pullback (p : MassiveParameters) (hφ : ContDiffAt ℝ 3 φ x)
    (hg : ContDiffAt ℝ 2 g (φ x)) (hs : ∀ᶠ y in 𝓝 (φ x), (g y).IsSymm)
    (hd : (g (φ x)).det < 0) (hJ : IsUnit (jacobianMatrix (fderiv ℝ φ x)).det)
    (hR : ContDiffAt ℝ 2 R (φ x)) :
    defect p (pullMetric g φ (fderiv ℝ φ)) (R ∘ φ) x = defect p g R (φ x) := by
  unfold defect
  rw [CurvedWaveOverlap.wave_pullback_real (hφ.of_le (by decide))
    (hg.differentiableAt (by decide)) hs hd hJ hR,
    CurvedRicciOverlap.scalar_pullback hφ hg hs (isUnit_iff_ne_zero.mpr hd.ne) hJ]
  rfl

/-- Equal metric and amplitude germs give exactly the same computed quantum mass defect. -/
theorem defect_congr (p : MassiveParameters) (hg : k =ᶠ[𝓝 x] g) (hR : A =ᶠ[𝓝 x] R) :
    defect p k A x = defect p g R x := by
  unfold defect
  rw [CurvedWaveOverlap.wave_germ hg hR, CurvedRicciOverlap.scalar_congr hg, hR.self_of_nhds]

/-- Actual overlap representatives agreeing locally with the pullback have the target chart's scalar defect. -/
theorem defect_overlap (p : MassiveParameters) (hφ : ContDiffAt ℝ 3 φ x)
    (hg : ContDiffAt ℝ 2 g (φ x)) (hs : ∀ᶠ y in 𝓝 (φ x), (g y).IsSymm)
    (hd : (g (φ x)).det < 0) (hJ : IsUnit (jacobianMatrix (fderiv ℝ φ x)).det)
    (hR : ContDiffAt ℝ 2 R (φ x))
    (hk : k =ᶠ[𝓝 x] pullMetric g φ (fderiv ℝ φ)) (hA : A =ᶠ[𝓝 x] R ∘ φ) :
    defect p k A x = defect p g R (φ x) :=
  (defect_congr p hk hA).trans (defect_pullback p hφ hg hs hd hJ hR)

/-- The scalar transformation is an equality on a neighborhood, so actual derivatives and regularity can be transported. -/
theorem defect_pullback_germ (p : MassiveParameters) (hφ : ContDiffAt ℝ 3 φ x)
    (hg : ContDiffAt ℝ 2 g (φ x)) (hs : ∀ᶠ y in 𝓝 (φ x), (g y).IsSymm)
    (hd : (g (φ x)).det < 0) (hJ : IsUnit (jacobianMatrix (fderiv ℝ φ x)).det)
    (hR : ContDiffAt ℝ 2 R (φ x)) :
    defect p (pullMetric g φ (fderiv ℝ φ)) (R ∘ φ) =ᶠ[𝓝 x] defect p g R ∘ φ := by
  have hdet : ContinuousAt (fun y => (g y).det) (φ x) :=
    (continuous_id.matrix_det : Continuous (Matrix.det : Mat4 → ℝ)).continuousAt.comp hg.continuousAt
  have hC : ContinuousAt (fun y => jacobianMatrix (fderiv ℝ φ y)) x :=
    jacobianMap.continuous.continuousAt.comp ((hφ.fderiv_right (m := 2) (by decide)).continuousAt)
  have hI : ∀ᶠ y in 𝓝 x, IsUnit (jacobianMatrix (fderiv ℝ φ y)) :=
    hC.eventually (Units.isOpen.mem_nhds ((jacobianMatrix (fderiv ℝ φ x)).isUnit_iff_isUnit_det.mpr hJ))
  filter_upwards [hφ.eventually (by decide), hφ.continuousAt.eventually (hg.eventually (by decide)),
    hφ.continuousAt.eventually hs.eventually_nhds,
    hφ.continuousAt.eventually (hdet.eventually (Iio_mem_nhds hd)), hI,
    hφ.continuousAt.eventually (hR.eventually (by decide))]
    with y hyφ hyg hys hyd hyJ hyR
  exact defect_pullback p hyφ hyg hys hyd
    ((jacobianMatrix (fderiv ℝ φ y)).isUnit_iff_isUnit_det.mp hyJ) hyR

/-- Genuine C¹ regularity of the target defect transfers to the defect computed in the pulled-back chart. -/
theorem contDiffAt_pullback_defect (p : MassiveParameters) (hφ : ContDiffAt ℝ 3 φ x)
    (hg : ContDiffAt ℝ 2 g (φ x)) (hs : ∀ᶠ y in 𝓝 (φ x), (g y).IsSymm)
    (hd : (g (φ x)).det < 0) (hJ : IsUnit (jacobianMatrix (fderiv ℝ φ x)).det)
    (hR : ContDiffAt ℝ 2 R (φ x)) (hq : ContDiffAt ℝ 1 (defect p g R) (φ x)) :
    ContDiffAt ℝ 1 (defect p (pullMetric g φ (fderiv ℝ φ)) (R ∘ φ)) x :=
  (hq.comp x (hφ.of_le (by decide))).congr_of_eventuallyEq
    (defect_pullback_germ p hφ hg hs hd hJ hR)

/-- The actual differential of the computed defect obeys the scalar chain rule on a nonlinear overlap. -/
theorem fderiv_defect_pullback (p : MassiveParameters) (hφ : ContDiffAt ℝ 3 φ x)
    (hg : ContDiffAt ℝ 2 g (φ x)) (hs : ∀ᶠ y in 𝓝 (φ x), (g y).IsSymm)
    (hd : (g (φ x)).det < 0) (hJ : IsUnit (jacobianMatrix (fderiv ℝ φ x)).det)
    (hR : ContDiffAt ℝ 2 R (φ x)) (hq : DifferentiableAt ℝ (defect p g R) (φ x)) :
    fderiv ℝ (defect p (pullMetric g φ (fderiv ℝ φ)) (R ∘ φ)) x =
      (fderiv ℝ (defect p g R) (φ x)).comp (fderiv ℝ φ x) := by
  rw [(defect_pullback_germ p hφ hg hs hd hJ hR).fderiv_eq]
  exact (hq.hasFDerivAt.comp x (hφ.differentiableAt (by decide)).hasFDerivAt).fderiv

end FoliationQM.CurvedDefectTransport
