module

public import FoliationQM.CurvedNormalizedQuantumForce
public import FoliationQM.CurvedDefectTransport
public import FoliationQM.CurvedGradientTransport
public import FoliationQM.CurvedVectorTransport

/-!
# Physical quantum velocities and forces under nonlinear chart changes

The phase gradient transforms by the actual coordinate differential.
Scalar covariance of the computed defect then transports its normalized
velocity as a vector-field germ. Its regularity in the second chart is
derived from the target KG solution; no independent second KG premise or
assumed force transformation is introduced. Differentiating the vector
transport germ gives covariance of the genuine accelerations.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.CurvedQuantumTransport

open LorentzMatrixGroup RNCCoordinateVolumeChange CurvedScalarAtlasOverlap
  CurvedQuantumVelocity CurvedPolarKG CurvedNormalizedQuantumForce CurvedPositiveNormalization
  CurvedCovariantDerivative CurvedKGTestResidual PolarSecondDifferential
open scoped Topology Matrix.Norms.Operator
set_option backward.isDefEq.respectTransparency false

variable {φ : Covector → Covector} {g : Covector → Mat4} {R S : Covector → ℝ}
  {x : Covector}

/-- The actual coordinate differential transports the constant-mass phase-gradient velocity. -/
theorem velocity_pullback (p : MassiveParameters) (g : Covector → Mat4)
    {D : Covector → Covector →L[ℝ] Covector} (hφ : HasFDerivAt φ (D x) x)
    (hJ : IsUnit (jacobianMatrix (D x)).det) (hS : DifferentiableAt ℝ S (φ x)) :
    D x (velocity p (pullMetric g φ D) (S ∘ φ) x) = velocity p g S (φ x) := by
  unfold velocity
  rw [map_smul, CurvedGradientTransport.grad_pullback g hφ hJ hS]

/-- The phase velocity transformation holds as a genuine vector-field transport germ. -/
theorem velocity_pullback_germ (p : MassiveParameters) (g : Covector → Mat4)
    (hφ : ContDiffAt ℝ 2 φ x) (hJ : IsUnit (jacobianMatrix (fderiv ℝ φ x)).det)
    (hS : ContDiffAt ℝ 1 S (φ x)) :
    (fun y => fderiv ℝ φ y (velocity p (pullMetric g φ (fderiv ℝ φ)) (S ∘ φ) y))
      =ᶠ[𝓝 x] velocity p g S ∘ φ := by
  have hC : ContinuousAt (fun y => jacobianMatrix (fderiv ℝ φ y)) x :=
    jacobianMap.continuous.continuousAt.comp ((hφ.fderiv_right (m := 1) (by decide)).continuousAt)
  have hI : ∀ᶠ y in 𝓝 x, IsUnit (jacobianMatrix (fderiv ℝ φ y)) :=
    hC.eventually (Units.isOpen.mem_nhds ((jacobianMatrix (fderiv ℝ φ x)).isUnit_iff_isUnit_det.mpr hJ))
  filter_upwards [hφ.eventually (by decide),
    hφ.continuousAt.eventually (hS.eventually (by decide)), hI] with y hyφ hyS hyJ
  exact velocity_pullback p g (hyφ.differentiableAt (by decide)).hasFDerivAt
    ((jacobianMatrix (fderiv ℝ φ y)).isUnit_iff_isUnit_det.mp hyJ) hyS.differentiableAt_one

/-- Scalar defect covariance makes the normalized phase velocity transform by the actual chart differential. -/
theorem normalizedVelocity_pullback (p : MassiveParameters) (hφ : ContDiffAt ℝ 3 φ x)
    (hg : ContDiffAt ℝ 2 g (φ x)) (hs : ∀ᶠ y in 𝓝 (φ x), (g y).IsSymm)
    (hd : (g (φ x)).det < 0) (hJ : IsUnit (jacobianMatrix (fderiv ℝ φ x)).det)
    (hR : ContDiffAt ℝ 2 R (φ x)) (hS : DifferentiableAt ℝ S (φ x)) :
    fderiv ℝ φ x (normalizedVelocity p (pullMetric g φ (fderiv ℝ φ)) (R ∘ φ) (S ∘ φ) x) =
      normalizedVelocity p g R S (φ x) := by
  unfold normalizedVelocity normalized
  rw [map_smul, CurvedDefectTransport.defect_pullback p hφ hg hs hd hJ hR,
    velocity_pullback p g (hφ.differentiableAt (by decide)).hasFDerivAt hJ hS]

/-- The normalized velocity transformation is a neighborhood identity, not merely a pointwise vector comparison. -/
theorem normalizedVelocity_pullback_germ (p : MassiveParameters) (hφ : ContDiffAt ℝ 3 φ x)
    (hg : ContDiffAt ℝ 2 g (φ x)) (hs : ∀ᶠ y in 𝓝 (φ x), (g y).IsSymm)
    (hd : (g (φ x)).det < 0) (hJ : IsUnit (jacobianMatrix (fderiv ℝ φ x)).det)
    (hR : ContDiffAt ℝ 2 R (φ x)) (hS : ContDiffAt ℝ 1 S (φ x)) :
    (fun y => fderiv ℝ φ y
      (normalizedVelocity p (pullMetric g φ (fderiv ℝ φ)) (R ∘ φ) (S ∘ φ) y))
      =ᶠ[𝓝 x] normalizedVelocity p g R S ∘ φ := by
  filter_upwards [CurvedDefectTransport.defect_pullback_germ p hφ hg hs hd hJ hR,
    velocity_pullback_germ p g (hφ.of_le (by decide)) hJ hS] with y hyq hyw
  change fderiv ℝ φ y ((Real.sqrt (1 + defect p (pullMetric g φ (fderiv ℝ φ)) (R ∘ φ) y))⁻¹ •
    velocity p (pullMetric g φ (fderiv ℝ φ)) (S ∘ φ) y) =
      (Real.sqrt (1 + defect p g R (φ y)))⁻¹ • velocity p g S (φ y)
  rw [map_smul, hyq, hyw]
  rfl

/-- The actual unnormalized covariant acceleration transforms tensorially after differentiating the phase-velocity transport germ. -/
theorem acceleration_velocity_pullback (p : MassiveParameters) (hφ : ContDiffAt ℝ 2 φ x)
    (hg : DifferentiableAt ℝ g (φ x)) (hs : (g (φ x)).IsSymm)
    (hu : IsUnit (g (φ x)).det) (hJ : IsUnit (jacobianMatrix (fderiv ℝ φ x)).det)
    (hS : ContDiffAt ℝ 2 S (φ x)) :
    fderiv ℝ φ x (acceleration (pullMetric g φ (fderiv ℝ φ))
      (velocity p (pullMetric g φ (fderiv ℝ φ)) (S ∘ φ)) x) =
      acceleration g (velocity p g S) (φ x) := by
  have hup : IsUnit (pullMetric g φ (fderiv ℝ φ) x).det := by
    rw [pullMetric, det_pullMatrix]
    exact (hJ.pow 2).mul hu
  exact CurvedVectorTransport.acceleration_pullback hφ hg hs hu hJ
    (differentiableAt_velocity p (differentiableAt_pullMetric hφ hg) hup (hS.comp x hφ))
    (differentiableAt_velocity p hg hu hS)
    (velocity_pullback_germ p g hφ hJ (hS.of_le (by decide)))

/-- Target-solution regularity and scalar defect transport prove C¹ regularity of the actual normalized velocity in the second chart. -/
theorem contDiffAt_pullback_normalizedVelocity (p : MassiveParameters)
    (hφ : ContDiffAt ℝ 3 φ x) (hg : ContDiffAt ℝ 2 g (φ x))
    (hs : ∀ᶠ y in 𝓝 (φ x), (g y).IsSymm) (hd : (g (φ x)).det < 0)
    (hJ : IsUnit (jacobianMatrix (fderiv ℝ φ x)).det)
    (hR : ContDiffAt ℝ 2 R (φ x)) (hS : ContDiffAt ℝ 2 S (φ x)) (hp : 0 < R (φ x))
    (hKG : ∀ᶠ y in 𝓝 (φ x), kgOperator p g (amplitudeField R (fun z => S z / p.hbar)) y = 0)
    (hq : 0 < 1 + defect p g R (φ x)) :
    ContDiffAt ℝ 1
      (normalizedVelocity p (pullMetric g φ (fderiv ℝ φ)) (R ∘ φ) (S ∘ φ)) x := by
  have hup : IsUnit (pullMetric g φ (fderiv ℝ φ) x).det := by
    rw [pullMetric, det_pullMatrix]
    exact (hJ.pow 2).mul (isUnit_iff_ne_zero.mpr hd.ne)
  have hw := contDiffAt_velocity p
    ((CurvedRiemannOverlap.contDiffAt_pullMetric hφ hg).of_le (by decide)) hup
    (hS.comp x (hφ.of_le (by decide)))
  have hqr := CurvedDefectTransport.contDiffAt_pullback_defect p hφ hg hs hd hJ hR
    (CurvedMassDefectRegularity.contDiffAt_defect p hg hd hs hR hS hp hKG)
  have hqp : 0 < 1 + defect p (pullMetric g φ (fderiv ℝ φ)) (R ∘ φ) x := by
    rwa [CurvedDefectTransport.defect_pullback p hφ hg hs hd hJ hR]
  exact contDiffAt_normalized hw hqr hqp

/-- The genuine normalized KG acceleration transforms as a vector on a regular nonlinear overlap, with only the target KG germ assumed. -/
theorem acceleration_normalized_pullback (p : MassiveParameters)
    (hφ : ContDiffAt ℝ 3 φ x) (hg : ContDiffAt ℝ 2 g (φ x))
    (hs : ∀ᶠ y in 𝓝 (φ x), (g y).IsSymm) (hd : (g (φ x)).det < 0)
    (hJ : IsUnit (jacobianMatrix (fderiv ℝ φ x)).det)
    (hR : ContDiffAt ℝ 2 R (φ x)) (hS : ContDiffAt ℝ 2 S (φ x)) (hp : 0 < R (φ x))
    (hKG : ∀ᶠ y in 𝓝 (φ x), kgOperator p g (amplitudeField R (fun z => S z / p.hbar)) y = 0)
    (hq : 0 < 1 + defect p g R (φ x)) :
    fderiv ℝ φ x (acceleration (pullMetric g φ (fderiv ℝ φ))
      (normalizedVelocity p (pullMetric g φ (fderiv ℝ φ)) (R ∘ φ) (S ∘ φ)) x) =
      acceleration g (normalizedVelocity p g R S) (φ x) :=
  CurvedVectorTransport.acceleration_pullback (hφ.of_le (by decide))
    (hg.differentiableAt (by decide)) hs.self_of_nhds (isUnit_iff_ne_zero.mpr hd.ne) hJ
    (contDiffAt_pullback_normalizedVelocity p hφ hg hs hd hJ hR hS hp hKG hq).differentiableAt_one
    (contDiffAt_normalizedVelocity p hg hd hs hR hS hp hKG hq).differentiableAt_one
    (normalizedVelocity_pullback_germ p hφ hg hs hd hJ hR (hS.of_le (by decide)))

/-- Transporting the actual acceleration computed in the second chart gives precisely the target's exact projected quantum force. -/
theorem normalized_force_pullback (p : MassiveParameters)
    (hφ : ContDiffAt ℝ 3 φ x) (hg : ContDiffAt ℝ 2 g (φ x))
    (hs : ∀ᶠ y in 𝓝 (φ x), (g y).IsSymm) (hd : (g (φ x)).det < 0)
    (hJ : IsUnit (jacobianMatrix (fderiv ℝ φ x)).det)
    (hR : ContDiffAt ℝ 2 R (φ x)) (hS : ContDiffAt ℝ 2 S (φ x)) (hp : 0 < R (φ x))
    (hKG : ∀ᶠ y in 𝓝 (φ x), kgOperator p g (amplitudeField R (fun z => S z / p.hbar)) y = 0)
    (hq : 0 < 1 + defect p g R (φ x)) :
    fderiv ℝ φ x (acceleration (pullMetric g φ (fderiv ℝ φ))
      (normalizedVelocity p (pullMetric g φ (fderiv ℝ φ)) (R ∘ φ) (S ∘ φ)) x) =
      (p.c ^ 2 / 2) • CurvedLogGradientProjection.projectedGradient p.c g
        (normalizedVelocity p g R S) (fun y => Real.log (1 + defect p g R y)) (φ x) := by
  rw [acceleration_normalized_pullback p hφ hg hs hd hJ hR hS hp hKG hq,
    normalized_force p hg hd hs hR hS hp hKG hq]

end FoliationQM.CurvedQuantumTransport
