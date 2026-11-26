module

public import FoliationQM.CurvedPolarKG
public import FoliationQM.CurvedScalarGradient

/-!
# On-solution regularity of the actual curved mass defect

The wave-and-curvature definition of the mass defect agrees, on an actual
positive-amplitude KG solution neighborhood, with the inverse-metric
phase-gradient expression. Its C¹ regularity and differential therefore
follow from C² metric and polar data without any C³ hypothesis.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.CurvedMassDefectRegularity

open LorentzMatrixGroup CurvedGradientCovariance CurvedScalarGradient
  CurvedPolarKG CurvedKGTestResidual PolarSecondDifferential
open scoped Topology Matrix.Norms.Operator
set_option backward.isDefEq.respectTransparency false

variable {g : Covector → Mat4} {R S : Covector → ℝ} {x : Covector}

/-- On a genuine KG solution neighborhood the computed defect equals its first-derivative phase expression. -/
theorem eventually_defect_eq (p : MassiveParameters) (hg : ContDiffAt ℝ 2 g x)
    (hd : (g x).det < 0) (hs : ∀ᶠ y in 𝓝 x, (g y).IsSymm)
    (hR : ContDiffAt ℝ 2 R x) (hS : ContDiffAt ℝ 2 S x) (hp : 0 < R x)
    (hKG : ∀ᶠ y in 𝓝 x, kgOperator p g (amplitudeField R (fun z => S z / p.hbar)) y = 0) :
    defect p g R =ᶠ[𝓝 x] fun y => pairing g S S y / (p.m ^ 2 * p.c ^ 2) - 1 := by
  have hdet : ContinuousAt (fun y => (g y).det) x :=
    (continuous_id.matrix_det : Continuous (Matrix.det : Mat4 → ℝ)).continuousAt.comp hg.continuousAt
  filter_upwards [hg.eventually (by decide), hR.eventually (by decide), hS.eventually (by decide),
    hdet.eventually (Iio_mem_nhds hd), hR.continuousAt.eventually (Ioi_mem_nhds hp), hs, hKG]
    with y hgy hRy hSy hdy hpy hsy hky
  exact defect_eq p (hgy.differentiableAt (by decide)) hdy hsy hRy hSy hpy hky

/-- The actual wave-and-curvature mass defect is C¹ on a positive polar KG solution germ, with only C² input data. -/
theorem contDiffAt_defect (p : MassiveParameters) (hg : ContDiffAt ℝ 2 g x)
    (hd : (g x).det < 0) (hs : ∀ᶠ y in 𝓝 x, (g y).IsSymm)
    (hR : ContDiffAt ℝ 2 R x) (hS : ContDiffAt ℝ 2 S x) (hp : 0 < R x)
    (hKG : ∀ᶠ y in 𝓝 x, kgOperator p g (amplitudeField R (fun z => S z / p.hbar)) y = 0) :
    ContDiffAt ℝ 1 (defect p g R) x := by
  have hpair := contDiffAt_pairing (hg.of_le (by decide)) (isUnit_iff_ne_zero.mpr hd.ne) hS hS
  exact ((hpair.div_const (p.m ^ 2 * p.c ^ 2)).sub contDiffAt_const).congr_of_eventuallyEq
    (eventually_defect_eq p hg hd hs hR hS hp hKG)

/-- The computed defect has a genuine Fréchet derivative on each positive polar KG solution germ. -/
theorem differentiableAt_defect (p : MassiveParameters) (hg : ContDiffAt ℝ 2 g x)
    (hd : (g x).det < 0) (hs : ∀ᶠ y in 𝓝 x, (g y).IsSymm)
    (hR : ContDiffAt ℝ 2 R x) (hS : ContDiffAt ℝ 2 S x) (hp : 0 < R x)
    (hKG : ∀ᶠ y in 𝓝 x, kgOperator p g (amplitudeField R (fun z => S z / p.hbar)) y = 0) :
    DifferentiableAt ℝ (defect p g R) x :=
  (contDiffAt_defect p hg hd hs hR hS hp hKG).differentiableAt_one

/-- The actual defect differential is the phase-gradient norm differential divided by the constant mass scale. -/
theorem fderiv_defect (p : MassiveParameters) (hg : ContDiffAt ℝ 2 g x)
    (hd : (g x).det < 0) (hs : ∀ᶠ y in 𝓝 x, (g y).IsSymm)
    (hR : ContDiffAt ℝ 2 R x) (hS : ContDiffAt ℝ 2 S x) (hp : 0 < R x)
    (hKG : ∀ᶠ y in 𝓝 x, kgOperator p g (amplitudeField R (fun z => S z / p.hbar)) y = 0) :
    fderiv ℝ (defect p g R) x = (p.m ^ 2 * p.c ^ 2)⁻¹ • fderiv ℝ (pairing g S S) x := by
  have hpair := (contDiffAt_pairing (hg.of_le (by decide)) (isUnit_iff_ne_zero.mpr hd.ne) hS hS).differentiableAt_one
  have hdiff : HasFDerivAt (fun y => pairing g S S y / (p.m ^ 2 * p.c ^ 2) - 1)
      ((p.m ^ 2 * p.c ^ 2)⁻¹ • fderiv ℝ (pairing g S S) x) x := by
    convert (hpair.hasFDerivAt.const_mul (p.m ^ 2 * p.c ^ 2)⁻¹).sub_const 1 using 1
    funext y
    ring
  rw [(eventually_defect_eq p hg hd hs hR hS hp hKG).fderiv_eq, hdiff.fderiv]

/-- Raising the actual defect differential gives the same constant-scaled gradient of the phase-gradient norm. -/
theorem grad_defect (p : MassiveParameters) (hg : ContDiffAt ℝ 2 g x)
    (hd : (g x).det < 0) (hs : ∀ᶠ y in 𝓝 x, (g y).IsSymm)
    (hR : ContDiffAt ℝ 2 R x) (hS : ContDiffAt ℝ 2 S x) (hp : 0 < R x)
    (hKG : ∀ᶠ y in 𝓝 x, kgOperator p g (amplitudeField R (fun z => S z / p.hbar)) y = 0) :
    grad g (defect p g R) x = (p.m ^ 2 * p.c ^ 2)⁻¹ • grad g (pairing g S S) x := by
  have hc : components (defect p g R) x = (p.m ^ 2 * p.c ^ 2)⁻¹ • components (pairing g S S) x := by
    funext i
    change fderiv ℝ (defect p g R) x (RNCCoordinateConnection.axis i) = _
    rw [fderiv_defect p hg hd hs hR hS hp hKG]
    rfl
  rw [grad, hc, Matrix.mulVec_smul]
  rfl

/-- On an actual open positive-amplitude KG solution domain the computed mass defect is C¹. -/
theorem contDiffOn_defect (p : MassiveParameters) {U : Set Covector} (hU : IsOpen U)
    (hg : ∀ x ∈ U, ContDiffAt ℝ 2 g x) (hd : ∀ x ∈ U, (g x).det < 0)
    (hs : ∀ x ∈ U, (g x).IsSymm) (hR : ∀ x ∈ U, ContDiffAt ℝ 2 R x)
    (hS : ∀ x ∈ U, ContDiffAt ℝ 2 S x) (hp : ∀ x ∈ U, 0 < R x)
    (hKG : ∀ x ∈ U, kgOperator p g (amplitudeField R (fun z => S z / p.hbar)) x = 0) :
    ContDiffOn ℝ 1 (defect p g R) U := by
  intro x hx
  have hmem : ∀ᶠ y in 𝓝 x, y ∈ U := hU.mem_nhds hx
  exact (contDiffAt_defect p (hg x hx) (hd x hx)
    (hmem.mono fun y hy => hs y hy) (hR x hx) (hS x hx) (hp x hx)
    (hmem.mono fun y hy => hKG y hy)).contDiffWithinAt

end FoliationQM.CurvedMassDefectRegularity
