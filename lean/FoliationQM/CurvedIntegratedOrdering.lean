module

public import FoliationQM.CurvedGreenBoundary
public import FoliationQM.RNCDeWittOrdering

/-!
# Integrated symmetric ordering and its boundary divergence

The selected normal-center prescription has scalar value
−ℏ² R □g R + ℏ² Scal R²/6. In arbitrary coordinates the difference from
the gradient expression is the divergence of the densitized amplitude flux.
This divergence is kept explicitly for finite actions with boundary.
-/

@[expose] public section
noncomputable section
open scoped Matrix.Norms.Operator
namespace FoliationQM.CurvedIntegratedOrdering

open MeasureTheory LorentzMatrixGroup RNCVolumeDensity RNCCoordinateCurvature
open CurvedWaveDivergence CurvedFluxGreen CurvedGreenBoundary

/-- Value of the symmetric prescription as a scalar action density. -/
def ordered (ℏ : ℝ) (g : Covector → Mat4) (R : Covector → ℝ) (x : Covector) : ℝ :=
  -(ℏ ^ 2) * R x * wave g R x + (ℏ ^ 2 / 6) * scalar g x * (R x) ^ 2

/-- The first-order gradient action density with the same selected curvature term. -/
def gradient (ℏ : ℝ) (g : Covector → Mat4) (R : Covector → ℝ) (x : Covector) : ℝ :=
  ℏ ^ 2 * kinetic g R R x + (ℏ ^ 2 / 6) * scalar g x * (R x) ^ 2

/-- At a normal center this scalar density is precisely the literal symmetric half-density ordering. -/
theorem ordered_at_center {g : Covector → Mat4} (h : RNCNormalChart.IsNormal g)
    (hg : ContDiffAt ℝ 2 g 0) {R : Covector → ℝ} (hR : ContDiffAt ℝ 2 R 0) (ℏ : ℝ) :
    RNCDeWittOrdering.symmetricKinetic ℏ g R = ordered ℏ g R 0 := by
  simpa only [ordered, wave_real] using RNCDeWittOrdering.symmetric_center h hg hR ℏ

/-- In any smooth coordinate region the exact difference is the divergence of the amplitude flux. -/
theorem ordered_eq_gradient_sub_boundary {g : Covector → Mat4} {R : Covector → ℝ} {x : Covector}
    (hg : DifferentiableAt ℝ g x) (hd : (g x).det < 0) (hR : ContDiffAt ℝ 2 R x) (ℏ : ℝ) :
    volumeFactor (g x) * ordered ℏ g R x = volumeFactor (g x) * gradient ℏ g R x -
      ℏ ^ 2 * boundaryDivergence g R R x := by
  have he := first_green hg hd (hR.differentiableAt (by decide)) hR
  rw [he]
  simp only [ordered, gradient, star_trivial, smul_eq_mul]
  ring

/-- For finite integrals the difference of the two action expressions is exactly the integrated boundary divergence. -/
theorem action_with_boundary {U : Set Covector} (hU : MeasurableSet U) {g : Covector → Mat4}
    {R : Covector → ℝ} (ℏ : ℝ) (hg : ∀ x ∈ U, DifferentiableAt ℝ g x)
    (hd : ∀ x ∈ U, (g x).det < 0) (hR : ∀ x ∈ U, ContDiffAt ℝ 2 R x)
    (hgrad : IntegrableOn (fun x => volumeFactor (g x) * gradient ℏ g R x) U)
    (hb : IntegrableOn (boundaryDivergence g R R) U) :
    (∫ x in U, volumeFactor (g x) * ordered ℏ g R x) =
    (∫ x in U, volumeFactor (g x) * gradient ℏ g R x) -
      ℏ ^ 2 * ∫ x in U, boundaryDivergence g R R x := by
  calc
    _ = ∫ x in U, volumeFactor (g x) * gradient ℏ g R x - ℏ ^ 2 * boundaryDivergence g R R x :=
      setIntegral_congr_fun hU fun x hx => ordered_eq_gradient_sub_boundary (hg x hx) (hd x hx) (hR x hx) ℏ
    _ = _ := by rw [integral_sub hgrad (hb.const_mul _), integral_const_mul]

/-- The actual boundary divergence integrates to zero for a compact interior test. -/
theorem compact_boundary {K : Type*} [RCLike K] {g : Covector → Mat4} {u f : Covector → K}
    {U : Set Covector} (hU : MeasurableSet U) (hu : ContDiff ℝ 1 u) (hc : HasCompactSupport u)
    (hs : tsupport u ⊆ U) (hg : ∀ x ∈ U, ContDiffAt ℝ 1 g x)
    (hd : ∀ x ∈ U, (g x).det < 0) (hf : ∀ x ∈ U, ContDiffAt ℝ 2 f x) :
    (∫ x in U, boundaryDivergence g u f x) = 0 := by
  obtain ⟨hk, hw⟩ := integrable_pairings hu hc hs hg hd hf
  rw [integral_first_green hU (fun x hx => (hg x hx).differentiableAt_one) hd
    (fun _ _ => hu.differentiable_one.differentiableAt) hf hk hw, integral_green hu hc hs hg hd hf,
    neg_add_cancel]

/-- The compact-amplitude symmetric action equals the first-order action, including its curvature term. -/
theorem compact_action {U : Set Covector} (hU : MeasurableSet U) {g : Covector → Mat4}
    {R : Covector → ℝ} (ℏ : ℝ) (hR : ContDiff ℝ 2 R) (hc : HasCompactSupport R)
    (hs : tsupport R ⊆ U) (hg : ∀ x ∈ U, ContDiffAt ℝ 2 g x) (hd : ∀ x ∈ U, (g x).det < 0) :
    (∫ x in U, volumeFactor (g x) * ordered ℏ g R x) =
      ∫ x in U, volumeFactor (g x) * gradient ℏ g R x := by
  have hg₁ (x) (hx : x ∈ U) : ContDiffAt ℝ 1 g x := (hg x hx).of_le (by decide)
  have hR₁ : ContDiff ℝ 1 R := hR.of_le (by decide)
  obtain ⟨hk, hw⟩ := integrable_pairings hR₁ hc hs hg₁ hd (fun _ _ => hR.contDiffAt)
  have hcurv : IntegrableOn (fun x => volumeFactor (g x) * (ℏ ^ 2 / 6 * scalar g x * R x ^ 2)) U := by
    apply Integrable.integrableOn
    have hcont : ContinuousOn (fun x => volumeFactor (g x) * (ℏ ^ 2 / 6 * scalar g x * R x ^ 2)) (tsupport R) := by
      intro x hx
      have hvol := (RNCMetricHalfDensity.volume_smooth (hd x (hs hx)) 2).comp x (hg x (hs hx))
      exact (hvol.continuousAt.mul ((continuousAt_const.mul
        (CurvedFluxRegularity.scalar_continuousAt (hg x (hs hx)) (hd x (hs hx)))).mul
          (hR.continuous.continuousAt.pow 2))).continuousWithinAt
    apply (hcont.integrableOn_compact hc).integrable_of_forall_notMem_eq_zero
    intro x hx
    simp [image_eq_zero_of_notMem_tsupport hx]
  have hb : IntegrableOn (boundaryDivergence g R R) U :=
    (hk.add hw).congr <| (ae_restrict_mem hU).mono fun x hx =>
      (first_green (hg₁ x hx).differentiableAt_one (hd x hx) hR₁.differentiable_one.differentiableAt hR.contDiffAt).symm
  have hgrad : IntegrableOn (fun x => volumeFactor (g x) * gradient ℏ g R x) U := by
    apply ((hk.const_mul (ℏ ^ 2)).add hcurv).congr
    filter_upwards with x
    simp only [gradient, smul_eq_mul, Pi.add_apply]
    ring
  rw [action_with_boundary hU ℏ (fun x hx => (hg₁ x hx).differentiableAt_one) hd
    (fun _ _ => hR.contDiffAt) hgrad hb, compact_boundary hU hR₁ hc hs hg₁ hd
      (fun _ _ => hR.contDiffAt), mul_zero, sub_zero]

end FoliationQM.CurvedIntegratedOrdering
