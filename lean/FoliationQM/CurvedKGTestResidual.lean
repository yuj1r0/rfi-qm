module

public import FoliationQM.CurvedKGFirstVariation
public import FoliationQM.CurvedWeakEquation

/-!
# The complex first variation and the curved Klein–Gordon residual

For v13 `eq:curved_KG_eq_thm`, compact interior variations move the
kinetic derivative to the field by Green's identity. The potential
contributes the signed mass coefficient from the action. Dividing the
resulting equation by the positive squared Planck constant gives the
curvature term with coefficient −1/6.
-/

@[expose] public section
noncomputable section
open scoped Matrix.Norms.Operator ComplexConjugate
namespace FoliationQM.CurvedKGTestResidual

open MeasureTheory LorentzMatrixGroup RNCCoordinateCurvature CurvedWaveDivergence
  CurvedFluxGreen CurvedPolarAction CurvedKGFirstVariation RNCVolumeDensity

/-- The signed, unnormalized Euler–Lagrange residual of the curved field action. -/
def residual (p : MassiveParameters) (g : Covector → Mat4) (ψ : Covector → ℂ) (x : Covector) : ℂ :=
  p.hbar ^ 2 • wave g ψ x + massTerm p g x • ψ x

/-- The normalized v13 Klein–Gordon operator with the geometric curvature coupling. -/
def kgOperator (p : MassiveParameters) (g : Covector → Mat4) (ψ : Covector → ℂ) (x : Covector) : ℂ :=
  wave g ψ x + (p.m ^ 2 * p.c ^ 2 / p.hbar ^ 2 - scalar g x / 6) • ψ x

/-- The complex residual is the normalized field equation multiplied by ℏ². -/
theorem residual_eq_smul_operator (p : MassiveParameters) (g : Covector → Mat4)
    (ψ : Covector → ℂ) (x : Covector) : residual p g ψ x = p.hbar ^ 2 • kgOperator p g ψ x := by
  rw [residual, kgOperator, smul_add, smul_smul]
  congr 2
  unfold massTerm
  field_simp [p.hbar_pos.ne']

/-- Positive ℏ lets weak-test detection of the residual determine the normalized equation. -/
theorem residual_zero_iff (p : MassiveParameters) (g : Covector → Mat4) (ψ : Covector → ℂ)
    (x : Covector) : residual p g ψ x = 0 ↔ kgOperator p g ψ x = 0 := by
  rw [residual_eq_smul_operator, smul_eq_zero]
  simp [p.hbar_pos.ne']

variable {g : Covector → Mat4} {x : Covector} {ψ η : Covector → ℂ}

/-- C² metric and field data give a continuous residual at every Lorentzian point. -/
theorem residual_continuousAt (p : MassiveParameters) (hg : ContDiffAt ℝ 2 g x)
    (hd : (g x).det < 0) (hψ : ContDiffAt ℝ 2 ψ x) : ContinuousAt (residual p g ψ) x :=
  ((continuousAt_const (y := p.hbar ^ 2)).smul
    (CurvedFluxRegularity.wave_continuousAt (hg.of_le (by decide)) hd hψ)).add
    ((massTerm_continuousAt p hg hd).smul hψ.continuousAt)

variable {U : Set Covector}

private theorem test_transfer (p : MassiveParameters) (hη : ContDiff ℝ 1 η)
    (hc : HasCompactSupport η) (hs : tsupport η ⊆ U)
    (hg : ∀ x ∈ U, ContDiffAt ℝ 2 g x) (hd : ∀ x ∈ U, (g x).det < 0)
    (hψ : ∀ x ∈ U, ContDiffAt ℝ 2 ψ x) :
    IntegrableOn (fun x => volumeFactor (g x) • cross p g η ψ x) U ∧
    IntegrableOn (fun x => volumeFactor (g x) • (star (η x) * residual p g ψ x)) U ∧
    (∫ x in U, volumeFactor (g x) • cross p g η ψ x) =
      -(∫ x in U, volumeFactor (g x) • (star (η x) * residual p g ψ x)) := by
  let A x := volumeFactor (g x) • kinetic g η ψ x
  let B x := volumeFactor (g x) • (star (η x) * wave g ψ x)
  let M x := volumeFactor (g x) • (star (η x) * (massTerm p g x • ψ x))
  have hg₁ (x) (hx : x ∈ U) := (hg x hx).of_le (show (1 : WithTop ℕ∞) ≤ 2 by decide)
  obtain ⟨hA, hB⟩ := integrable_pairings hη hc hs hg₁ hd hψ
  have hM : IntegrableOn M U :=
    (CurvedWeakEquation.integrable_pair (fun x hx => (hg x hx).continuousAt.continuousWithinAt)
      (F := fun x => massTerm p g x • ψ x) (fun x hx =>
        ((massTerm_continuousAt p (hg x hx) (hd x hx)).smul (hψ x hx).continuousAt).continuousWithinAt)
      hη.continuous hc hs).integrableOn
  have ha : (fun x => volumeFactor (g x) • cross p g η ψ x) = fun x => p.hbar ^ 2 • A x - M x := by
    funext x
    simp only [cross, A, M, smul_sub, mul_smul_comm, smul_comm (volumeFactor (g x)) (p.hbar ^ 2)]
  have hb : (fun x => volumeFactor (g x) • (star (η x) * residual p g ψ x)) =
      fun x => p.hbar ^ 2 • B x + M x := by
    funext x
    simp only [residual, B, M, mul_add, smul_add, mul_smul_comm, smul_comm (volumeFactor (g x)) (p.hbar ^ 2)]
  have ha' : IntegrableOn (fun x => p.hbar ^ 2 • A x) U :=
    Integrable.fun_smul (f := A) (μ := volume.restrict U) (p.hbar ^ 2) hA
  have hb' : IntegrableOn (fun x => p.hbar ^ 2 • B x) U :=
    Integrable.fun_smul (f := B) (μ := volume.restrict U) (p.hbar ^ 2) hB
  rw [ha, hb]
  refine ⟨ha'.sub hM, hb'.add hM, ?_⟩
  have hi : (∫ x in U, A x) = -(∫ x in U, B x) := integral_green hη hc hs hg₁ hd hψ
  rw [integral_sub ha' hM, integral_add hb' hM, integral_smul, integral_smul, hi, smul_neg]
  abel

/-- The weighted complex cross variation is integrable for every compact interior test. -/
theorem integrable_cross (p : MassiveParameters) (hη : ContDiff ℝ 1 η)
    (hc : HasCompactSupport η) (hs : tsupport η ⊆ U) (hg : ∀ x ∈ U, ContDiffAt ℝ 2 g x)
    (hd : ∀ x ∈ U, (g x).det < 0) (hψ : ∀ x ∈ U, ContDiffAt ℝ 2 ψ x) :
    IntegrableOn (fun x => volumeFactor (g x) • cross p g η ψ x) U :=
  (test_transfer p hη hc hs hg hd hψ).1

/-- The real volume-weighted cross term of the actual action is integrable as well. -/
theorem integrable_cross_re (p : MassiveParameters) (hη : ContDiff ℝ 1 η)
    (hc : HasCompactSupport η) (hs : tsupport η ⊆ U) (hg : ∀ x ∈ U, ContDiffAt ℝ 2 g x)
    (hd : ∀ x ∈ U, (g x).det < 0) (hψ : ∀ x ∈ U, ContDiffAt ℝ 2 ψ x) :
    IntegrableOn (fun x => volumeFactor (g x) * (cross p g η ψ x).re) U := by
  simpa only [Function.comp_apply, RCLike.re_eq_complex_re, Complex.smul_re, smul_eq_mul]
    using (integrable_cross p hη hc hs hg hd hψ).re

/-- Integrated complex first variation equals the negative weighted test of the residual. -/
theorem integral_cross_residual (p : MassiveParameters) (hη : ContDiff ℝ 1 η)
    (hc : HasCompactSupport η) (hs : tsupport η ⊆ U) (hg : ∀ x ∈ U, ContDiffAt ℝ 2 g x)
    (hd : ∀ x ∈ U, (g x).det < 0) (hψ : ∀ x ∈ U, ContDiffAt ℝ 2 ψ x) :
    (∫ x in U, volumeFactor (g x) • cross p g η ψ x) =
      -(∫ x in U, volumeFactor (g x) • (star (η x) * residual p g ψ x)) :=
  (test_transfer p hη hc hs hg hd hψ).2.2

/-- The real action couples its variation to both components of the continuous complex residual. -/
theorem integral_cross_re (p : MassiveParameters) (hη : ContDiff ℝ 1 η)
    (hc : HasCompactSupport η) (hs : tsupport η ⊆ U) (hg : ∀ x ∈ U, ContDiffAt ℝ 2 g x)
    (hd : ∀ x ∈ U, (g x).det < 0) (hψ : ∀ x ∈ U, ContDiffAt ℝ 2 ψ x) :
    (∫ x in U, volumeFactor (g x) * (cross p g η ψ x).re) =
      -CurvedWeakEquation.testIntegral U g η (residual p g ψ) := by
  obtain ⟨hL, hR, he⟩ := test_transfer p hη hc hs hg hd hψ
  calc
    _ = (∫ x in U, volumeFactor (g x) • cross p g η ψ x).re := by
      simpa only [RCLike.re_eq_complex_re, Complex.smul_re, smul_eq_mul] using integral_re hL
    _ = -(∫ x in U, volumeFactor (g x) • (star (η x) * residual p g ψ x)).re :=
      congrArg Complex.re he
    _ = _ := by
      apply congrArg Neg.neg
      simpa only [CurvedWeakEquation.testIntegral, RCLike.re_eq_complex_re, Complex.smul_re, smul_eq_mul,
        Complex.star_def] using (integral_re hR).symm

end FoliationQM.CurvedKGTestResidual
