module
public import FoliationQM.DiracEquation
public import FoliationQM.DiracSecondJet
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.Calculus.FDeriv.CompCLM
/-!
# Genuine flat-coordinate Dirac operator factorization

Source: v13's flat Dirac operator product preceding
`eq:spinor_quadratic_exact`. Both factors are the actual first-order
operators from DiracEquation. Local C2 regularity supplies the genuine
second Frechet derivative and its symmetry. The concrete Clifford
anticommutator then reduces the actual slashed square to the actual
Minkowski d'Alembertian, with all mass cross terms cancelling.

The local Klein--Gordon consequence assumes the Dirac equation throughout
a neighborhood of the point, expressed as eventual equality of the actual
residual to zero or as the shared equation on actual coordinate derivatives.
No supplied Hessian, d'Alembertian equation, or final factorization identity
is a premise. No converse, boundary-value theorem or variational derivation
is asserted.
-/

@[expose] public section
noncomputable section
open scoped Matrix.Norms.Operator
set_option backward.isDefEq.respectTransparency false
open Filter Topology
namespace FoliationQM.DiracOperatorFactorization
open DiracMatrices DiracEquation DiracFieldDensity RealLorentzFrame

/-- Fixed matrix action as an actual real continuous-linear map on spinors. -/
def matrixActionCLM (A : Mat) : Spinor →L[ℝ] Spinor :=
  (A.mulVecLin.restrictScalars ℝ).toContinuousLinearMap

/-- The continuous-linear map is actual matrix-vector multiplication. -/
@[simp]
theorem matrixActionCLM_apply (A : Mat) (psi : Spinor) :
    matrixActionCLM A psi = A.mulVec psi := rfl

variable {psi : Covector → Spinor} {x : Covector}

/-- A fixed matrix preserves actual differentiability of the spinor field. -/
theorem differentiableAt_matrixAction (hpsi : DifferentiableAt ℝ psi x) (A : Mat) :
    DifferentiableAt ℝ (fun y => A.mulVec (psi y)) x := by
  exact (matrixActionCLM A).differentiableAt.comp x hpsi

/-- Actual Frechet differentiation commutes with the fixed matrix action. -/
theorem fderiv_matrixAction_apply (hpsi : DifferentiableAt ℝ psi x) (A : Mat) (v : Covector) :
    fderiv ℝ (fun y => A.mulVec (psi y)) x v = A.mulVec (fderiv ℝ psi x v) := by
  have hd := congrArg (fun T : Covector →L[ℝ] Spinor => T v)
    ((matrixActionCLM A).hasFDerivAt.comp x hpsi.hasFDerivAt).fderiv
  simpa only [Function.comp_def, ContinuousLinearMap.comp_apply, matrixActionCLM_apply] using! hd

/-- Local C2 regularity makes the genuine spinor derivative field differentiable. -/
theorem differentiableAt_fderiv (hpsi : ContDiffAt ℝ 2 psi x) :
    DifferentiableAt ℝ (fderiv ℝ psi) x :=
  (hpsi.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)

/-- The genuine first derivative evaluated in a fixed direction is differentiable at a locally C2 point. -/
theorem differentiableAt_directional (hpsi : ContDiffAt ℝ 2 psi x) (w : Covector) :
    DifferentiableAt ℝ (fun y => fderiv ℝ psi y w) x :=
  (differentiableAt_fderiv hpsi).clm_apply (differentiableAt_const w)

/-- Differentiating the genuine directional derivative gives the actual second Frechet derivative in the stated order. -/
theorem fderiv_directional_apply (hpsi : ContDiffAt ℝ 2 psi x) (v w : Covector) :
    fderiv ℝ (fun y => fderiv ℝ psi y w) x v = fderiv ℝ (fderiv ℝ psi) x v w := by
  have hd := congrArg (fun T : Covector →L[ℝ] Spinor => T v)
    ((differentiableAt_fderiv hpsi).hasFDerivAt.clm_apply (hasFDerivAt_const w x)).fderiv
  change fderiv ℝ (fun y => fderiv ℝ psi y w) x v =
    fderiv ℝ psi x 0 + fderiv ℝ (fderiv ℝ psi) x v w at hd
  simpa only [map_zero, zero_add] using hd

/-- Local C2 regularity derives symmetry of the actual spinor second derivative. -/
theorem second_fderiv_symmetric (hpsi : ContDiffAt ℝ 2 psi x) (v w : Covector) :
    fderiv ℝ (fderiv ℝ psi) x v w = fderiv ℝ (fderiv ℝ psi) x w v := by
  simpa using! hpsi.isSymmSndFDerivAt (by norm_num) v w

/-- The actual slashed first derivative is differentiable under local C2 regularity. -/
theorem differentiableAt_slashField (hpsi : ContDiffAt ℝ 2 psi x) :
    DifferentiableAt ℝ (slashField psi) x := by
  simpa only [slashField, slashJet] using! (DifferentiableAt.fun_sum (u := Finset.univ)
    (fun mu _ => differentiableAt_matrixAction
      (differentiableAt_directional hpsi (coordinateDirections mu)) (gamma mu)))

/-- The actual derivative of the slashed field is the gamma contraction of the genuine second derivative. -/
theorem fderiv_slashField_apply (hpsi : ContDiffAt ℝ 2 psi x) (v : Covector) :
    fderiv ℝ (slashField psi) x v = ∑ mu,
      (gamma mu).mulVec (fderiv ℝ (fderiv ℝ psi) x v (coordinateDirections mu)) := by
  unfold slashField slashJet
  rw [fderiv_fun_sum (fun mu _ =>
    differentiableAt_matrixAction (differentiableAt_directional hpsi (coordinateDirections mu)) (gamma mu))]
  simp only [sum_apply]
  apply Finset.sum_congr rfl
  intro mu _
  rw [fderiv_matrixAction_apply (differentiableAt_directional hpsi (coordinateDirections mu)),
    fderiv_directional_apply hpsi]

/-- The square of the actual slashed first-order differential operator is the actual flat d'Alembertian at every locally C2 point. -/
theorem slashField_squared (hpsi : ContDiffAt ℝ 2 psi x) :
    slashField (slashField psi) x = boxField psi x := by
  change (∑ a, (gamma a).mulVec (fderiv ℝ (slashField psi) x (coordinateDirections a))) = _
  simp_rw [fderiv_slashField_apply hpsi]
  simp only [Matrix.mulVec_sum]
  rw [DiracSecondJet.symmetric_iterated_contraction
    (fun a b => fderiv ℝ (fderiv ℝ psi) x (coordinateDirections a) (coordinateDirections b))
    (fun a b => second_fderiv_symmetric hpsi _ _)]
  simp only [boxField, fderiv_directional_apply hpsi]

/-- The actual slashed field operator distributes over complex constant linear combinations of differentiable fields. -/
theorem slashField_linear_combination {phi : Covector → Spinor}
    (hpsi : DifferentiableAt ℝ psi x) (hphi : DifferentiableAt ℝ phi x) (a b : ℂ) :
    slashField (fun y => a • psi y - b • phi y) x =
      a • slashField psi x - b • slashField phi x := by
  have hd := ((hpsi.hasFDerivAt.const_smul a).sub (hphi.hasFDerivAt.const_smul b)).fderiv
  change fderiv ℝ (fun y => a • psi y - b • phi y) x = _ at hd
  simp only [slashField, slashJet, hd, sub_apply,
    _root_.smul_apply, Matrix.mulVec_sub, Matrix.mulVec_smul,
    Finset.sum_sub_distrib, ← Finset.smul_sum]

/-- The actual opposite Dirac factor times the Dirac operator equals hbar squared times the actual d'Alembertian plus the mass square. -/
theorem dirac_factorization (hpsi : ContDiffAt ℝ 2 psi x) (hbar m c : ℝ) :
    oppositeDiracField hbar m c (diracField hbar m c psi) x =
      ((hbar : ℂ)^2) • boxField psi x + ((m : ℂ)^2*(c : ℂ)^2) • psi x := by
  have hdiff := hpsi.differentiableAt (by norm_num)
  change (-Complex.I*(hbar : ℂ)) •
      slashField (fun y => (Complex.I*(hbar : ℂ)) • slashField psi y - ((m*c : ℝ) : ℂ) • psi y) x -
      ((m*c : ℝ) : ℂ) • ((Complex.I*(hbar : ℂ)) • slashField psi x - ((m*c : ℝ) : ℂ) • psi x) = _
  rw [slashField_linear_combination (differentiableAt_slashField hpsi) hdiff,
    slashField_squared hpsi]
  ext i
  simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Complex.ofReal_mul]
  ring_nf
  simp only [Complex.I_sq]
  ring

/-- A genuine local Dirac equation implies the Klein--Gordon equation at a locally C2 point, by differentiating the eventual zero residual. -/
theorem kleinGordon_of_eventually_dirac (hpsi : ContDiffAt ℝ 2 psi x) (hbar m c : ℝ)
    (hD : ∀ᶠ y in 𝓝 x, diracField hbar m c psi y = 0) :
    ((hbar : ℂ)^2) • boxField psi x + ((m : ℂ)^2*(c : ℂ)^2) • psi x = 0 := by
  have heq : diracField hbar m c psi =ᶠ[𝓝 x] (fun _ => (0 : Spinor)) := hD
  have hd : fderiv ℝ (diracField hbar m c psi) x = 0 := by
    rw [heq.fderiv_eq]
    exact (hasFDerivAt_const (0 : Spinor) x).fderiv
  have hz : oppositeDiracField hbar m c (diracField hbar m c psi) x = 0 := by
    simp only [oppositeDiracField, slashField, slashJet, hd, hD.self_of_nhds,
      zero_apply, Matrix.mulVec_zero, Finset.sum_const_zero,
      smul_zero, sub_zero]
  rw [dirac_factorization hpsi] at hz
  exact hz

/-- The shared Dirac equation on the genuine derivative jet throughout a neighborhood implies the actual Klein--Gordon equation at a locally C2 point. -/
theorem kleinGordon_of_eventually_jetEquation (hpsi : ContDiffAt ℝ 2 psi x) (hbar m c : ℝ)
    (hD : ∀ᶠ y in 𝓝 x, jetEquation hbar m c (psi y)
      (fun mu => fderiv ℝ psi y (coordinateDirections mu))) :
    ((hbar : ℂ)^2) • boxField psi x + ((m : ℂ)^2*(c : ℂ)^2) • psi x = 0 := by
  apply kleinGordon_of_eventually_dirac hpsi hbar m c
  exact hD.mono (fun y hy => (diracField_eq_zero_iff hbar m c psi y).mpr hy)

end FoliationQM.DiracOperatorFactorization
