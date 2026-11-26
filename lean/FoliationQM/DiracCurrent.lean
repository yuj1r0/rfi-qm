module
public import FoliationQM.DiracEquation
public import Mathlib.Analysis.Calculus.FDeriv.Bilinear

/-!
# Actual bilinear differentiation and conditional Dirac current conservation

Sources: v13 `eq:dirac`, the conserved-current statement preceding
`eq:gordon_decomp`, and the spinor-adjoint derivative conventions. The
Dirac equation is the shared explicit physical input. Its adjoint equation
is derived by taking the actual conjugate spinor row, and the actual field
version uses the genuine derivative of that row.

The constant-matrix bilinear is a real continuous bilinear map, whose
Frechet product derivative is proved for arbitrary real normed domains.
The current is the actual c-scaled gamma bilinear; its real part reconstructs
it faithfully. The two differentiated terms cancel under the Dirac equation
and nonzero hbar. The flat-coordinate corollaries use the established actual
coordinate directions. No variational derivation of the Dirac equation,
polar reconstruction, or boundary/integral conservation law is asserted.
-/

@[expose] public section
noncomputable section
open scoped Matrix.Norms.Operator
namespace FoliationQM.DiracCurrent
open DiracMatrices DiracAdjoint MatrixDifferential DiracDensity Matrix DiracEquation

private theorem bilinear_add_left (p q r : Spinor) (A : Mat) :
    bilinear (p+q) A r = bilinear p A r + bilinear q A r := by
  simp [bilinear, add_dotProduct]

private theorem bilinear_add_right (p q r : Spinor) (A : Mat) :
    bilinear p A (q+r) = bilinear p A q + bilinear p A r := by
  simp [bilinear, Matrix.mulVec_add, dotProduct_add]

private theorem bilinear_real_smul_left (a : ℝ) (p q : Spinor) (A : Mat) :
    bilinear (a • p) A q = a • bilinear p A q := by
  rw [← IsScalarTower.algebraMap_smul ℂ a p, bilinear_smul_left]
  simp

private theorem bilinear_real_smul_right (a : ℝ) (p q : Spinor) (A : Mat) :
    bilinear p A (a • q) = a • bilinear p A q := by
  rw [← IsScalarTower.algebraMap_smul ℂ a q, bilinear_smul_right]
  rfl

private def bilinearRight (A : Mat) (p : Spinor) : Spinor →L[ℝ] ℂ :=
  ({ toFun := bilinear p A
     map_add' := fun q r => bilinear_add_right p q r A
     map_smul' := fun a q => bilinear_real_smul_right a p q A } :
    Spinor →ₗ[ℝ] ℂ).toContinuousLinearMap

private def bilinearCLM (A : Mat) : Spinor →L[ℝ] Spinor →L[ℝ] ℂ :=
  ({ toFun := bilinearRight A
     map_add' := by
       intro p q
       ext r
       exact bilinear_add_left p q r A
     map_smul' := by
       intro a p
       ext q
       exact bilinear_real_smul_left a p q A } :
    Spinor →ₗ[ℝ] Spinor →L[ℝ] ℂ).toContinuousLinearMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A constant-matrix bilinear of two differentiable spinor fields is genuinely real-Frechet differentiable. -/
theorem differentiableAt_bilinear {psi chi : E → Spinor} {x : E}
    (hpsi : DifferentiableAt ℝ psi x) (hchi : DifferentiableAt ℝ chi x) (A : Mat) :
    DifferentiableAt ℝ (fun y => bilinear (psi y) A (chi y)) x :=
  ((bilinearCLM A).hasFDerivAt_of_bilinear hpsi.hasFDerivAt hchi.hasFDerivAt).differentiableAt

/-- The genuine constant-matrix bilinear derivative is the sum of its actual left and right spinor derivatives. -/
theorem fderiv_bilinear_apply {psi chi : E → Spinor} {x : E}
    (hpsi : DifferentiableAt ℝ psi x) (hchi : DifferentiableAt ℝ chi x) (A : Mat) (v : E) :
    fderiv ℝ (fun y => bilinear (psi y) A (chi y)) x v =
      bilinear (fderiv ℝ psi x v) A (chi x) + bilinear (psi x) A (fderiv ℝ chi x v) := by
  have hd := congrArg (fun T : E →L[ℝ] ℂ => T v)
    ((bilinearCLM A).hasFDerivAt_of_bilinear hpsi.hasFDerivAt hchi.hasFDerivAt).fderiv
  change fderiv ℝ (fun y => bilinear (psi y) A (chi y)) x v =
    bilinear (psi x) A (fderiv ℝ chi x v) + bilinear (fderiv ℝ psi x v) A (chi x) at hd
  exact hd.trans (add_comm _ _)

/-- The genuine bilinear product derivative is the source row formula using the actual derivative of the spinor-adjoint row. -/
theorem fderiv_bilinear_row_apply {psi chi : E → Spinor} {x : E}
    (hpsi : DifferentiableAt ℝ psi x) (hchi : DifferentiableAt ℝ chi x) (A : Mat) (v : E) :
    fderiv ℝ (fun y => bilinear (psi y) A (chi y)) x v =
      dotProduct (fderiv ℝ (fun y => spinorAdjoint (psi y)) x v) (A.mulVec (chi x)) +
        dotProduct (spinorAdjoint (psi x)) (A.mulVec (fderiv ℝ chi x v)) := by
  rw [fderiv_bilinear_apply hpsi hchi, fderiv_spinorAdjoint_apply hpsi]
  simp only [bilinear_eq_row]

private theorem spinorAdjoint_smul (z : ℂ) (psi : Spinor) :
    spinorAdjoint (z • psi) = star z • spinorAdjoint psi := by
  simp [spinorAdjoint, Matrix.smul_vecMul]

private theorem spinorAdjoint_sum (v : Fin 4 → Spinor) :
    spinorAdjoint (∑ mu, v mu) = ∑ mu, spinorAdjoint (v mu) := by
  change spinorAdjointCLM (∑ mu, v mu) = ∑ mu, spinorAdjointCLM (v mu)
  exact map_sum spinorAdjointCLM v Finset.univ

/-- Taking the actual spinor-adjoint row of the shared Dirac jet equation derives its negative-i adjoint equation without a second field-equation premise. -/
theorem adjoint_jetEquation (hbar m c : ℝ) (psi : Spinor) (jet : Fin 4 → Spinor)
    (hDirac : jetEquation hbar m c psi jet) :
    (-Complex.I*(hbar : ℂ)) • (∑ mu, Matrix.vecMul (spinorAdjoint (jet mu)) (gamma mu)) =
      ((m*c : ℝ) : ℂ) • spinorAdjoint psi := by
  have h := congrArg spinorAdjoint hDirac
  simpa only [slashJet, spinorAdjoint_smul, spinorAdjoint_sum,
    spinorAdjoint_mulVec, diracAdjoint_gamma, star_mul, Complex.star_def,
    Complex.conj_ofReal, Complex.conj_I, mul_comm] using h

private theorem bilinear_sum_right (psi : Spinor) (A : Mat) (v : Fin 4 → Spinor) :
    bilinear psi A (∑ mu, v mu) = ∑ mu, bilinear psi A (v mu) := by
  simp [bilinear, Matrix.mulVec_sum, dotProduct_sum]

/-- The actual Dirac jet equation gives the right gamma-contracted scalar equation at the same spinor. -/
theorem jetEquation_right_bilinear (hbar m c : ℝ) (psi : Spinor) (jet : Fin 4 → Spinor)
    (hDirac : jetEquation hbar m c psi jet) :
    (Complex.I*(hbar : ℂ)) * (∑ mu, bilinear psi (gamma mu) (jet mu)) =
      ((m*c : ℝ) : ℂ) * bilinear psi 1 psi := by
  have h := congrArg (bilinear psi 1) hDirac
  simpa only [bilinear_smul_right, slashJet, bilinear_sum_right,
    ← bilinear_mul_matrix, one_mul] using h

/-- Complex conjugation of the right scalar Dirac equation derives the left negative-i gamma contraction. -/
theorem jetEquation_left_bilinear (hbar m c : ℝ) (psi : Spinor) (jet : Fin 4 → Spinor)
    (hDirac : jetEquation hbar m c psi jet) :
    (-Complex.I*(hbar : ℂ)) * (∑ mu, bilinear (jet mu) (gamma mu) psi) =
      ((m*c : ℝ) : ℂ) * bilinear psi 1 psi := by
  have h := congrArg star (jetEquation_right_bilinear hbar m c psi jet hDirac)
  simpa only [star_mul, star_sum, star_bilinear, diracAdjoint_gamma, diracAdjoint_one,
    Complex.star_def, Complex.conj_ofReal, Complex.conj_I, mul_comm] using h

/-- The sum of actual left and right vector-bilinear jet terms vanishes under the shared Dirac equation and nonzero hbar. -/
theorem jet_vector_conservation (hbar m c : ℝ) (hhbar : hbar ≠ 0)
    (psi : Spinor) (jet : Fin 4 → Spinor) (hDirac : jetEquation hbar m c psi jet) :
    (∑ mu, (bilinear (jet mu) (gamma mu) psi + bilinear psi (gamma mu) (jet mu))) = 0 := by
  have hr := jetEquation_right_bilinear hbar m c psi jet hDirac
  have hl := jetEquation_left_bilinear hbar m c psi jet hDirac
  have hz : (Complex.I*(hbar : ℂ)) *
      (∑ mu, (bilinear (jet mu) (gamma mu) psi + bilinear psi (gamma mu) (jet mu))) = 0 := by
    rw [Finset.sum_add_distrib]
    linear_combination hr - hl
  exact (mul_eq_zero.mp hz).resolve_left (mul_ne_zero Complex.I_ne_zero (by exact_mod_cast hhbar))

/-- The actual adjoint-row field equation follows from the Dirac equation and genuine differentiation of the spinor-adjoint field. -/
theorem adjoint_fieldEquation {psi : E → Spinor} {x : E}
    (hpsi : DifferentiableAt ℝ psi x) (directions : Fin 4 → E) (hbar m c : ℝ)
    (hDirac : jetEquation hbar m c (psi x) (fun mu => fderiv ℝ psi x (directions mu))) :
    (-Complex.I*(hbar : ℂ)) •
      (∑ mu, Matrix.vecMul (fderiv ℝ (fun y => spinorAdjoint (psi y)) x (directions mu)) (gamma mu)) =
      ((m*c : ℝ) : ℂ) • spinorAdjoint (psi x) := by
  simp only [fderiv_spinorAdjoint_apply hpsi]
  exact adjoint_jetEquation hbar m c (psi x) _ hDirac

/-- The actual physical vector current component is c times the Dirac vector bilinear. -/
def current (c : ℝ) (psi : Spinor) (mu : Fin 4) : ℂ :=
  (c : ℂ) * bilinear psi (gamma mu) psi

/-- The faithful real component of the actual physical vector current. -/
def currentRe (c : ℝ) (psi : Spinor) (mu : Fin 4) : ℝ := (current c psi mu).re

/-- Every actual physical current component has zero imaginary part. -/
theorem current_im_eq_zero (c : ℝ) (psi : Spinor) (mu : Fin 4) :
    (current c psi mu).im = 0 := by
  simp only [current, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    vector_bilinear_real, mul_zero, zero_mul, add_zero]

/-- The actual complex current is faithfully reconstructed from its real current component. -/
theorem current_eq_ofReal (c : ℝ) (psi : Spinor) (mu : Fin 4) :
    current c psi mu = (currentRe c psi mu : ℂ) := by
  apply Complex.ext
  · rfl
  · simpa only [Complex.ofReal_im] using current_im_eq_zero c psi mu

/-- A differentiable spinor field gives a genuinely differentiable physical current component. -/
theorem differentiableAt_current {psi : E → Spinor} {x : E}
    (hpsi : DifferentiableAt ℝ psi x) (c : ℝ) (mu : Fin 4) :
    DifferentiableAt ℝ (fun y => current c (psi y) mu) x :=
  (differentiableAt_bilinear hpsi hpsi (gamma mu)).const_mul (c : ℂ)

/-- The genuine directional derivative of the physical current is c times the two actual vector-bilinear product terms. -/
theorem fderiv_current_apply {psi : E → Spinor} {x : E}
    (hpsi : DifferentiableAt ℝ psi x) (c : ℝ) (mu : Fin 4) (v : E) :
    fderiv ℝ (fun y => current c (psi y) mu) x v =
      (c : ℂ) * (bilinear (fderiv ℝ psi x v) (gamma mu) (psi x) +
        bilinear (psi x) (gamma mu) (fderiv ℝ psi x v)) := by
  have hd := congrArg (fun T : E →L[ℝ] ℂ => T v)
    (((differentiableAt_bilinear hpsi hpsi (gamma mu)).hasFDerivAt).const_mul (c : ℂ)).fderiv
  change fderiv ℝ (fun y => current c (psi y) mu) x v =
    (c : ℂ) * fderiv ℝ (fun y => bilinear (psi y) (gamma mu) (psi y)) x v at hd
  rw [fderiv_bilinear_apply hpsi hpsi] at hd
  exact hd

/-- The actual current derivative sum vanishes under the shared Dirac equation on those actual field directions and nonzero hbar. -/
theorem current_conservation {psi : E → Spinor} {x : E}
    (hpsi : DifferentiableAt ℝ psi x) (directions : Fin 4 → E) (hbar m c : ℝ)
    (hhbar : hbar ≠ 0)
    (hDirac : jetEquation hbar m c (psi x) (fun mu => fderiv ℝ psi x (directions mu))) :
    (∑ mu, fderiv ℝ (fun y => current c (psi y) mu) x (directions mu)) = 0 := by
  simp only [fderiv_current_apply hpsi]
  rw [← Finset.mul_sum, jet_vector_conservation hbar m c hhbar (psi x) _ hDirac, mul_zero]

/-- The real current derivative is the real part of the actual complex current derivative, by the genuine real-part chain rule. -/
theorem fderiv_currentRe_apply {psi : E → Spinor} {x : E}
    (hpsi : DifferentiableAt ℝ psi x) (c : ℝ) (mu : Fin 4) (v : E) :
    fderiv ℝ (fun y => currentRe c (psi y) mu) x v =
      (fderiv ℝ (fun y => current c (psi y) mu) x v).re := by
  have hd := congrArg (fun T : E →L[ℝ] ℝ => T v)
    (Complex.reCLM.hasFDerivAt.comp x (differentiableAt_current hpsi c mu).hasFDerivAt).fderiv
  exact hd

/-- The faithful real physical current has zero actual derivative sum under the shared Dirac jet equation. -/
theorem currentRe_conservation {psi : E → Spinor} {x : E}
    (hpsi : DifferentiableAt ℝ psi x) (directions : Fin 4 → E) (hbar m c : ℝ)
    (hhbar : hbar ≠ 0)
    (hDirac : jetEquation hbar m c (psi x) (fun mu => fderiv ℝ psi x (directions mu))) :
    (∑ mu, fderiv ℝ (fun y => currentRe c (psi y) mu) x (directions mu)) = 0 := by
  simp only [fderiv_currentRe_apply hpsi]
  have h := congrArg Complex.re (current_conservation hpsi directions hbar m c hhbar hDirac)
  simpa only [Complex.re_sum, Complex.zero_re] using h

/-- A genuine flat-coordinate Dirac solution has conserved complex current with the actual coordinate divergence. -/
theorem coordinate_current_conservation {psi : Covector → Spinor} {x : Covector}
    (hpsi : DifferentiableAt ℝ psi x) (hbar m c : ℝ) (hhbar : hbar ≠ 0)
    (hDirac : diracField hbar m c psi x = 0) :
    (∑ mu, fderiv ℝ (fun y => current c (psi y) mu) x (DiracFieldDensity.coordinateDirections mu)) = 0 :=
  current_conservation hpsi _ hbar m c hhbar ((diracField_eq_zero_iff hbar m c psi x).mp hDirac)

/-- A genuine flat-coordinate Dirac solution has conserved faithful real current with the actual coordinate divergence. -/
theorem coordinate_currentRe_conservation {psi : Covector → Spinor} {x : Covector}
    (hpsi : DifferentiableAt ℝ psi x) (hbar m c : ℝ) (hhbar : hbar ≠ 0)
    (hDirac : diracField hbar m c psi x = 0) :
    (∑ mu, fderiv ℝ (fun y => currentRe c (psi y) mu) x (DiracFieldDensity.coordinateDirections mu)) = 0 :=
  currentRe_conservation hpsi _ hbar m c hhbar ((diracField_eq_zero_iff hbar m c psi x).mp hDirac)

end FoliationQM.DiracCurrent
