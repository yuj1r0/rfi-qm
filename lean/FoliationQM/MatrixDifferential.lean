module
public import FoliationQM.DiracAdjoint
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Actual matrix and spinor-adjoint differential calculus

Source: the inverse differentiation and adjoint steps in v13
`lem:maurer_cartan`, `eq:d_psi_polar_main`, and `eq:d_psibar_polar_main`.
All derivatives are Mathlib real Frechet derivatives of actual matrix or
spinor functions. Matrix calculus uses `Matrix.Norms.Operator`, consistently
with the existing rotor and chiral modules. The domain may be any real normed
space; only the matrix and spinor target spaces use finite dimensionality to
turn the explicitly verified real-linear maps into continuous-linear maps.

The inverse derivative is obtained from Mathlib's normed-algebra inversion
theorem and the proved equality of actual matrix inversion with Ring.inverse.
Its hypothesis is invertibility at the point. No derivative conclusion or
connection formula is supplied as a premise.
-/

@[expose] public section

noncomputable section
open scoped Matrix.Norms.Operator
namespace FoliationQM.MatrixDifferential
open DiracMatrices DiracAdjoint

/-- The actual Dirac adjoint as a real continuous-linear map on matrices. -/
def diracAdjointCLM : Mat →L[ℝ] Mat :=
  ({ toFun := diracAdjoint
     map_add' := diracAdjoint_add
     map_smul' := by
       intro r A
       simp [diracAdjoint, Matrix.conjTranspose_smul] } :
    Mat →ₗ[ℝ] Mat).toContinuousLinearMap

/-- The real continuous-linear Dirac-adjoint map evaluates to the actual Dirac adjoint. -/
@[simp]
theorem diracAdjointCLM_apply (A : Mat) :
    diracAdjointCLM A = diracAdjoint A := rfl

/-- The actual Dirac-adjoint row of a four-component spinor, represented by its coordinates. -/
def spinorAdjoint (psi : Spinor) : Spinor := Matrix.vecMul (star psi) (gamma 0)

/-- The actual spinor-adjoint row as a real continuous-linear map. -/
def spinorAdjointCLM : Spinor →L[ℝ] Spinor :=
  ({ toFun := spinorAdjoint
     map_add' := by intro p q; simp [spinorAdjoint, Matrix.add_vecMul]
     map_smul' := by intro r p; simp [spinorAdjoint, Matrix.smul_vecMul] } :
    Spinor →ₗ[ℝ] Spinor).toContinuousLinearMap

/-- The real continuous-linear spinor-adjoint map evaluates to the actual row. -/
@[simp]
theorem spinorAdjointCLM_apply (psi : Spinor) :
    spinorAdjointCLM psi = spinorAdjoint psi := rfl

/-- Actual matrix action on a fixed spinor as a real continuous-linear map of the matrix. -/
def mulVecCLM (psi : Spinor) : Mat →L[ℝ] Spinor :=
  ({ toFun := fun A => A.mulVec psi
     map_add' := by intro A B; exact Matrix.add_mulVec A B psi
     map_smul' := by intro r A; simp [Matrix.smul_mulVec] } :
    Mat →ₗ[ℝ] Spinor).toContinuousLinearMap

/-- The fixed-spinor continuous-linear map evaluates to actual matrix-vector multiplication. -/
@[simp]
theorem mulVecCLM_apply (psi : Spinor) (A : Mat) :
    mulVecCLM psi A = A.mulVec psi := rfl

/-- Taking the actual spinor-adjoint row moves a matrix action to the right with its Dirac adjoint. -/
theorem spinorAdjoint_mulVec (A : Mat) (psi : Spinor) :
    spinorAdjoint (A.mulVec psi) = Matrix.vecMul (spinorAdjoint psi) (diracAdjoint A) := by
  unfold spinorAdjoint diracAdjoint
  rw [Matrix.star_mulVec]
  simp only [Matrix.vecMul_vecMul]
  congr 1
  simp only [← mul_assoc, gamma_zero_sq, one_mul]

/-- At an invertible matrix the actual inverse has the real Frechet derivative minus left and right multiplication by its inverse. -/
theorem hasFDerivAt_matrix_inv (A : Mat) (hA : IsUnit A) :
    HasFDerivAt (fun B : Mat => B⁻¹)
      (-ContinuousLinearMap.mulLeftRight ℝ Mat A⁻¹ A⁻¹) A := by
  rcases hA with ⟨u, rfl⟩
  simpa only [Matrix.nonsing_inv_eq_ringInverse, Ring.inverse_unit] using
    (hasFDerivAt_ringInverse (𝕜 := ℝ) u)

/-- The actual matrix Dirac-adjoint function has its real continuous-linear map as derivative. -/
theorem hasFDerivAt_diracAdjoint (A : Mat) :
    HasFDerivAt diracAdjoint diracAdjointCLM A := diracAdjointCLM.hasFDerivAt

/-- The actual spinor-adjoint function has its real continuous-linear map as derivative. -/
theorem hasFDerivAt_spinorAdjoint (psi : Spinor) :
    HasFDerivAt spinorAdjoint spinorAdjointCLM psi := spinorAdjointCLM.hasFDerivAt

/-- Actual matrix action on a fixed spinor has the fixed-spinor continuous-linear map as derivative. -/
theorem hasFDerivAt_mulVec_const (psi : Spinor) (A : Mat) :
    HasFDerivAt (fun B : Mat => B.mulVec psi) (mulVecCLM psi) A :=
  (mulVecCLM psi).hasFDerivAt

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The chain rule differentiates the actual inverse of a matrix field at an invertible value. -/
theorem hasFDerivAt_inv_field {L : E → Mat} {L' : E →L[ℝ] Mat} {x : E}
    (hL : HasFDerivAt L L' x) (hunit : IsUnit (L x)) :
    HasFDerivAt (fun y => (L y)⁻¹)
      ((-ContinuousLinearMap.mulLeftRight ℝ Mat (L x)⁻¹ (L x)⁻¹).comp L') x :=
  (hasFDerivAt_matrix_inv (L x) hunit).comp x hL

/-- The actual inverse-field derivative applied to a direction is minus inverse times derivative times inverse. -/
theorem fderiv_inv_apply {L : E → Mat} {x : E}
    (hL : DifferentiableAt ℝ L x) (hunit : IsUnit (L x)) (v : E) :
    fderiv ℝ (fun y => (L y)⁻¹) x v = -(L x)⁻¹ * (fderiv ℝ L x v) * (L x)⁻¹ := by
  have h := congrArg (fun T : E →L[ℝ] Mat => T v)
    (hasFDerivAt_inv_field hL.hasFDerivAt hunit).fderiv
  change fderiv ℝ (fun y => (L y)⁻¹) x v =
    -((L x)⁻¹ * (fderiv ℝ L x v) * (L x)⁻¹) at h
  simpa only [neg_mul] using h

/-- The chain rule differentiates the actual Dirac adjoint of a matrix field. -/
theorem hasFDerivAt_diracAdjoint_field {L : E → Mat} {L' : E →L[ℝ] Mat} {x : E}
    (hL : HasFDerivAt L L' x) :
    HasFDerivAt (fun y => diracAdjoint (L y)) (diracAdjointCLM.comp L') x :=
  (hasFDerivAt_diracAdjoint (L x)).comp x hL

/-- Applying the actual derivative of a matrix-adjoint field commutes with the actual Dirac adjoint. -/
theorem fderiv_diracAdjoint_apply {L : E → Mat} {x : E}
    (hL : DifferentiableAt ℝ L x) (v : E) :
    fderiv ℝ (fun y => diracAdjoint (L y)) x v = diracAdjoint (fderiv ℝ L x v) := by
  rw [(hasFDerivAt_diracAdjoint_field hL.hasFDerivAt).fderiv]
  rfl

/-- The chain rule differentiates the actual spinor-adjoint row of a spinor field. -/
theorem hasFDerivAt_spinorAdjoint_field {psi : E → Spinor} {psi' : E →L[ℝ] Spinor}
    {x : E} (hpsi : HasFDerivAt psi psi' x) :
    HasFDerivAt (fun y => spinorAdjoint (psi y)) (spinorAdjointCLM.comp psi') x :=
  (hasFDerivAt_spinorAdjoint (psi x)).comp x hpsi

/-- Applying the actual derivative of a spinor-adjoint field gives the adjoint row of the spinor derivative. -/
theorem fderiv_spinorAdjoint_apply {psi : E → Spinor} {x : E}
    (hpsi : DifferentiableAt ℝ psi x) (v : E) :
    fderiv ℝ (fun y => spinorAdjoint (psi y)) x v = spinorAdjoint (fderiv ℝ psi x v) := by
  rw [(hasFDerivAt_spinorAdjoint_field hpsi.hasFDerivAt).fderiv]
  rfl

/-- The chain rule differentiates a matrix field acting on a fixed spinor. -/
theorem hasFDerivAt_mulVec_const_field {L : E → Mat} {L' : E →L[ℝ] Mat}
    {x : E} (hL : HasFDerivAt L L' x) (psi : Spinor) :
    HasFDerivAt (fun y => (L y).mulVec psi) ((mulVecCLM psi).comp L') x :=
  (hasFDerivAt_mulVec_const psi (L x)).comp x hL

/-- The actual derivative of a matrix field acting on a fixed spinor is the derivative matrix acting on that spinor. -/
theorem fderiv_mulVec_const_apply {L : E → Mat} {x : E}
    (hL : DifferentiableAt ℝ L x) (psi : Spinor) (v : E) :
    fderiv ℝ (fun y => (L y).mulVec psi) x v = (fderiv ℝ L x v).mulVec psi := by
  rw [(hasFDerivAt_mulVec_const_field hL.hasFDerivAt psi).fderiv]
  rfl

end FoliationQM.MatrixDifferential
