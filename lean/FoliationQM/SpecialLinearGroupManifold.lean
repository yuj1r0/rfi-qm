module
public import FoliationQM.SpecialLinearManifold
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.Geometry.Manifold.Algebra.LieGroup
public import Mathlib.Geometry.Manifold.Diffeomorph
/-!
# The actual special linear matrix Lie group

Sources: the concrete determinant-one matrix factor in v13
`prop:takabayasi` and `eq:takabayasi_polar`, and its actual matrix
multiplication and inverse used in local polar-frame changes.
The existing `SpecialLinearMatrix` subtype is definitionally Mathlib's
special linear matrix group. Its genuine group structure is inherited,
so multiplication is matrix multiplication and inversion is the actual
adjugate, equal to matrix inversion because the determinant is one.

The natural subtype topology and the existing intrinsic six-dimensional
rational atlas are retained. Joint multiplication is proved smooth via
actual ambient matrix multiplication and the established intrinsic
coordinate criterion. Inversion is proved smooth through the actual
two-by-two adjugate continuous linear map. These results give a genuine
real Lie-group instance to every order, together with actual left and
right translations and inversion as diffeomorphisms. No abstract Spin
identification or additional group-law premise is used.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Matrix.Norms.Operator Manifold
namespace FoliationQM.SpecialLinearGroupManifold
open SpinorMatrix SourcePolarDatum SpecialLinearCharts

/-- The determinant-one subtype inherits the actual special linear matrix group. -/
instance instGroupSpecialLinearMatrix : Group SpecialLinearMatrix :=
  inferInstanceAs (Group (Matrix.SpecialLinearGroup (Fin 2) ℂ))

/-- The identity is the actual identity matrix. -/
@[simp]
theorem coe_one : ((1 : SpecialLinearMatrix) : Mat2) = 1 := rfl

/-- Multiplication is actual matrix multiplication. -/
@[simp]
theorem coe_mul (A B : SpecialLinearMatrix) : ((A * B : SpecialLinearMatrix) : Mat2) =
    (A : Mat2) * (B : Mat2) := rfl

/-- The group inverse is the actual adjugate. -/
theorem coe_inv_adjugate (A : SpecialLinearMatrix) : ((A⁻¹ : SpecialLinearMatrix) : Mat2) =
    Matrix.adjugate (A : Mat2) := rfl

/-- The group inverse agrees with the actual matrix inverse. -/
@[simp]
theorem coe_inv (A : SpecialLinearMatrix) : ((A⁻¹ : SpecialLinearMatrix) : Mat2) =
    (A : Mat2)⁻¹ := by
  rw [coe_inv_adjugate, Matrix.inv_def, A.property]
  simp

/-- Actual joint matrix multiplication is smooth in the intrinsic manifold. -/
theorem contMDiff_mul (n : WithTop ℕ∞) :
    ContMDiff ((𝓘(ℝ, Model)).prod 𝓘(ℝ, Model)) 𝓘(ℝ, Model) n
      (fun p : SpecialLinearMatrix × SpecialLinearMatrix => p.1 * p.2) := by
  apply SpecialLinearManifold.contMDiff_iff_value.mpr
  have hm : ContDiff ℝ n (fun p : Mat2 × Mat2 => p.1 * p.2) :=
    contDiff_fst.mul contDiff_snd
  exact hm.contMDiff.comp
    (((SpecialLinearManifold.contMDiff_value n).comp contMDiff_fst).prodMk_space
      ((SpecialLinearManifold.contMDiff_value n).comp contMDiff_snd))

/-- The actual two-dimensional adjugate is a real continuous linear map. -/
def adjugateCLM : Mat2 →L[ℝ] Mat2 :=
  LinearMap.toContinuousLinearMap {
    toFun := Matrix.adjugate
    map_add' := by
      intro A B
      simp only [Matrix.adjugate_fin_two]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [add_comm]
    map_smul' := by
      intro r A
      simp only [Matrix.adjugate_fin_two]
      ext i j
      fin_cases i <;> fin_cases j <;> simp }

/-- The continuous linear adjugate map is the actual matrix adjugate. -/
@[simp]
theorem adjugateCLM_apply (A : Mat2) : adjugateCLM A = Matrix.adjugate A := rfl

/-- Actual group inversion is smooth in the intrinsic manifold. -/
theorem contMDiff_inv (n : WithTop ℕ∞) :
    ContMDiff 𝓘(ℝ, Model) 𝓘(ℝ, Model) n
      (fun A : SpecialLinearMatrix => A⁻¹) := by
  apply SpecialLinearManifold.contMDiff_iff_value.mpr
  exact adjugateCLM.contMDiff.comp (SpecialLinearManifold.contMDiff_value n)

/-- The intrinsic six-dimensional real manifold is an actual Lie group to every order. -/
instance instLieGroupSpecialLinearMatrix (n : WithTop ℕ∞) :
    LieGroup 𝓘(ℝ, Model) n SpecialLinearMatrix where
  contMDiff_mul := contMDiff_mul n
  contMDiff_inv := contMDiff_inv n

/-- Actual left multiplication by a fixed determinant-one matrix is smooth. -/
theorem contMDiff_leftMul (n : WithTop ℕ∞) (A : SpecialLinearMatrix) :
    ContMDiff 𝓘(ℝ, Model) 𝓘(ℝ, Model) n (fun B : SpecialLinearMatrix => A * B) :=
  (contMDiff_mul n).comp (contMDiff_const.prodMk contMDiff_id)

/-- Actual right multiplication by a fixed determinant-one matrix is smooth. -/
theorem contMDiff_rightMul (n : WithTop ℕ∞) (A : SpecialLinearMatrix) :
    ContMDiff 𝓘(ℝ, Model) 𝓘(ℝ, Model) n (fun B : SpecialLinearMatrix => B * A) :=
  (contMDiff_mul n).comp (contMDiff_id.prodMk contMDiff_const)

/-- Left translation is a genuine diffeomorphism, with inverse left translation by the actual matrix inverse. -/
def leftMulDiffeomorph (n : WithTop ℕ∞) (A : SpecialLinearMatrix) :
    Diffeomorph 𝓘(ℝ, Model) 𝓘(ℝ, Model) SpecialLinearMatrix SpecialLinearMatrix n where
  toFun := fun B => A * B
  invFun := fun B => A⁻¹ * B
  left_inv := fun B => by simp [← mul_assoc]
  right_inv := fun B => by simp [← mul_assoc]
  contMDiff_toFun := contMDiff_leftMul n A
  contMDiff_invFun := contMDiff_leftMul n A⁻¹

/-- Right translation is a genuine diffeomorphism, with inverse right translation by the actual matrix inverse. -/
def rightMulDiffeomorph (n : WithTop ℕ∞) (A : SpecialLinearMatrix) :
    Diffeomorph 𝓘(ℝ, Model) 𝓘(ℝ, Model) SpecialLinearMatrix SpecialLinearMatrix n where
  toFun := fun B => B * A
  invFun := fun B => B * A⁻¹
  left_inv := fun B => by simp [mul_assoc]
  right_inv := fun B => by simp [mul_assoc]
  contMDiff_toFun := contMDiff_rightMul n A
  contMDiff_invFun := contMDiff_rightMul n A⁻¹

/-- Actual group inversion is an involutive diffeomorphism. -/
def inverseDiffeomorph (n : WithTop ℕ∞) :
    Diffeomorph 𝓘(ℝ, Model) 𝓘(ℝ, Model) SpecialLinearMatrix SpecialLinearMatrix n where
  toFun := fun A => A⁻¹
  invFun := fun A => A⁻¹
  left_inv := inv_inv
  right_inv := inv_inv
  contMDiff_toFun := contMDiff_inv n
  contMDiff_invFun := contMDiff_inv n

/-- The left-translation diffeomorphism is literally multiplication in the actual matrix group. -/
@[simp]
theorem leftMulDiffeomorph_apply (n : WithTop ℕ∞) (A B : SpecialLinearMatrix) :
    leftMulDiffeomorph n A B = A * B := rfl

/-- The inverse left-translation diffeomorphism is literally multiplication by the actual group inverse. -/
@[simp]
theorem leftMulDiffeomorph_symm_apply (n : WithTop ℕ∞) (A B : SpecialLinearMatrix) :
    (leftMulDiffeomorph n A).symm B = A⁻¹ * B := rfl

/-- The right-translation diffeomorphism is literally right multiplication in the actual matrix group. -/
@[simp]
theorem rightMulDiffeomorph_apply (n : WithTop ℕ∞) (A B : SpecialLinearMatrix) :
    rightMulDiffeomorph n A B = B * A := rfl

/-- The inverse right-translation diffeomorphism is literally right multiplication by the actual group inverse. -/
@[simp]
theorem rightMulDiffeomorph_symm_apply (n : WithTop ℕ∞) (A B : SpecialLinearMatrix) :
    (rightMulDiffeomorph n A).symm B = B * A⁻¹ := rfl

/-- The inversion diffeomorphism is literally the actual group inverse. -/
@[simp]
theorem inverseDiffeomorph_apply (n : WithTop ℕ∞) (A : SpecialLinearMatrix) :
    inverseDiffeomorph n A = A⁻¹ := rfl

end FoliationQM.SpecialLinearGroupManifold
