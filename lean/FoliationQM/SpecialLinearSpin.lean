module
public import FoliationQM.SpinorMatrix
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# A concrete determinant-one matrix representation on Dirac spinors

Source: the matrix realization used in v13 `prop:takabayasi` and
`eq:takabayasi_polar`. For an actual complex two-by-two matrix A, the second
Weyl block is the actual adjugate conjugate transpose. The displayed
four-by-four Dirac matrix has half-blocks A+B and A-B. Its actual action
intertwines the existing spinor matrix encoding with left multiplication
by A. Multiplication, the identity and faithfulness are proved on all
matrix inputs by exact matrix algebra.

For determinant-one inputs the actual Dirac adjoint is a two-sided inverse,
and the representative commutes with the actual gamma5. This is a concrete
faithful determinant-one representation with proved matrix operations.
It does not identify its image with an abstract Clifford spin group, prove
a Lorentz covering classification, choose a global polar phase, or assert
a quotient reconstruction theorem.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.SpecialLinearSpin
open DiracMatrices DiracAdjoint SpinorMatrix

/-- The explicit second Weyl block is the conjugate transpose of the two-by-two adjugate. -/
def weylDual (A : Mat2) : Mat2 :=
  !![star (A 1 1), -star (A 1 0); -star (A 0 1), star (A 0 0)]

/-- The explicit four-by-four Dirac matrix of the two Weyl actions A and its adjugate conjugate transpose. -/
def spin (A : Mat2) : Mat :=
  (1/2 : ℂ) •
    !![A 0 0 + weylDual A 0 0, A 0 1 + weylDual A 0 1,
         A 0 0 - weylDual A 0 0, A 0 1 - weylDual A 0 1;
       A 1 0 + weylDual A 1 0, A 1 1 + weylDual A 1 1,
         A 1 0 - weylDual A 1 0, A 1 1 - weylDual A 1 1;
       A 0 0 - weylDual A 0 0, A 0 1 - weylDual A 0 1,
         A 0 0 + weylDual A 0 0, A 0 1 + weylDual A 0 1;
       A 1 0 - weylDual A 1 0, A 1 1 - weylDual A 1 1,
         A 1 0 + weylDual A 1 0, A 1 1 + weylDual A 1 1]

/-- The displayed second Weyl block is the actual adjugate conjugate transpose. -/
theorem weylDual_eq_adjugate_conjTranspose (A : Mat2) :
    weylDual A = A.adjugate.conjTranspose := by
  rw [Matrix.adjugate_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [weylDual, Matrix.conjTranspose_apply]

/-- The actual Dirac matrix at the two-dimensional identity is the four-dimensional identity. -/
theorem spin_one : spin (1 : Mat2) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [spin, weylDual, Matrix.one_apply]

/-- Every explicit Dirac representative commutes with the actual gamma5 matrix. -/
theorem spin_gamma5_commute (A : Mat2) : Commute (spin A) gamma5 := by
  change spin A*gamma5 = gamma5*spin A
  rw [gamma5_explicit]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [spin, Matrix.mul_apply, Fin.sum_univ_succ]

/-- The explicit Dirac representative respects actual two-by-two matrix multiplication. -/
theorem spin_mul (A B : Mat2) : spin (A*B) = spin A*spin B := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [spin, weylDual, Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

/-- The actual Dirac adjoint of the representative is the representative of the actual two-by-two adjugate. -/
theorem spin_diracAdjoint (A : Mat2) :
    diracAdjoint (spin A) = spin (A.adjugate) := by
  rw [Matrix.adjugate_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [spin, weylDual, diracAdjoint, gamma, Matrix.conjTranspose_apply,
      Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_succ, map_ofNat] <;> ring

/-- Every determinant-one two-by-two input gives an actual Dirac isometry. -/
theorem spin_dirac_isometry (A : Mat2) (hdet : A.det = 1) :
    diracAdjoint (spin A) * spin A = 1 := by
  rw [spin_diracAdjoint, ← spin_mul, Matrix.adjugate_mul, hdet, one_smul, spin_one]

/-- The actual four-by-four inverse of a determinant-one representative is its Dirac adjoint. -/
theorem spin_inverse (A : Mat2) (hdet : A.det = 1) :
    (spin A)⁻¹ = diracAdjoint (spin A) := Matrix.inv_eq_left_inv (spin_dirac_isometry A hdet)

/-- A determinant-one two-by-two input gives an actual invertible four-by-four Dirac matrix. -/
theorem spin_isUnit (A : Mat2) (hdet : A.det = 1) : IsUnit (spin A) := by
  have hl := spin_dirac_isometry A hdet
  have hr := mul_eq_one_comm.mp hl
  exact ⟨⟨spin A, diracAdjoint (spin A), hr, hl⟩, rfl⟩

/-- Actual matrix action on the spinor corresponds exactly to left multiplication in the concrete two-by-two encoding. -/
theorem spin_action (A : Mat2) (psi : Spinor) :
    toMatrix ((spin A).mulVec psi) = A * toMatrix psi := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [toMatrix, spin, weylDual, Matrix.mulVec, dotProduct,
      Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

/-- Acting on the actual rest spinor encodes the input two-by-two matrix itself. -/
theorem spin_rest_matrix (A : Mat2) : toMatrix ((spin A).mulVec restSpinor) = A := by
  rw [spin_action, toMatrix_restSpinor, mul_one]

/-- The concrete Dirac representation is faithful on actual two-by-two matrices. -/
theorem spin_injective : Function.Injective spin := by
  intro A B h
  have hh := congrArg (fun M : Mat => toMatrix (M.mulVec restSpinor)) h
  simpa only [spin_rest_matrix] using hh

end FoliationQM.SpecialLinearSpin
