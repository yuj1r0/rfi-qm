module

public import FoliationQM.DiracMatrices
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.Tactic.NoncommRing

/-!
# Actual Dirac adjoints and spinor bilinears

Sources: v13 `sec:spinor`, especially `prop:takabayasi` and its fixed rest
spinor conventions. The adjoint is the actual conjugate transpose conjugated
by gamma0 in the explicit (+---) Dirac representation. Bilinears use the
actual complex vector contraction, conjugate-linear in the first spinor and
linear in the matrix and second spinor.

The scalar, vector, axial and signed pseudoscalar reality statements hold for
arbitrary complex four-component spinors. The normalized reference spinor
has the source scalar, pseudoscalar, temporal-vector and axial-three values.
No polar-decomposition existence theorem, full spin-group classification or
spinor field equation is assumed or claimed.
-/

@[expose] public section

noncomputable section
namespace FoliationQM.DiracAdjoint
open DiracMatrices Matrix

/-- The actual Dirac adjoint of a complex matrix in signature (+---). -/
def diracAdjoint (A : Mat) : Mat := gamma 0*A.conjTranspose*gamma 0

/-- The actual spinor contraction psi dagger gamma0 A chi. -/
def bilinear (psi : Spinor) (A : Mat) (chi : Spinor) : ℂ :=
  star psi ⬝ᵥ (gamma 0*A).mulVec chi

/-- The explicit temporal Dirac matrix is Hermitian under actual conjugate transpose. -/
theorem gamma_zero_conjTranspose : (gamma 0).conjTranspose=gamma 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [gamma, Matrix.conjTranspose_apply]

/-- The temporal gamma matrix is Hermitian and each spatial gamma matrix is anti-Hermitian. -/
theorem gamma_conjTranspose (a : Fin 4) :
    (gamma a).conjTranspose = if a=0 then gamma a else -gamma a := by
  ext i j
  fin_cases a <;> fin_cases i <;> fin_cases j <;>
    norm_num [gamma, Matrix.conjTranspose_apply]

/-- Applying the actual Dirac adjoint twice recovers the original matrix. -/
theorem diracAdjoint_involutive (A : Mat) : diracAdjoint (diracAdjoint A)=A := by
  simp only [diracAdjoint, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    gamma_zero_conjTranspose]
  simp only [← mul_assoc, gamma_zero_sq, one_mul]
  rw [mul_assoc, gamma_zero_sq, mul_one]

/-- The actual Dirac adjoint reverses matrix multiplication. -/
theorem diracAdjoint_mul (A B : Mat) :
    diracAdjoint (A*B)=diracAdjoint B*diracAdjoint A := by
  simp only [diracAdjoint, Matrix.conjTranspose_mul]
  symm
  calc
    _ = gamma 0*B.conjTranspose*(gamma 0*gamma 0)*A.conjTranspose*gamma 0 := by noncomm_ring
    _ = _ := by rw [gamma_zero_sq]; simp [mul_assoc]

/-- The actual Dirac adjoint conjugates complex scalar coefficients. -/
theorem diracAdjoint_smul (z : ℂ) (A : Mat) :
    diracAdjoint (z • A) = star z • diracAdjoint A := by
  simp [diracAdjoint, Matrix.conjTranspose_smul]

/-- The matrix identity is fixed by the Dirac adjoint. -/
theorem diracAdjoint_one : diracAdjoint 1 = 1 := by
  simp [diracAdjoint, gamma_zero_sq]

/-- The Dirac adjoint preserves addition of matrices. -/
theorem diracAdjoint_add (A B : Mat) :
    diracAdjoint (A+B)=diracAdjoint A+diracAdjoint B := by
  simp [diracAdjoint, mul_add, add_mul]

/-- The Dirac adjoint preserves matrix negation. -/
theorem diracAdjoint_neg (A : Mat) : diracAdjoint (-A) = -diracAdjoint A := by
  simp [diracAdjoint]

/-- The Dirac adjoint preserves matrix subtraction. -/
theorem diracAdjoint_sub (A B : Mat) :
    diracAdjoint (A-B)=diracAdjoint A-diracAdjoint B := by
  simp [sub_eq_add_neg, diracAdjoint_add, diracAdjoint_neg]

/-- Every upper-index Dirac gamma matrix is self-adjoint for the actual Dirac adjoint. -/
theorem diracAdjoint_gamma (a : Fin 4) : diracAdjoint (gamma a)=gamma a := by
  unfold diracAdjoint
  rw [gamma_conjTranspose]
  ext i j
  fin_cases a <;> fin_cases i <;> fin_cases j <;>
    norm_num [gamma, Matrix.mul_apply, Fin.sum_univ_succ]

/-- Every actual Dirac bivector sigma matrix is self-adjoint for the Dirac adjoint. -/
theorem diracAdjoint_sigma (a b : Fin 4) : diracAdjoint (sigma a b)=sigma a b := by
  simp only [sigma, diracAdjoint_smul, diracAdjoint_sub, diracAdjoint_mul, diracAdjoint_gamma]
  ext i j
  simp
  ring

/-- The actual ordered chiral matrix is Hermitian under conjugate transpose. -/
theorem gamma5_conjTranspose : gamma5.conjTranspose=gamma5 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [gamma5, gamma, Matrix.conjTranspose_apply, Matrix.mul_apply, Fin.sum_univ_succ]

/-- The chiral matrix is anti-self-adjoint for the actual Dirac adjoint, as required by the source chiral signs. -/
theorem diracAdjoint_gamma5 : diracAdjoint gamma5 = -gamma5 := by
  unfold diracAdjoint
  rw [gamma5_conjTranspose]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [gamma5, gamma, Matrix.mul_apply, Fin.sum_univ_succ]

/-- Each axial gamma product is self-adjoint for the actual Dirac adjoint. -/
theorem diracAdjoint_axial (a : Fin 4) : diracAdjoint (gamma a*gamma5)=gamma a*gamma5 := by
  rw [diracAdjoint_mul, diracAdjoint_gamma5, diracAdjoint_gamma, neg_mul,
    gamma5_anticomm, neg_neg]

/-- The actual spatial rotor generator is anti-self-adjoint for the Dirac adjoint. -/
theorem diracAdjoint_planeGenerator : diracAdjoint planeGenerator = -planeGenerator := by
  rw [planeGenerator, diracAdjoint_mul, diracAdjoint_gamma, diracAdjoint_gamma]
  apply eq_neg_of_add_eq_zero_left
  simpa [eta] using clifford 2 1

/-- The actual spinor bilinear is complex-linear in its matrix argument. -/
theorem bilinear_smul_matrix (psi chi : Spinor) (z : ℂ) (A : Mat) :
    bilinear psi (z • A) chi=z*bilinear psi A chi := by
  simp [bilinear, Matrix.smul_mulVec, dotProduct_smul]

/-- The actual spinor bilinear is conjugate-linear in its first spinor argument. -/
theorem bilinear_smul_left (psi chi : Spinor) (z : ℂ) (A : Mat) :
    bilinear (z • psi) A chi=star z*bilinear psi A chi := by
  have hs : star (z • psi) = star z • star psi := by
    ext i
    simp
  simp only [bilinear, hs, smul_dotProduct, smul_eq_mul]

/-- The actual spinor bilinear is complex-linear in its second spinor argument. -/
theorem bilinear_smul_right (psi chi : Spinor) (z : ℂ) (A : Mat) :
    bilinear psi A (z • chi)=z*bilinear psi A chi := by
  simp [bilinear, Matrix.mulVec_smul, dotProduct_smul]

/-- The spinor bilinear preserves addition of matrices. -/
theorem bilinear_add_matrix (psi chi : Spinor) (A B : Mat) :
    bilinear psi (A+B) chi=bilinear psi A chi+bilinear psi B chi := by
  simp [bilinear, mul_add, Matrix.add_mulVec, dotProduct_add]

/-- Negating the matrix negates the spinor bilinear. -/
theorem bilinear_neg_matrix (psi chi : Spinor) (A : Mat) :
    bilinear psi (-A) chi = -bilinear psi A chi := by
  simp [bilinear, Matrix.neg_mulVec, dotProduct_neg]

/-- Conjugating the actual spinor bilinear swaps the spinors and takes the Dirac adjoint of its matrix. -/
theorem star_bilinear (psi chi : Spinor) (A : Mat) :
    star (bilinear psi A chi)=bilinear chi (diracAdjoint A) psi := by
  unfold bilinear
  rw [star_dotProduct, star_star, star_mulVec, ← dotProduct_mulVec]
  congr 2
  simp only [Matrix.conjTranspose_mul, gamma_zero_conjTranspose, diracAdjoint]
  simp only [← mul_assoc, gamma_zero_sq, one_mul]

/-- Moving an actual matrix action from the first spinor to the bilinear takes its Dirac adjoint. -/
theorem bilinear_mulVec_left (psi chi : Spinor) (A B : Mat) :
    bilinear (A.mulVec psi) B chi=bilinear psi (diracAdjoint A*B) chi := by
  unfold bilinear
  rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec]
  congr 2
  simp only [diracAdjoint]
  simp only [← mul_assoc, gamma_zero_sq, one_mul]

/-- A matrix product inside the bilinear acts successively on the second spinor. -/
theorem bilinear_mul_matrix (psi chi : Spinor) (A B : Mat) :
    bilinear psi (A*B) chi=bilinear psi A (B.mulVec chi) := by
  simp [bilinear, Matrix.mul_assoc, Matrix.mulVec_mulVec]

/-- A Dirac-self-adjoint matrix has real diagonal spinor bilinears. -/
theorem bilinear_im_eq_zero_of_selfAdjoint (psi : Spinor) {A : Mat}
    (hA : diracAdjoint A=A) : (bilinear psi A psi).im=0 := by
  apply Complex.conj_eq_iff_im.mp
  change star (bilinear psi A psi)=bilinear psi A psi
  rw [star_bilinear, hA]

/-- Every component of the actual Dirac vector bilinear is real for an arbitrary spinor. -/
theorem vector_bilinear_real (psi : Spinor) (a : Fin 4) :
    (bilinear psi (gamma a) psi).im=0 :=
  bilinear_im_eq_zero_of_selfAdjoint psi (diracAdjoint_gamma a)

/-- Every component of the actual axial-vector bilinear is real for an arbitrary spinor. -/
theorem axial_bilinear_real (psi : Spinor) (a : Fin 4) :
    (bilinear psi (gamma a*gamma5) psi).im=0 :=
  bilinear_im_eq_zero_of_selfAdjoint psi (diracAdjoint_axial a)

/-- The actual scalar Dirac bilinear is real for every complex spinor. -/
theorem scalar_bilinear_real (psi : Spinor) : (bilinear psi 1 psi).im=0 :=
  bilinear_im_eq_zero_of_selfAdjoint psi diracAdjoint_one

/-- The source signed pseudoscalar minus i times the gamma5 bilinear is real for every complex spinor. -/
theorem pseudoscalar_bilinear_real (psi : Spinor) :
    (-Complex.I*bilinear psi gamma5 psi).im=0 := by
  apply Complex.conj_eq_iff_im.mp
  change star (-Complex.I*bilinear psi gamma5 psi)= -Complex.I*bilinear psi gamma5 psi
  rw [star_mul, star_bilinear, diracAdjoint_gamma5, bilinear_neg_matrix]
  simp [mul_comm]

/-- The fixed rest spinor has scalar Dirac bilinear one. -/
theorem rest_scalar : bilinear restSpinor 1 restSpinor=1 := by
  norm_num [bilinear, gamma, restSpinor, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

/-- The fixed rest spinor has zero gamma5 pseudoscalar bilinear. -/
theorem rest_pseudoscalar : bilinear restSpinor gamma5 restSpinor=0 := by
  norm_num [bilinear, gamma, gamma5, restSpinor, Matrix.mulVec, dotProduct,
    Matrix.mul_apply, Fin.sum_univ_succ]

/-- The four actual rest-spinor vector bilinears equal delta a0. -/
theorem rest_vector (a : Fin 4) :
    bilinear restSpinor (gamma a) restSpinor=if a=0 then 1 else 0 := by
  fin_cases a <;> norm_num [bilinear, gamma, restSpinor, Matrix.mulVec, dotProduct,
    Matrix.mul_apply, Fin.sum_univ_succ]

/-- The four actual rest-spinor axial bilinears equal delta a3 with the source positive axial-three sign. -/
theorem rest_axial (a : Fin 4) :
    bilinear restSpinor (gamma a*gamma5) restSpinor=if a=3 then 1 else 0 := by
  fin_cases a <;> norm_num [bilinear, gamma, gamma5, restSpinor, Matrix.mulVec, dotProduct,
    Matrix.mul_apply, Fin.sum_univ_succ]

end FoliationQM.DiracAdjoint
