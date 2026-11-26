module

public import FoliationQM.RotorExponential
public import FoliationQM.DiracAdjoint

/-!
# The actual chiral Dirac matrix

Sources: v13 `prop:takabayasi`, `eq:scalar_pseudoscalar_bilinears`, and the
chiral matrix conventions in `sec:spinor`. The parameter beta is the full
source chiral angle; the trigonometric coefficients use beta/2. All products,
conjugate transposes, Dirac adjoints and inverses are actual matrix operations
in the explicit Dirac representation. The genuine normed-algebra matrix
exponential is computed by a verified change of basis to diagonal gamma0. No general polar-reconstruction or
spin-group quotient classification is assumed or asserted.
-/

@[expose] public section
noncomputable section
open scoped Matrix.Norms.Operator
namespace FoliationQM.ChiralMatrix
open DiracMatrices DiracAdjoint

/-- The actual chiral matrix at full source angle beta, with gamma5 half-angle coefficients. -/
def chiral (beta : ℝ) : Mat :=
  (Real.cos (beta / 2) : ℂ) • 1 + (Complex.I * (Real.sin (beta / 2) : ℂ)) • gamma5

/-- The actual chiral matrix is the identity at zero angle. -/
theorem chiral_zero : chiral 0 = 1 := by simp [chiral]

/-- Addition of full chiral angles gives actual matrix multiplication. -/
theorem chiral_add (a b : ℝ) : chiral (a + b) = chiral a * chiral b := by
  simp only [chiral, add_div, Real.cos_add, Real.sin_add, Complex.ofReal_sub,
    Complex.ofReal_mul, Complex.ofReal_add, add_mul, mul_add, smul_mul_assoc,
    mul_smul_comm, one_mul, mul_one, gamma5_sq]
  match_scalars <;> ring_nf
  norm_num
  ring

/-- Negating the chiral angle reverses the gamma5 term. -/
theorem chiral_neg (beta : ℝ) :
    chiral (-beta) = (Real.cos (beta / 2) : ℂ) • 1 -
      (Complex.I * (Real.sin (beta / 2) : ℂ)) • gamma5 := by
  simp only [chiral, neg_div, Real.cos_neg, Real.sin_neg, Complex.ofReal_neg,
    mul_neg, neg_smul, sub_eq_add_neg]

/-- The negative-angle chiral matrix is an actual right inverse. -/
theorem chiral_mul_negative (beta : ℝ) : chiral beta * chiral (-beta) = 1 := by
  rw [← chiral_add, add_neg_cancel, chiral_zero]

/-- The negative-angle chiral matrix is an actual left inverse. -/
theorem chiral_negative_mul (beta : ℝ) : chiral (-beta) * chiral beta = 1 := by
  rw [← chiral_add, neg_add_cancel, chiral_zero]

/-- The actual nonsingular inverse of the chiral matrix has the negative full angle. -/
theorem chiral_inv (beta : ℝ) : (chiral beta)⁻¹ = chiral (-beta) :=
  Matrix.inv_eq_left_inv (chiral_negative_mul beta)

/-- Every actual chiral matrix is a matrix unit. -/
theorem chiral_isUnit (beta : ℝ) : IsUnit (chiral beta) :=
  ⟨⟨chiral beta, chiral (-beta), chiral_mul_negative beta, chiral_negative_mul beta⟩, rfl⟩

/-- The actual Dirac adjoint fixes the chiral matrix, as required by the source polar bilinears. -/
theorem chiral_diracAdjoint (beta : ℝ) : diracAdjoint (chiral beta) = chiral beta := by
  simp only [chiral, diracAdjoint_add, diracAdjoint_smul, diracAdjoint_one,
    diracAdjoint_gamma5, star_mul, Complex.star_def, Complex.conj_ofReal, Complex.conj_I,
    smul_neg]
  module

/-- The ordinary actual conjugate transpose reverses the chiral angle. -/
theorem chiral_conjTranspose (beta : ℝ) : (chiral beta).conjTranspose = chiral (-beta) := by
  rw [chiral_neg]
  simp only [chiral, Matrix.conjTranspose_add, Matrix.conjTranspose_smul,
    Matrix.conjTranspose_one, gamma5_conjTranspose, star_mul, Complex.star_def,
    Complex.conj_ofReal, Complex.conj_I, sub_eq_add_neg]
  module

/-- The actual chiral matrix commutes with gamma5. -/
theorem chiral_gamma5_commute (beta : ℝ) : Commute (chiral beta) gamma5 := by
  change chiral beta * gamma5 = gamma5 * chiral beta
  simp [chiral, add_mul, mul_add]

/-- Moving an actual gamma matrix past the chiral matrix reverses the chiral angle. -/
theorem chiral_gamma_swap (beta : ℝ) (a : Fin 4) :
    chiral beta * gamma a = gamma a * chiral (-beta) := by
  rw [chiral_neg]
  simp only [chiral, add_mul, mul_add, mul_neg, smul_mul_assoc, mul_smul_comm,
    one_mul, mul_one, gamma5_anticomm, smul_neg, sub_eq_add_neg]

/-- Equal chiral factors on both sides of a gamma matrix cancel exactly. -/
theorem chiral_gamma_cancel (beta : ℝ) (a : Fin 4) :
    chiral beta * gamma a * chiral beta = gamma a := by
  rw [chiral_gamma_swap, mul_assoc, chiral_negative_mul, mul_one]

/-- Equal chiral factors on both sides of an axial gamma product also cancel exactly. -/
theorem chiral_axial_cancel (beta : ℝ) (a : Fin 4) :
    chiral beta * (gamma a * gamma5) * chiral beta = gamma a * gamma5 := by
  calc
    _ = (chiral beta * gamma a) * (gamma5 * chiral beta) := by simp only [mul_assoc]
    _ = (chiral beta * gamma a) * (chiral beta * gamma5) := by
      rw [← (chiral_gamma5_commute beta).eq]
    _ = _ := by rw [← mul_assoc, chiral_gamma_cancel]

/-- Squaring the actual chiral matrix gives full-angle cosine and i sine coefficients. -/
theorem chiral_squared (beta : ℝ) :
    chiral beta * chiral beta =
      (Real.cos beta : ℂ) • 1 + (Complex.I * (Real.sin beta : ℂ)) • gamma5 := by
  rw [← chiral_add, chiral]
  rw [show (beta + beta) / 2 = beta by ring]

/-- Increasing the full chiral angle by two pi changes the sign of the actual matrix. -/
theorem chiral_add_two_pi (beta : ℝ) : chiral (beta + 2 * Real.pi) = -chiral beta := by
  have h : (beta + 2 * Real.pi) / 2 = beta / 2 + Real.pi := by ring
  simp only [chiral, h, Real.cos_add_pi, Real.sin_add_pi, Complex.ofReal_neg,
    mul_neg, neg_smul, neg_add_rev]
  abel

/-- Increasing the full chiral angle by four pi preserves the actual matrix. -/
theorem chiral_add_four_pi (beta : ℝ) : chiral (beta + 4 * Real.pi) = chiral beta := by
  have h : beta + 4 * Real.pi = (beta + 2 * Real.pi) + 2 * Real.pi := by ring
  rw [h, chiral_add_two_pi, chiral_add_two_pi, neg_neg]

/-- The actual chiral matrix has full-angle period four pi. -/
theorem chiral_periodic : Function.Periodic chiral (4 * Real.pi) := chiral_add_four_pi

/-- The ordinary actual conjugate transpose is the actual nonsingular inverse of the chiral matrix. -/
theorem chiral_conjTranspose_eq_inv (beta : ℝ) :
    (chiral beta).conjTranspose = (chiral beta)⁻¹ := by
  rw [chiral_conjTranspose, chiral_inv]

private def basisChange : Mat :=
  !![1, 0, 1, 0; 0, 1, 0, 1; 1, 0, -1, 0; 0, 1, 0, -1]

private theorem basisChange_mul_inverse : basisChange * ((1 / 2 : ℂ) • basisChange) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [basisChange, Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_succ]

private theorem basisChange_inverse_mul : ((1 / 2 : ℂ) • basisChange) * basisChange = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [basisChange, Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_succ]

private def basisChangeUnit : Matˣ :=
  ⟨basisChange, (1 / 2 : ℂ) • basisChange, basisChange_mul_inverse, basisChange_inverse_mul⟩

private theorem gamma5_diagonalization :
    basisChange * gamma 0 * ((1 / 2 : ℂ) • basisChange) = gamma5 := by
  rw [gamma5_explicit]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [basisChange, gamma, Matrix.mul_apply, Fin.sum_univ_succ]

private theorem exp_scaled_gamma_zero (z : ℂ) :
    NormedSpace.exp (z • gamma 0) = Matrix.diagonal
      ![NormedSpace.exp z, NormedSpace.exp z, NormedSpace.exp (-z), NormedSpace.exp (-z)] := by
  have hg : gamma 0 = Matrix.diagonal ![1, 1, -1, -1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [gamma]
  rw [hg, ← Matrix.diagonal_smul, Matrix.exp_diagonal]
  congr 1
  ext i
  fin_cases i <;> simp [Pi.coe_exp]

private theorem exp_positive_half (beta : ℝ) :
    NormedSpace.exp (Complex.I * (beta : ℂ) / 2) =
      (Real.cos (beta / 2) : ℂ) + Complex.I * (Real.sin (beta / 2) : ℂ) := by
  rw [← Complex.exp_eq_exp_ℂ]
  calc
    _ = Complex.exp (((beta / 2 : ℝ) : ℂ) * Complex.I) := by
      congr 1
      push_cast
      ring
    _ = _ := by rw [Complex.exp_ofReal_mul_I]; ring

private theorem exp_negative_half (beta : ℝ) :
    NormedSpace.exp (-(Complex.I * (beta : ℂ) / 2)) =
      (Real.cos (beta / 2) : ℂ) - Complex.I * (Real.sin (beta / 2) : ℂ) := by
  rw [← Complex.exp_eq_exp_ℂ]
  calc
    _ = Complex.exp (-Complex.I * ((beta / 2 : ℝ) : ℂ)) := by
      congr 1
      push_cast
      ring
    _ = _ := by
      simpa [mul_comm, sub_eq_add_neg] using (PlaneRotor.negative_phase_identity (beta / 2)).symm

/-- The genuine matrix exponential of i beta gamma5/2 is the actual half-angle chiral matrix. -/
theorem exp_chiral (beta : ℝ) :
    NormedSpace.exp ((Complex.I * (beta : ℂ) / 2) • gamma5) = chiral beta := by
  let z : ℂ := Complex.I * (beta : ℂ) / 2
  have harg : z • gamma5 = basisChange * (z • gamma 0) * ((1 / 2 : ℂ) • basisChange) := by
    calc
      z • gamma5 = z • (basisChange * gamma 0 * ((1 / 2 : ℂ) • basisChange)) :=
        congrArg (z • ·) gamma5_diagonalization.symm
      _ = _ := by simp only [mul_smul_comm, smul_mul_assoc, smul_smul, mul_comm]
  have he : NormedSpace.exp (basisChange * (z • gamma 0) * ((1 / 2 : ℂ) • basisChange)) =
      basisChange * NormedSpace.exp (z • gamma 0) * ((1 / 2 : ℂ) • basisChange) :=
    Matrix.exp_units_conj basisChangeUnit (z • gamma 0)
  change NormedSpace.exp (z • gamma5) = _
  rw [harg, he, exp_scaled_gamma_zero]
  dsimp only [z]
  rw [exp_positive_half, exp_negative_half]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [basisChange, chiral, gamma5_explicit, Matrix.mul_apply, Matrix.vecMul, dotProduct,
      Matrix.diagonal_apply, Fin.sum_univ_succ] <;> ring

end FoliationQM.ChiralMatrix
