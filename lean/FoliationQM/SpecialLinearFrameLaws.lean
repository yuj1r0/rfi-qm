module
public import FoliationQM.SpecialLinearFrame
public import FoliationQM.SpinorMatrixSmooth
/-!
# Actual algebraic laws of the constructed real frame

Sources: v13 `eq:tetrad_rotor_map` and the real Lorentz frame in
`prop:takabayasi`. The concrete Dirac sandwich supplies every gamma
expansion used here. Actual matrix composition and Dirac-adjoint reversal
then give identity, sign invariance and the reversed coefficient-matrix
product law: the input gamma label is stored as a row.

For determinant-one two-by-two inputs, the actual Clifford relation gives
row and column Minkowski orthonormality and the signed-transpose inverse.
The explicit inverse and adjugate inputs give the inverse frame matrix.
No real expansion, normalization, inverse frame, or time orientation is
supplied as a premise. This file does not classify the complete Lorentz
image or identify an abstract spin covering.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.SpecialLinearFrameLaws
open DiracMatrices DiracAdjoint SpinorMatrix SpecialLinearSpin SpecialLinearFrame
open RealLorentzFrame

/-- The constructed real frame as an actual matrix, so products use matrix multiplication rather than pointwise function multiplication. -/
def frameMatrix (A : Mat2) : Matrix (Fin 4) (Fin 4) ℝ := Matrix.of (frame A)

/-- Entries of the actual frame matrix are the already constructed real frame coefficients. -/
theorem frameMatrix_apply (A : Mat2) (a mu : Fin 4) : frameMatrix A a mu = frame A a mu := rfl

/-- The two-by-two identity induces the actual identity coefficient matrix. -/
theorem frame_one : frameMatrix (1 : Mat2) = 1 := by
  ext a mu
  have hh : gammaExpansion (frame (1 : Mat2) a) = gammaExpansion ((1 : Matrix (Fin 4) (Fin 4) ℝ) a) := by
    rw [← sandwich_expansion, spin_one, diracAdjoint_one]
    simp [gammaExpansion, Matrix.one_apply]
  exact congrFun (gammaExpansion_injective hh) mu

/-- Negating the actual two-by-two representative leaves its constructed real frame unchanged. -/
theorem frame_neg (A : Mat2) : frame (-A) = frame A := by
  have hs : spin (-A) = -spin A := SpinorMatrixSmooth.spinCLM.map_neg A
  funext a
  apply gammaExpansion_injective
  rw [← sandwich_expansion, ← sandwich_expansion, hs, diracAdjoint_neg]
  simp

/-- The actual coefficient matrix is invariant under the simultaneous representative sign change. -/
theorem frameMatrix_neg (A : Mat2) : frameMatrix (-A) = frameMatrix A := by
  simp only [frameMatrix, frame_neg]

/-- Actual representative multiplication induces reversed coefficient-matrix multiplication because input gamma labels are rows. -/
theorem frame_mul (A B : Mat2) : frameMatrix (A*B) = frameMatrix B * frameMatrix A := by
  ext a mu
  have hh : gammaExpansion (frame (A*B) a) =
      gammaExpansion (fun nu => ∑ b : Fin 4, frame B a b * frame A b nu) := by
    rw [← sandwich_expansion, spin_mul, diracAdjoint_mul, gammaExpansion_sum_smul]
    calc
      _ = spin A * (spin B * gamma a * diracAdjoint (spin B)) * diracAdjoint (spin A) := by noncomm_ring
      _ = spin A * gammaExpansion (frame B a) * diracAdjoint (spin A) := by rw [sandwich_expansion]
      _ = ∑ b : Fin 4, (frame B a b : ℂ) •
          (spin A * gamma b * diracAdjoint (spin A)) := by
        simp [gammaExpansion, Matrix.mul_sum, Matrix.sum_mul]
      _ = _ := by simp only [sandwich_expansion]
  simpa only [frameMatrix_apply, Matrix.mul_apply] using congrFun (gammaExpansion_injective hh) mu

/-- The constructed frame rows are Minkowski orthonormal for determinant-one inputs, derived from the actual conjugation and Clifford relations. -/
theorem frame_row_orthonormal (A : Mat2) (hA : A.det = 1) (a b : Fin 4) :
    minkowski (frame A a) (frame A b) = if a = b then sign a else 0 :=
  row_orthonormal (spin_isUnit A hA) (frame_expansion A hA) a b

/-- The constructed real frame has the explicit signed-sum row normalization used in source contractions. -/
theorem frame_row_orthonormal_sum (A : Mat2) (hA : A.det = 1) (a b : Fin 4) :
    (∑ mu : Fin 4, sign mu * frame A a mu * frame A b mu) =
      if a = b then sign a else 0 :=
  row_orthonormal_sum (spin_isUnit A hA) (frame_expansion A hA) a b

/-- The actual metric-signed transpose is a left inverse of the constructed determinant-one frame matrix. -/
theorem inverseCoefficients_mul_frame (A : Mat2) (hA : A.det = 1) :
    inverseCoefficients (frame A) * frameMatrix A = 1 :=
  inverse_coefficients_mul (spin_isUnit A hA) (frame_expansion A hA)

/-- The actual metric-signed transpose is also a right inverse of the constructed frame matrix. -/
theorem frame_mul_inverseCoefficients (A : Mat2) (hA : A.det = 1) :
    frameMatrix A * inverseCoefficients (frame A) = 1 :=
  mul_eq_one_comm.mp (inverseCoefficients_mul_frame A hA)

/-- Every determinant-one two-by-two input induces an actually invertible real frame matrix. -/
theorem frameMatrix_isUnit (A : Mat2) (hA : A.det = 1) : IsUnit (frameMatrix A) := by
  exact ⟨⟨frameMatrix A, inverseCoefficients (frame A),
    frame_mul_inverseCoefficients A hA, inverseCoefficients_mul_frame A hA⟩, rfl⟩

/-- The actual inverse frame matrix equals the transpose with both explicit Minkowski metric signs. -/
theorem frameMatrix_inv_eq_inverseCoefficients (A : Mat2) (hA : A.det = 1) :
    (frameMatrix A)⁻¹ = inverseCoefficients (frame A) :=
  Matrix.inv_eq_left_inv (inverseCoefficients_mul_frame A hA)

/-- The actual frame columns are Minkowski orthonormal as a consequence of the derived inverse coefficient identity. -/
theorem frame_column_orthonormal (A : Mat2) (hA : A.det = 1) (a b : Fin 4) :
    minkowski (fun nu => frame A nu a) (fun nu => frame A nu b) =
      if a = b then sign a else 0 := by
  have hh := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℝ => M a b)
    (inverseCoefficients_mul_frame A hA)
  have hs : sign a * (∑ nu : Fin 4, sign nu * frame A nu a * frame A nu b) =
      if a = b then 1 else 0 := by
    simpa only [Matrix.mul_apply, inverseCoefficients, frameMatrix_apply,
      Matrix.one_apply, Finset.mul_sum, mul_assoc] using hh
  rw [minkowski_eq_sum]
  calc
    _ = sign a * (sign a * (∑ nu : Fin 4, sign nu * frame A nu a * frame A nu b)) := by
      rw [← mul_assoc, sign_sq, one_mul]
    _ = sign a * (if a = b then 1 else 0) := by rw [hs]
    _ = _ := by split_ifs <;> simp

/-- The physical inverse-frame columns are Minkowski orthonormal without any supplied normalization premise. -/
theorem frame_inverse_columns_orthonormal (A : Mat2) (hA : A.det = 1) (a b : Fin 4) :
    minkowski (fun mu => inverseCoefficients (frame A) mu a)
      (fun mu => inverseCoefficients (frame A) mu b) =
        if a = b then sign a else 0 :=
  inverse_columns_orthonormal (spin_isUnit A hA) (frame_expansion A hA) a b

/-- The actual inverse two-by-two input induces the actual inverse real frame matrix on determinant-one inputs. -/
theorem frame_inv (A : Mat2) (hA : A.det = 1) :
    frameMatrix (A⁻¹) = (frameMatrix A)⁻¹ := by
  have hi : A * A⁻¹ = 1 := Matrix.mul_nonsing_inv A (by rw [hA]; exact isUnit_one)
  have hf : frameMatrix (A⁻¹) * frameMatrix A = 1 := by
    rw [← frame_mul, hi, frame_one]
  exact (Matrix.inv_eq_left_inv hf).symm

/-- The frame of the actual inverse input equals the explicit metric-signed transpose of the forward coefficients. -/
theorem frame_inv_coefficients (A : Mat2) (hA : A.det = 1) :
    frameMatrix (A⁻¹) = inverseCoefficients (frame A) := by
  rw [frame_inv A hA, frameMatrix_inv_eq_inverseCoefficients A hA]

/-- For determinant-one inputs, the actual adjugate induces the same explicit inverse frame coefficients. -/
theorem frame_adjugate (A : Mat2) (hA : A.det = 1) :
    frameMatrix A.adjugate = inverseCoefficients (frame A) := by
  have hi : A⁻¹ = A.adjugate := Matrix.inv_eq_left_inv (by rw [Matrix.adjugate_mul, hA, one_smul])
  rw [← hi, frame_inv_coefficients A hA]

end FoliationQM.SpecialLinearFrameLaws
