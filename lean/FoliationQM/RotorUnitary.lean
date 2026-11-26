module
public import FoliationQM.PlaneRotor
public import FoliationQM.DiracAdjoint

/-!
# Unitary and Dirac-unitary plane-rotor identities

Sources: v13 `eq:rotor_compton_evolution`, the matrix premises of
`prop:takabayasi`, and `eq:scalar_pseudoscalar_bilinears`.
The conjugate transpose and Dirac adjoint are actual operations on the
concrete complex matrices. The assertions concern this spatial rotation
subgroup and explicit matrix hypotheses; no full spin-group classification
or polar reconstruction follows from them.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.RotorUnitary
open DiracMatrices PlaneRotor DiracAdjoint

/-- The actual spatial-plane Clifford generator is skew Hermitian. -/
theorem generator_conjTranspose : planeGenerator.conjTranspose = -planeGenerator := by
  rw [planeGenerator_diagonal]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.conjTranspose_apply]

/-- The actual conjugate transpose of a plane rotor reverses its half-angle. -/
theorem rotor_conjTranspose (theta : ℝ) : (rotor theta).conjTranspose = rotor (-theta) := by
  rw [rotor, Matrix.conjTranspose_add, Matrix.conjTranspose_smul, Matrix.conjTranspose_smul,
    Matrix.conjTranspose_one, generator_conjTranspose, rotor_neg]
  simp only [Complex.star_def, Complex.conj_ofReal, smul_neg, sub_eq_add_neg]

/-- The actual Dirac adjoint of a plane rotor reverses its half-angle. -/
theorem rotor_diracAdjoint (theta : ℝ) : diracAdjoint (rotor theta) = rotor (-theta) := by
  rw [rotor, diracAdjoint_add, diracAdjoint_smul, diracAdjoint_smul,
    diracAdjoint_one, diracAdjoint_planeGenerator, rotor_neg]
  simp only [Complex.star_def, Complex.conj_ofReal, smul_neg, sub_eq_add_neg]

/-- The conjugate transpose is an actual left inverse of the plane rotor. -/
theorem rotor_conjTranspose_mul (theta : ℝ) : (rotor theta).conjTranspose * rotor theta = 1 := by
  rw [rotor_conjTranspose, rotor_negative_mul]

/-- The conjugate transpose is an actual right inverse of the plane rotor. -/
theorem rotor_mul_conjTranspose (theta : ℝ) : rotor theta * (rotor theta).conjTranspose = 1 := by
  rw [rotor_conjTranspose, rotor_mul_negative]

/-- The Dirac adjoint is an actual left inverse of the plane rotor. -/
theorem rotor_diracAdjoint_mul (theta : ℝ) : diracAdjoint (rotor theta) * rotor theta = 1 := by
  rw [rotor_diracAdjoint, rotor_negative_mul]

/-- The Dirac adjoint is an actual right inverse of the plane rotor. -/
theorem rotor_mul_diracAdjoint (theta : ℝ) : rotor theta * diracAdjoint (rotor theta) = 1 := by
  rw [rotor_diracAdjoint, rotor_mul_negative]

/-- The actual even spatial-plane generator commutes with gamma5. -/
theorem generator_commute_gamma5 : Commute planeGenerator gamma5 := by
  change (gamma 1 * gamma 2) * gamma5 = gamma5 * (gamma 1 * gamma 2)
  calc
    (gamma 1 * gamma 2) * gamma5 = gamma 1 * (gamma 2 * gamma5) := mul_assoc _ _ _
    _ = -(gamma 1 * (gamma5 * gamma 2)) := by rw [gamma5_anticomm 2, mul_neg, neg_neg]
    _ = -((gamma 1 * gamma5) * gamma 2) := by rw [mul_assoc]
    _ = gamma5 * (gamma 1 * gamma 2) := by rw [← mul_assoc, gamma5_anticomm 1, neg_mul]

/-- Every actual plane rotor commutes with gamma5. -/
theorem rotor_commute_gamma5 (theta : ℝ) : Commute (rotor theta) gamma5 := by
  change rotor theta * gamma5 = gamma5 * rotor theta
  simp only [rotor, add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one,
    generator_commute_gamma5.eq]

/-- Acting by the actual plane rotor preserves the scalar Dirac pairing of any two spinors. -/
theorem rotor_preserves_scalar (theta : ℝ) (psi chi : Spinor) :
    bilinear ((rotor theta).mulVec psi) 1 ((rotor theta).mulVec chi) = bilinear psi 1 chi := by
  rw [bilinear_mulVec_left, mul_one, ← bilinear_mul_matrix, rotor_diracAdjoint_mul]

/-- Acting by the actual plane rotor preserves the gamma5 pairing of any two spinors. -/
theorem rotor_preserves_pseudoscalar (theta : ℝ) (psi chi : Spinor) :
    bilinear ((rotor theta).mulVec psi) gamma5 ((rotor theta).mulVec chi) =
      bilinear psi gamma5 chi := by
  rw [bilinear_mulVec_left, ← bilinear_mul_matrix, mul_assoc,
    ← (rotor_commute_gamma5 theta).eq, ← mul_assoc, rotor_diracAdjoint_mul, one_mul]

/-- Right multiplication by a plane rotor preserves an initial matrix Dirac isometry. -/
theorem initial_dirac_isometry_preserved (L0 : Mat) (h : diracAdjoint L0 * L0 = 1) (theta : ℝ) :
    diracAdjoint (L0 * rotor theta) * (L0 * rotor theta) = 1 := by
  rw [diracAdjoint_mul, mul_assoc, ← mul_assoc (diracAdjoint L0), h, one_mul,
    rotor_diracAdjoint_mul]

end FoliationQM.RotorUnitary
