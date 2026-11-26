module
public import FoliationQM.SpecialLinearFrameLaws
public import FoliationQM.LorentzMatrixGroup
public import FoliationQM.SpecialLinearFrameSmooth
public import FoliationQM.SpecialLinearTimeOrientation
public import FoliationQM.SpecialLinearGroupManifold
public import Mathlib.Topology.Algebra.Group.Units

/-!
# The actual physical Lorentz action of determinant-one spin matrices

Sources: the concrete Lorentz rotor and tetrad map in v13
`prop:takabayasi` and `eq:tetrad_rotor_map`. The existing gamma-coefficient
matrix stores input basis indices as rows and reverses matrix products.
Its metric-signed transpose is the physical inverse-frame matrix. This
module proves its ordinary multiplicative order, metric preservation,
future time orientation, and exact source gamma expansions from the
already constructed actual Dirac representation.

The resulting units and Lorentz-group homomorphism use the independent
metric-defined matrix group and its natural topology. Matrix and group
continuity follow from the actual polynomial frame and actual inverse
maps. Determinant properness, complete image classification, kernel, and
identification with an abstract Clifford group are separate results.
-/

@[expose] public section
noncomputable section
open scoped Matrix Matrix.Norms.Operator Manifold
namespace FoliationQM.SpinLorentzAction
open DiracMatrices SpinorMatrix SpecialLinearSpin SpecialLinearFrame SpecialLinearFrameLaws
open RealLorentzFrame SourcePolarDatum SpecialLinearGroupManifold
open LorentzMatrixGroup

/-- The physical real matrix action is the metric-signed transpose of the actual upper-gamma coefficient matrix. -/
def lorentzMatrix (A : Mat2) : Mat4 :=
  LorentzMatrixGroup.eta * (frameMatrix A)ᵀ * LorentzMatrixGroup.eta

/-- Every entry of the physical matrix contains exactly the two Minkowski signs and the transposed actual frame coefficient. -/
theorem lorentzMatrix_apply (A : Mat2) (mu a : Fin 4) :
    lorentzMatrix A mu a = sign mu * sign a * frame A a mu := by
  simp only [lorentzMatrix, LorentzMatrixGroup.eta, Matrix.mul_diagonal,
    Matrix.diagonal_mul, Matrix.transpose_apply, frameMatrix_apply]
  ring

/-- The actual physical matrix equals the existing source inverse-frame coefficient matrix for every two-by-two input. -/
theorem lorentzMatrix_eq_inverseCoefficients (A : Mat2) :
    lorentzMatrix A = inverseCoefficients (frame A) := by
  ext mu a
  exact lorentzMatrix_apply A mu a

/-- The actual identity spin matrix induces the real identity transformation. -/
theorem lorentzMatrix_one : lorentzMatrix (1 : Mat2) = 1 := by
  rw [lorentzMatrix, frame_one, Matrix.transpose_one, mul_one, LorentzMatrixGroup.eta_sq]

/-- Actual two-by-two multiplication induces ordinary physical matrix multiplication, with the reversed row-frame convention explicitly corrected. -/
theorem lorentzMatrix_mul (A B : Mat2) :
    lorentzMatrix (A * B) = lorentzMatrix A * lorentzMatrix B := by
  rw [lorentzMatrix, frame_mul, Matrix.transpose_mul]
  simp only [lorentzMatrix]
  calc
    _ = LorentzMatrixGroup.eta * (frameMatrix A)ᵀ * 1 *
        (frameMatrix B)ᵀ * LorentzMatrixGroup.eta := by simp [mul_assoc]
    _ = _ := by rw [← LorentzMatrixGroup.eta_sq]; noncomm_ring

/-- The actual physical matrix action is unchanged by negating the spin representative. -/
theorem lorentzMatrix_neg (A : Mat2) : lorentzMatrix (-A) = lorentzMatrix A := by
  simp only [lorentzMatrix, frameMatrix_neg]

/-- For determinant-one inputs the physical matrix is the actual inverse of the upper-gamma row-frame matrix. -/
theorem lorentzMatrix_eq_frame_inv (A : Mat2) (hA : A.det = 1) :
    lorentzMatrix A = (frameMatrix A)⁻¹ := by
  rw [lorentzMatrix_eq_inverseCoefficients, frameMatrix_inv_eq_inverseCoefficients A hA]

/-- The physical matrix is a left inverse of the actual gamma coefficient matrix on determinant-one inputs. -/
theorem lorentzMatrix_mul_frame (A : Mat2) (hA : A.det = 1) :
    lorentzMatrix A * frameMatrix A = 1 := by
  rw [lorentzMatrix_eq_inverseCoefficients]
  exact inverseCoefficients_mul_frame A hA

/-- The physical matrix is also a right inverse of the gamma coefficient matrix on determinant-one inputs. -/
theorem frame_mul_lorentzMatrix (A : Mat2) (hA : A.det = 1) :
    frameMatrix A * lorentzMatrix A = 1 := by
  rw [lorentzMatrix_eq_inverseCoefficients]
  exact frame_mul_inverseCoefficients A hA

/-- Every determinant-one input induces an actually invertible physical real matrix. -/
theorem lorentzMatrix_isUnit (A : Mat2) (hA : A.det = 1) :
    IsUnit (lorentzMatrix A) := by
  exact ⟨⟨lorentzMatrix A, frameMatrix A,
    lorentzMatrix_mul_frame A hA, frame_mul_lorentzMatrix A hA⟩, rfl⟩

/-- Actual inversion of a determinant-one spin representative induces actual inversion of its physical real matrix. -/
theorem lorentzMatrix_inv (A : Mat2) (hA : A.det = 1) :
    lorentzMatrix A⁻¹ = (lorentzMatrix A)⁻¹ := by
  have hi : A * A⁻¹ = 1 := Matrix.mul_nonsing_inv A (by rw [hA]; exact isUnit_one)
  apply Eq.symm
  apply Matrix.inv_eq_right_inv
  rw [← lorentzMatrix_mul, hi, lorentzMatrix_one]

/-- The actual physical matrix preserves the independent Minkowski metric matrix for determinant-one inputs. -/
theorem lorentzMatrix_metric (A : Mat2) (hA : A.det = 1) :
    (lorentzMatrix A)ᵀ * LorentzMatrixGroup.eta * lorentzMatrix A =
      LorentzMatrixGroup.eta := by
  ext i j
  rw [Matrix.mul_apply]
  simp only [LorentzMatrixGroup.eta, Matrix.mul_diagonal, Matrix.transpose_apply]
  have hm := frame_inverse_columns_orthonormal A hA i j
  rw [minkowski_eq_sum] at hm
  simpa only [lorentzMatrix_eq_inverseCoefficients, Matrix.diagonal_apply, mul_comm,
    mul_left_comm, mul_assoc] using hm

/-- The physical time component is at least one, using the already derived future physical time column. -/
theorem lorentzMatrix_time_ge_one (A : Mat2) (hA : A.det = 1) :
    1 ≤ lorentzMatrix A 0 0 := by
  rw [lorentzMatrix_eq_inverseCoefficients]
  exact SpecialLinearTimeOrientation.frame_time_ge_one A hA

/-- The actual physical time component is strictly positive for every determinant-one representative. -/
theorem lorentzMatrix_time_pos (A : Mat2) (hA : A.det = 1) :
    0 < lorentzMatrix A 0 0 := lt_of_lt_of_le zero_lt_one (lorentzMatrix_time_ge_one A hA)

/-- Conjugating a lower-index Dirac basis matrix gives precisely the physical matrix column in the lower-index gamma basis. -/
theorem physical_frame_expansion (A : Mat2) (hA : A.det = 1) (a : Fin 4) :
    spin A * gammaLower a * (spin A)⁻¹ =
      ∑ mu : Fin 4, (lorentzMatrix A mu a : ℂ) • gammaLower mu := by
  rw [lorentzMatrix_eq_inverseCoefficients]
  exact PolarVectorGeometry.physical_frame_expansion (frame_expansion A hA) a

/-- Inverse Dirac conjugation of an upper-index gamma matrix gives precisely the physical matrix row in the upper-index basis. -/
theorem inverse_frame_expansion (A : Mat2) (hA : A.det = 1) (mu : Fin 4) :
    (spin A)⁻¹ * gamma mu * spin A =
      gammaExpansion (fun a => lorentzMatrix A mu a) := by
  rw [lorentzMatrix_eq_inverseCoefficients]
  exact inverse_expansion (spin_isUnit A hA) (frame_expansion A hA) mu

/-- The actual physical matrix is continuous on the entire ambient two-by-two matrix space. -/
theorem continuous_lorentzMatrix : Continuous lorentzMatrix := by
  have hf : Continuous frameMatrix :=
    (SpecialLinearFrameSmooth.contDiff_frame 0).continuous.matrixOf
  exact (continuous_const.matrix_mul hf.matrix_transpose).matrix_mul continuous_const

/-- The actual physical matrix and the matrix of the actual special linear inverse form a genuine real matrix unit. -/
def matrixUnits (A : SpecialLinearMatrix) : Mat4ˣ where
  val := lorentzMatrix A.val
  inv := lorentzMatrix (A⁻¹).val
  val_inv := by rw [← lorentzMatrix_mul, ← coe_mul, mul_inv_cancel, coe_one, lorentzMatrix_one]
  inv_val := by rw [← lorentzMatrix_mul, ← coe_mul, inv_mul_cancel, coe_one, lorentzMatrix_one]

/-- The unit value is exactly the independently defined physical real matrix. -/
theorem matrixUnits_val (A : SpecialLinearMatrix) : (matrixUnits A : Mat4) = lorentzMatrix A.val := rfl

/-- The actual inverse unit value is the physical matrix of the actual special linear group inverse. -/
theorem matrixUnits_inv_val (A : SpecialLinearMatrix) :
    ((matrixUnits A)⁻¹).val = lorentzMatrix (A⁻¹).val := rfl

/-- The constructed matrix unit preserves the actual group identity. -/
theorem matrixUnits_one : matrixUnits 1 = 1 := by
  apply Units.ext
  exact lorentzMatrix_one

/-- The constructed units preserve actual special linear multiplication. -/
theorem matrixUnits_mul (A B : SpecialLinearMatrix) : matrixUnits (A * B) = matrixUnits A * matrixUnits B := by
  apply Units.ext
  exact lorentzMatrix_mul A.val B.val

/-- The constructed units vary continuously in their natural unit topology, including both value and inverse coordinates. -/
theorem continuous_matrixUnits : Continuous matrixUnits := by
  apply Units.continuous_iff.mpr
  constructor
  · exact continuous_lorentzMatrix.comp continuous_subtype_val
  · exact continuous_lorentzMatrix.comp
      (continuous_subtype_val.comp ((SpecialLinearGroupManifold.contMDiff_inv 0).continuous))

/-- The actual determinant-one spin action is a homomorphism into the independently specified real Lorentz matrix group. -/
def lorentzHom : SpecialLinearMatrix →* LorentzMatrixGroup.Lorentz where
  toFun A := ⟨matrixUnits A, lorentzMatrix_metric A.val A.property⟩
  map_one' := Subtype.ext matrixUnits_one
  map_mul' A B := Subtype.ext (matrixUnits_mul A B)

/-- The Lorentz group homomorphism has exactly the independently defined physical matrix as its underlying real matrix. -/
theorem lorentzHom_matrix (A : SpecialLinearMatrix) :
    LorentzMatrixGroup.matrix (lorentzHom A) = lorentzMatrix A.val := rfl

/-- The actual Lorentz group homomorphism is continuous for the natural special linear, matrix-unit, and subgroup topologies. -/
theorem continuous_lorentzHom : Continuous lorentzHom :=
  continuous_matrixUnits.subtype_mk (fun A => lorentzMatrix_metric A.val A.property)

end FoliationQM.SpinLorentzAction
