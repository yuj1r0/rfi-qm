module
public import FoliationQM.CliffordEvenDimension
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# The faithful Pauli model of the even Minkowski Clifford algebra

Source scope: the abstract Clifford realization underlying v13
`prop:takabayasi` and `eq:tetrad_rotor_map`. The map is constructed from
Mathlib's genuine even Clifford universal property, with the physical
lower-gamma convention: a vector pair is sent to H(v) adj(H(w)). Its
contraction identities follow from the actual matrix adjugate and the
Minkowski determinant.

Every complex two-by-two matrix is decomposed into two real Hermitian
Pauli images. The imaginary scalar is itself the image of a concrete
product of three spatial-temporal Clifford pairs. This supplies an
explicit surjectivity proof on all matrices, with no determinant
restriction. Faithfulness uses the independently derived dimension of
the actual even algebra; subgroup identification is a separate step.
-/

@[expose] public section
noncomputable section
open scoped Matrix Matrix.Norms.Operator
namespace FoliationQM.CliffordEvenPauli
open CliffordMinkowski SpinorMatrix SpinLorentzPauli SpecialLinearSpin

private theorem adjugate_add (A B : Mat2) :
    (A+B).adjugate = A.adjugate + B.adjugate := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.adjugate_fin_two] <;> ring

private theorem adjugate_real_smul (r : ℝ) (A : Mat2) :
    (r • A).adjugate = r • A.adjugate := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.adjugate_fin_two]

/-- The real bilinear Pauli matrix product representing a pair of physical Clifford vectors. -/
def pauliPair : Vector →ₗ[ℝ] Vector →ₗ[ℝ] Mat2 :=
  LinearMap.mk₂ ℝ (fun v w => pauli v * (pauli w).adjugate)
    (fun _ _ _ => by rw [pauli_add, add_mul])
    (fun _ _ _ => by rw [pauli_smul, smul_mul_assoc])
    (fun _ _ _ => by rw [pauli_add, adjugate_add, mul_add])
    (fun _ _ _ => by rw [pauli_smul, adjugate_real_smul, mul_smul_comm])

/-- The bundled pair map evaluates to the actual Pauli-adjugate product. -/
theorem pauliPair_apply (v w : Vector) :
    pauliPair v w = pauli v * (pauli w).adjugate := rfl

/-- Equal arguments in the pair map contract to the actual Minkowski quadratic form. -/
theorem pauliPair_contract (v : Vector) :
    pauliPair v v = algebraMap ℝ Mat2 (quadratic v) := by
  rw [pauliPair_apply, Matrix.mul_adjugate, pauli_det, ← quadratic_eq_minkowski,
    Algebra.algebraMap_eq_smul_one]
  exact IsScalarTower.algebraMap_smul ℂ (quadratic v) 1

/-- Multiplying pair images contracts their common middle vector with its actual quadratic value. -/
theorem pauliPair_contract_mid (u v w : Vector) :
    pauliPair u v * pauliPair v w = quadratic v • pauliPair u w := by
  simp only [pauliPair_apply]
  calc
    _ = pauli u * ((pauli v).adjugate * pauli v) * (pauli w).adjugate := by
      simp only [mul_assoc]
    _ = quadratic v • (pauli u * (pauli w).adjugate) := by
      rw [Matrix.adjugate_mul, pauli_det, ← quadratic_eq_minkowski]
      have hs : ((quadratic v : ℂ) • (1 : Mat2)) = quadratic v • (1 : Mat2) :=
        IsScalarTower.algebraMap_smul ℂ (quadratic v) 1
      rw [hs]
      rw [mul_smul_comm, mul_one, smul_mul_assoc]

/-- The Pauli pair map satisfies the genuine universal property of the even Clifford algebra. -/
def pauliEvenHom : CliffordAlgebra.EvenHom quadratic Mat2 where
  bilin := pauliPair
  contract := pauliPair_contract
  contract_mid := pauliPair_contract_mid

/-- The actual real algebra homomorphism from the even Minkowski Clifford algebra to complex two-by-two matrices. -/
def evenPauli : CliffordAlgebra.even quadratic →ₐ[ℝ] Mat2 :=
  CliffordAlgebra.even.lift quadratic pauliEvenHom

/-- The universal even map sends an actual embedded vector pair to its physical Pauli-adjugate matrix product. -/
theorem evenPauli_pair (v w : Vector) :
    evenPauli ((CliffordAlgebra.even.ι quadratic).bilin v w) =
      pauli v * (pauli w).adjugate :=
  CliffordAlgebra.even.lift_ι quadratic pauliEvenHom v w

/-- A spatial generator paired with the temporal vector has its standard Pauli image. -/
theorem evenPauli_time_pair (v : Vector) :
    evenPauli ((CliffordAlgebra.even.ι quadratic).bilin v (basisVector 0)) = pauli v := by
  rw [evenPauli_pair]
  simp [basisVector, pauli_zero_basis]

/-- The product of the three spatial-temporal pairs represents the complex imaginary scalar. -/
def imaginaryUnit : CliffordAlgebra.even quadratic :=
  (CliffordAlgebra.even.ι quadratic).bilin (basisVector 1) (basisVector 0) *
    (CliffordAlgebra.even.ι quadratic).bilin (basisVector 2) (basisVector 0) *
    (CliffordAlgebra.even.ι quadratic).bilin (basisVector 3) (basisVector 0)

/-- The actual even Clifford product has image exactly i times the identity matrix. -/
theorem evenPauli_imaginaryUnit : evenPauli imaginaryUnit = Complex.I • (1 : Mat2) := by
  simp only [imaginaryUnit, map_mul, evenPauli_time_pair]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [basisVector, pauli, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply]

private def realVector (A : Mat2) : Vector :=
  ![((A 0 0).re+(A 1 1).re)/2, ((A 0 1).re+(A 1 0).re)/2,
    ((A 1 0).im-(A 0 1).im)/2, ((A 0 0).re-(A 1 1).re)/2]

private def imaginaryVector (A : Mat2) : Vector :=
  ![((A 0 0).im+(A 1 1).im)/2, ((A 0 1).im+(A 1 0).im)/2,
    ((A 0 1).re-(A 1 0).re)/2, ((A 0 0).im-(A 1 1).im)/2]

private theorem pauli_decomposition (A : Mat2) :
    pauli (realVector A) + Complex.I • pauli (imaginaryVector A) = A := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    apply Complex.ext <;> simp [pauli, realVector, imaginaryVector] <;> ring

/-- Every actual complex two-by-two matrix is represented by an explicit even Clifford element. -/
theorem evenPauli_surjective : Function.Surjective evenPauli := by
  intro A
  refine ⟨(CliffordAlgebra.even.ι quadratic).bilin (realVector A) (basisVector 0) +
    imaginaryUnit * (CliffordAlgebra.even.ι quadratic).bilin (imaginaryVector A) (basisVector 0), ?_⟩
  rw [map_add, map_mul, evenPauli_time_pair, evenPauli_time_pair, evenPauli_imaginaryUnit,
    smul_mul_assoc, one_mul]
  exact pauli_decomposition A

/-- Actual complex two-by-two matrices form an eight-dimensional real vector space. -/
theorem finrank_matrix : Module.finrank ℝ Mat2 = 8 := by
  have h := Module.finrank_matrix ℝ ℂ (Fin 2) (Fin 2)
  simpa [Complex.finrank_real_complex] using h

/-- The actual even Pauli representation is faithful, by its proved surjectivity and independently derived equal dimensions. -/
theorem evenPauli_injective : Function.Injective evenPauli := by
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (CliffordEvenDimension.finrank_even.trans finrank_matrix.symm)
    (f := evenPauli.toLinearMap)).mpr evenPauli_surjective

/-- The genuine even Minkowski Clifford algebra is isomorphic as a real algebra to all complex two-by-two matrices. -/
def evenPauliEquiv : CliffordAlgebra.even quadratic ≃ₐ[ℝ] Mat2 :=
  AlgEquiv.ofBijective evenPauli ⟨evenPauli_injective, evenPauli_surjective⟩

/-- The algebra equivalence retains the actual universal Pauli map. -/
theorem evenPauliEquiv_apply (x : CliffordAlgebra.even quadratic) :
    evenPauliEquiv x = evenPauli x := rfl

/-- The inverse equivalence reconstructs the actual Clifford vector pair from its physical matrix image. -/
theorem evenPauliEquiv_symm_pair (v w : Vector) :
    evenPauliEquiv.symm (pauli v * (pauli w).adjugate) =
      (CliffordAlgebra.even.ι quadratic).bilin v w := by
  apply evenPauliEquiv.injective
  rw [evenPauliEquiv.apply_symm_apply, evenPauliEquiv_apply, evenPauli_pair]

/-- The inverse equivalence sends the complex imaginary scalar to its actual even Clifford product. -/
theorem evenPauliEquiv_symm_imaginaryUnit :
    evenPauliEquiv.symm (Complex.I • (1 : Mat2)) = imaginaryUnit := by
  apply evenPauliEquiv.injective
  rw [evenPauliEquiv.apply_symm_apply, evenPauliEquiv_apply, evenPauli_imaginaryUnit]

end FoliationQM.CliffordEvenPauli
