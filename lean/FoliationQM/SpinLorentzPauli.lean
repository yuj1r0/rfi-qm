module
public import FoliationQM.SpinLorentzAction

/-!
# The explicit Hermitian Pauli model of the physical Lorentz action

Source scope: the concrete Lorentz-frame action in v13
`prop:takabayasi` and `eq:tetrad_rotor_map`. The standard Hermitian
matrix with temporal diagonal sum and spatial Pauli coefficients is
an actual injective real linear map. Its determinant is the explicit
Minkowski quadratic form in signature (+---).

The actual two-by-two sandwich A H(v) A† agrees with the previously
constructed physical Lorentz matrix. The proof extracts the upper
Weyl block of the actual lower-gamma conjugation, establishing the
spatial signs and the physical matrix convention by finite algebra.
Neither a transformation identity nor a kernel conclusion is supplied
as a premise. Image classification, covering structure, and an abstract
Clifford spin-group identification are separate obligations.
-/

@[expose] public section
noncomputable section
open scoped Matrix Matrix.Norms.Operator
namespace FoliationQM.SpinLorentzPauli
open SpinorMatrix DiracMatrices SpecialLinearSpin SpinLorentzAction

/-- The standard Hermitian Pauli matrix of an actual real Minkowski vector. -/
def pauli (v : Covector) : Mat2 :=
  !![(v 0 : ℂ) + v 3, (v 1 : ℂ) - Complex.I * v 2;
     (v 1 : ℂ) + Complex.I * v 2, (v 0 : ℂ) - v 3]

/-- The actual Pauli map preserves vector addition. -/
theorem pauli_add (v w : Covector) : pauli (v+w) = pauli v + pauli w := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pauli] <;> ring

/-- The actual Pauli map preserves multiplication by a real scalar. -/
theorem pauli_smul (a : ℝ) (v : Covector) : pauli (a • v) = a • pauli v := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pauli, Complex.real_smul] <;> ring

/-- The explicit Pauli construction bundled as a real linear map. -/
def pauliLM : Covector →ₗ[ℝ] Mat2 where
  toFun := pauli
  map_add' := pauli_add
  map_smul' := pauli_smul

/-- The bundled real linear map evaluates to the literal Pauli matrix. -/
theorem pauliLM_apply (v : Covector) : pauliLM v = pauli v := rfl

/-- The explicit Pauli construction bundled as an actual real continuous linear map. -/
def pauliCLM : Covector →L[ℝ] Mat2 := pauliLM.toContinuousLinearMap

/-- The continuous linear map retains exactly the literal matrix formula. -/
theorem pauliCLM_apply (v : Covector) : pauliCLM v = pauli v := rfl

/-- The actual Pauli matrix depends continuously on its real vector coordinates. -/
theorem continuous_pauli : Continuous pauli := pauliCLM.continuous

/-- The actual real-linear Pauli matrix map is smooth to every order. -/
theorem contDiff_pauli (n : WithTop ℕ∞) : ContDiff ℝ n pauli := pauliCLM.contDiff

/-- The actual Hermitian matrix determines all four real vector coordinates uniquely. -/
theorem pauli_injective : Function.Injective pauli := by
  intro v w h
  have h0 := congrArg (fun M : Mat2 => (M 0 0).re) h
  have h1 := congrArg (fun M : Mat2 => (M 0 1).re) h
  have h2 := congrArg (fun M : Mat2 => (M 0 1).im) h
  have h3 := congrArg (fun M : Mat2 => (M 1 1).re) h
  simp [pauli] at h0 h1 h2 h3
  ext i
  fin_cases i <;> dsimp <;> linarith

/-- Every Pauli matrix is Hermitian for the actual conjugate transpose. -/
theorem pauli_conjTranspose (v : Covector) : (pauli v).conjTranspose = pauli v := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauli, Matrix.conjTranspose_apply, sub_eq_add_neg]

/-- The actual two-by-two determinant is the complex inclusion of the Minkowski quadratic form. -/
theorem pauli_det (v : Covector) : (pauli v).det = (minkowski v v : ℂ) := by
  simp [pauli, Matrix.det_fin_two, minkowski]
  ring_nf
  simp
  ring

/-- The temporal coordinate basis vector is encoded by the actual two-by-two identity. -/
theorem pauli_zero_basis : pauli (Pi.single 0 1) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [pauli, Matrix.one_apply]

/-- The first spatial coordinate basis vector is encoded by the standard first Pauli matrix. -/
theorem pauli_one_basis : pauli (Pi.single 1 1) = !![0,1;1,0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [pauli]

/-- The second spatial coordinate basis vector has the standard imaginary off-diagonal Pauli signs. -/
theorem pauli_two_basis : pauli (Pi.single 2 1) = !![0,-Complex.I;Complex.I,0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [pauli]

/-- The third spatial coordinate basis vector is encoded by the standard diagonal Pauli matrix. -/
theorem pauli_three_basis : pauli (Pi.single 3 1) = !![1,0;0,-1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [pauli]

private def lowerGamma (v : Covector) : Mat := ∑ mu, (v mu : ℂ) • gammaLower mu

private def upperWeyl (M : Mat) : Mat2 :=
  !![M 0 0+M 2 0, M 0 1+M 2 1; M 1 0+M 3 0, M 1 1+M 3 1]

private theorem upperWeyl_lowerGamma (v : Covector) : upperWeyl (lowerGamma v) = pauli v := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [upperWeyl, lowerGamma, pauli, gammaLower, gamma, Fin.sum_univ_succ] <;> ring

private theorem lowerGamma_conjugation (A : Mat2) (hA : A.det = 1) (v : Covector) :
    spin A * lowerGamma v * (spin A)⁻¹ = lowerGamma (lorentzMatrix A *ᵥ v) := by
  simp only [lowerGamma, Finset.mul_sum, Finset.sum_mul, mul_smul_comm, smul_mul_assoc,
    physical_frame_expansion A hA, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro mu hmu
  rw [← Finset.sum_smul]
  congr 1
  simp only [Matrix.mulVec, dotProduct, Complex.ofReal_sum, Complex.ofReal_mul]
  apply Finset.sum_congr rfl
  intro a ha
  exact mul_comm _ _

private theorem upperWeyl_sandwich (A : Mat2) (v : Covector) :
    upperWeyl (spin A * lowerGamma v * DiracAdjoint.diracAdjoint (spin A)) =
      A * pauli v * A.conjTranspose := by
  rw [spin_diracAdjoint]
  simp only [Matrix.adjugate_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [upperWeyl, lowerGamma, pauli, spin, weylDual, gammaLower, gamma,
      Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_succ] <;> ring

/-- For an actual determinant-one matrix, its Hermitian Pauli sandwich is exactly the physical Lorentz action already derived from the Dirac representation. -/
theorem pauli_sandwich (A : Mat2) (hA : A.det = 1) (v : Covector) :
    A * pauli v * A.conjTranspose = pauli (lorentzMatrix A *ᵥ v) := by
  rw [← upperWeyl_sandwich, ← spin_inverse A hA, lowerGamma_conjugation A hA,
    upperWeyl_lowerGamma]

end FoliationQM.SpinLorentzPauli
