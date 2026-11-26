module
public import FoliationQM.SpinLorentzPauli
/-!
# Explicit special-unitary lifts of spatial unit vectors

Source scope: the concrete proper Lorentz-frame representation in v13
`prop:takabayasi` and `eq:tetrad_rotor_map`. This module constructs an actual
determinant-one complex matrix carrying the third spatial basis vector to any
purely spatial Minkowski unit vector. Away from the south pole it uses the
positive square root of `(1+w₃)/2` and actual real quotients for the two
remaining parameters. The south pole has a separate explicit matrix.

Determinant, conjugate-transpose unitarity, and the Pauli sandwich are finite
matrix identities. The already proved actual Pauli transformation transfers
these identities to the physical Lorentz action, including the fixed time
basis vector. No supplied rotation matrix, spin lift, or final image equality
is assumed. This spatial construction alone does not assert full Lorentz
surjectivity, a covering, or an abstract Clifford spin-group identification.
-/

@[expose] public section
noncomputable section
open scoped Matrix Matrix.Norms.Operator
namespace FoliationQM.SpinLorentzSphere
open SpinorMatrix SourcePolarDatum SpinLorentzAction SpinLorentzPauli

/-- The explicit real-parameter special-unitary matrix used for the spatial lift. -/
def sphereMatrix (a x y : ℝ) : Mat2 :=
  !![(a : ℂ), -(x : ℂ) + Complex.I * y;
    (x : ℂ) + Complex.I * y, (a : ℂ)]

/-- Its actual determinant is the sum of the three parameter squares. -/
theorem sphereMatrix_det (a x y : ℝ) :
    (sphereMatrix a x y).det = ((a ^ 2 + x ^ 2 + y ^ 2 : ℝ) : ℂ) := by
  apply Complex.ext <;>
    simp [sphereMatrix, Matrix.det_fin_two, Complex.mul_re, Complex.mul_im, pow_two] <;> ring

/-- Its product with the actual conjugate transpose is the squared parameter norm times identity. -/
theorem sphereMatrix_unitary_product (a x y : ℝ) :
    sphereMatrix a x y * (sphereMatrix a x y).conjTranspose =
      ((a ^ 2 + x ^ 2 + y ^ 2 : ℝ) : ℂ) • (1 : Mat2) := by
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    simp [sphereMatrix, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fin.sum_univ_succ, Complex.mul_re, Complex.mul_im, pow_two] <;> ring

/-- The third Pauli sandwich has the exact spatial coordinates determined by the real parameters. -/
theorem sphereMatrix_pauli_three (a x y : ℝ) :
    sphereMatrix a x y * pauli (Pi.single 3 1) * (sphereMatrix a x y).conjTranspose =
      pauli ![0, 2*a*x, 2*a*y, a^2-x^2-y^2] := by
  rw [pauli_three_basis]
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    simp [sphereMatrix, pauli, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fin.sum_univ_succ, Complex.mul_re, Complex.mul_im, pow_two] <;> ring

/-- Every actual unitary determinant-one spin matrix fixes the time basis vector in its physical Lorentz action. -/
theorem time_fixed_of_unitary (A : Mat2) (hdet : A.det = 1)
    (hunit : A * A.conjTranspose = 1) :
    lorentzMatrix A *ᵥ Pi.single 0 1 = Pi.single 0 1 := by
  apply pauli_injective
  rw [← pauli_sandwich A hdet, pauli_zero_basis, mul_one, hunit]


/-- A purely spatial Minkowski unit vector has Euclidean spatial norm one. -/
theorem spatial_norm_one (w : Covector) (h0 : w 0 = 0) (hunit : minkowski w w = -1) :
    (w 1)^2 + (w 2)^2 + (w 3)^2 = 1 := by
  simp only [minkowski, h0, zero_mul, zero_sub] at hunit
  nlinarith

/-- The third component of a purely spatial Minkowski unit vector lies between the two poles. -/
theorem spatial_third_bounds (w : Covector) (h0 : w 0 = 0) (hunit : minkowski w w = -1) :
    -1 ≤ w 3 ∧ w 3 ≤ 1 := by
  have hs := spatial_norm_one w h0 hunit
  constructor <;> nlinarith [sq_nonneg (w 1), sq_nonneg (w 2)]

private theorem north_parameters (r s t : ℝ) (h : r^2+s^2+t^2=1) (ht : -1<t) :
    let a := Real.sqrt ((1+t)/2)
    let x := r/(2*a)
    let y := s/(2*a)
    a^2+x^2+y^2=1 ∧ 2*a*x=r ∧ 2*a*y=s ∧ a^2-x^2-y^2=t := by
  dsimp only
  let a := Real.sqrt ((1+t)/2)
  have ha : 0 < a := Real.sqrt_pos.mpr (by linarith)
  have ha2 : a^2 = (1+t)/2 := Real.sq_sqrt (by linarith)
  have hd : 2*a≠0 := ne_of_gt (mul_pos (by norm_num) ha)
  have hx : 2*a*(r/(2*a))=r := mul_div_cancel₀ _ hd
  have hy : 2*a*(s/(2*a))=s := mul_div_cancel₀ _ hd
  have hxy : (r/(2*a))^2+(s/(2*a))^2=(1-t)/2 := by
    apply (mul_left_cancel₀ (pow_ne_zero 2 hd))
    have hx2 := congrArg (fun q : ℝ => q^2) hx
    have hy2 := congrArg (fun q : ℝ => q^2) hy
    simp only [mul_pow] at hx2 hy2
    rw [mul_add, mul_pow, hx2, hy2, ha2]
    nlinarith
  exact ⟨by nlinarith, hx, hy, by nlinarith⟩

/-- The explicit northern lift, using positive square root and two actual real quotients. -/
def northMatrix (w : Covector) : Mat2 :=
  let a := Real.sqrt ((1 + w 3) / 2)
  sphereMatrix a (w 1 / (2*a)) (w 2 / (2*a))

/-- Away from the south pole the actual northern formula has determinant one, is unitary, and carries the third spatial basis vector to the specified vector. -/
theorem northMatrix_properties (w : Covector) (h0 : w 0 = 0)
    (hunit : minkowski w w = -1) (hnorth : w 3 ≠ -1) :
    (northMatrix w).det = 1 ∧ northMatrix w * (northMatrix w).conjTranspose = 1 ∧
      lorentzMatrix (northMatrix w) *ᵥ Pi.single 3 1 = w := by
  have ht : -1 < w 3 := lt_of_le_of_ne (spatial_third_bounds w h0 hunit).1 hnorth.symm
  obtain ⟨hn, hx, hy, hz⟩ := north_parameters (w 1) (w 2) (w 3)
    (spatial_norm_one w h0 hunit) ht
  have hd : (northMatrix w).det = 1 := by
    rw [northMatrix, sphereMatrix_det, hn]
    rfl
  have hu : northMatrix w * (northMatrix w).conjTranspose = 1 := by
    rw [northMatrix, sphereMatrix_unitary_product, hn]
    simp
  refine ⟨hd, hu, ?_⟩
  apply pauli_injective
  rw [← pauli_sandwich (northMatrix w) hd, northMatrix, sphereMatrix_pauli_three]
  congr 1
  ext i
  fin_cases i
  · exact h0.symm
  · exact hx
  · exact hy
  · exact hz

/-- The fixed southern lift is an explicit real matrix. -/
def southMatrix : Mat2 := sphereMatrix 0 1 0

/-- The southern formula is literally the real matrix with entries zero, minus one, one, zero. -/
theorem southMatrix_explicit : southMatrix = !![0,-1;1,0] := by
  simp [southMatrix, sphereMatrix]

/-- The actual southern matrix is special unitary and sends the third spatial basis vector to the south pole. -/
theorem southMatrix_properties :
    southMatrix.det = 1 ∧ southMatrix * southMatrix.conjTranspose = 1 ∧
      lorentzMatrix southMatrix *ᵥ Pi.single 3 1 = ![0,0,0,-1] := by
  have hd : southMatrix.det = 1 := by
    rw [southMatrix, sphereMatrix_det]
    norm_num
  have hu : southMatrix * southMatrix.conjTranspose = 1 := by
    rw [southMatrix, sphereMatrix_unitary_product]
    norm_num
  refine ⟨hd, hu, ?_⟩
  apply pauli_injective
  rw [← pauli_sandwich southMatrix hd, southMatrix, sphereMatrix_pauli_three]
  norm_num

/-- Every purely spatial Minkowski unit vector has an actual special linear lift that is unitary, fixes time, and carries the third spatial basis vector to it. -/
theorem exists_spatial_lift (w : Covector) (h0 : w 0 = 0) (hunit : minkowski w w = -1) :
    ∃ A : SpecialLinearMatrix,
      A.val * A.val.conjTranspose = 1 ∧
      lorentzMatrix A.val *ᵥ Pi.single 0 1 = Pi.single 0 1 ∧
      lorentzMatrix A.val *ᵥ Pi.single 3 1 = w := by
  by_cases hp : w 3 = -1
  · have hs := spatial_norm_one w h0 hunit
    have h1 : w 1 = 0 := by nlinarith [sq_nonneg (w 2)]
    have h2 : w 2 = 0 := by nlinarith [sq_nonneg (w 1)]
    have hw : w = ![0,0,0,-1] := by
      ext i
      fin_cases i <;> simp [h0, h1, h2, hp]
    obtain ⟨hd, hu, he⟩ := southMatrix_properties
    exact ⟨⟨southMatrix, hd⟩, hu, time_fixed_of_unitary southMatrix hd hu, he.trans hw.symm⟩
  · obtain ⟨hd, hu, he⟩ := northMatrix_properties w h0 hunit hp
    exact ⟨⟨northMatrix w, hd⟩, hu, time_fixed_of_unitary (northMatrix w) hd hu, he⟩

end FoliationQM.SpinLorentzSphere
