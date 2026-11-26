module
public import FoliationQM.SpinLorentzPauli

/-!
# An explicit special linear lift of every future unit time vector

Source scope: the concrete Lorentz-frame action of v13 `prop:takabayasi`
and `eq:tetrad_rotor_map`. For an actual future unit Minkowski vector u,
the displayed matrix (H(u)+1)/sqrt(2(u0+1)) is constructed directly in
the standard Hermitian Pauli model. Its positive real denominator,
determinant one, Hermiticity, and exact Hermitian square are proved by
finite algebra and the supplied unit-vector equation.

The existing genuine Pauli sandwich then proves that this actual
special linear matrix carries the time basis vector to u under the
previously constructed physical Lorentz action. No lift, transformation,
or square identity is supplied as a premise. This is the time-axis part
of a constructive lift; the full Lorentz image, covering, and abstract
Clifford identification are separate results.
-/

@[expose] public section
noncomputable section
open scoped Matrix Matrix.Norms.Operator
namespace FoliationQM.SpinLorentzBoost
open SpinorMatrix SpinLorentzPauli SpinLorentzAction SourcePolarDatum

/-- The explicit Hermitian boost candidate, with the actual positive-root denominator on the future unit domain. -/
def boostMatrix (u : Covector) : Mat2 :=
  (Real.sqrt (2*(u 0+1)) : ℂ)⁻¹ • (pauli u + 1)

/-- The numerator determinant is an exact polynomial in the actual Minkowski square and temporal coordinate. -/
theorem pauli_add_one_det (u : Covector) :
    (pauli u + 1).det = (minkowski u u + 2*u 0 + 1 : ℝ) := by
  apply Complex.ext <;>
    simp [pauli, Matrix.det_fin_two, minkowski, Complex.mul_re, Complex.mul_im] <;> ring

/-- The numerator satisfies the exact two-by-two quadratic identity before imposing unit Minkowski norm. -/
theorem pauli_add_one_square (u : Covector) :
    (pauli u + 1)*(pauli u + 1) =
      (2*(u 0+1) : ℂ) • pauli u + ((1-minkowski u u : ℝ) : ℂ) • (1 : Mat2) := by
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    norm_num [pauli, Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_succ, minkowski,
      Complex.mul_re, Complex.mul_im] <;> ring

/-- A positive temporal coordinate makes the actual square-root denominator strictly positive. -/
theorem denominator_pos (u : Covector) (hu0 : 0 < u 0) :
    0 < Real.sqrt (2*(u 0+1)) := by
  apply Real.sqrt_pos.2
  positivity

/-- The actual positive-root denominator has its specified squared value on the future domain. -/
theorem denominator_sq (u : Covector) (hu0 : 0 < u 0) :
    (Real.sqrt (2*(u 0+1)))^2 = 2*(u 0+1) := by
  apply Real.sq_sqrt
  positivity

/-- The explicit boost candidate is Hermitian for every real vector input. -/
theorem boostMatrix_conjTranspose (u : Covector) :
    (boostMatrix u).conjTranspose = boostMatrix u := by
  simp [boostMatrix, Matrix.conjTranspose_smul, pauli_conjTranspose]

/-- The explicit boost matrix has determinant one for every future unit Minkowski vector. -/
theorem boostMatrix_det (u : Covector) (hu0 : 0 < u 0)
    (hu : minkowski u u = 1) : (boostMatrix u).det = 1 := by
  have hd : (Real.sqrt (2*(u 0+1)) : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (denominator_pos u hu0))
  have hs : (Real.sqrt (2*(u 0+1)) : ℂ)^2 = (2*(u 0+1) : ℂ) := by
    exact_mod_cast denominator_sq u hu0
  rw [boostMatrix, Matrix.det_smul, pauli_add_one_det, hu]
  norm_num only [Fintype.card_fin, Complex.ofReal_add, Complex.ofReal_mul,
    Complex.ofReal_one, Complex.ofReal_ofNat]
  have he : (1 : ℂ) + 2 * (u 0 : ℂ) + 1 = (2*(u 0+1) : ℂ) := by ring
  rw [he, ← hs]
  field_simp

/-- The actual boost times its conjugate transpose is exactly the Pauli matrix of the future unit vector. -/
theorem boostMatrix_mul_conjTranspose (u : Covector) (hu0 : 0 < u 0)
    (hu : minkowski u u = 1) : boostMatrix u * (boostMatrix u).conjTranspose = pauli u := by
  have hd : (Real.sqrt (2*(u 0+1)) : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (denominator_pos u hu0))
  have hs : (Real.sqrt (2*(u 0+1)) : ℂ)^2 = (2*(u 0+1) : ℂ) := by
    exact_mod_cast denominator_sq u hu0
  rw [boostMatrix_conjTranspose, boostMatrix, smul_mul_smul_comm,
    pauli_add_one_square, hu]
  simp only [sub_self, Complex.ofReal_zero, zero_smul, add_zero, smul_smul]
  have hc : (Real.sqrt (2*(u 0+1)) : ℂ)⁻¹ *
      (Real.sqrt (2*(u 0+1)) : ℂ)⁻¹ * (2*(u 0+1) : ℂ) = 1 := by
    rw [← hs]
    field_simp
  rw [hc, one_smul]

/-- The actual physical Lorentz action of the constructed boost sends the time basis vector to the supplied future unit vector. -/
theorem boost_time_image (u : Covector) (hu0 : 0 < u 0)
    (hu : minkowski u u = 1) :
    lorentzMatrix (boostMatrix u) *ᵥ Pi.single 0 1 = u := by
  apply pauli_injective
  rw [← pauli_sandwich (boostMatrix u) (boostMatrix_det u hu0 hu), pauli_zero_basis,
    mul_one, boostMatrix_mul_conjTranspose u hu0 hu]

/-- The explicit boost bundled as an actual determinant-one complex matrix. -/
def boost (u : Covector) (hu0 : 0 < u 0) (hu : minkowski u u = 1) :
    SpecialLinearMatrix := ⟨boostMatrix u, boostMatrix_det u hu0 hu⟩

/-- The bundled special linear lift retains exactly the displayed boost formula. -/
theorem boost_val (u : Covector) (hu0 : 0 < u 0) (hu : minkowski u u = 1) :
    (boost u hu0 hu).val = boostMatrix u := rfl

/-- Every actual future unit Minkowski vector has a constructed special linear representative with precisely that temporal column. -/
theorem exists_boost_lift (u : Covector) (hu0 : 0 < u 0)
    (hu : minkowski u u = 1) :
    ∃ A : SpecialLinearMatrix, lorentzMatrix A.val *ᵥ Pi.single 0 1 = u :=
  ⟨boost u hu0 hu, boost_time_image u hu0 hu⟩

end FoliationQM.SpinLorentzBoost
