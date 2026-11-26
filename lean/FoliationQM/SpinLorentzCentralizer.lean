module
public import FoliationQM.SpinLorentzPauli

/-!
# The scalar centralizer of two actual Pauli matrices

Source scope: the concrete two-sign ambiguity underlying the spin-frame
representation in v13 `prop:takabayasi` and `eq:tetrad_rotor_map`.
Commutation with the first and third standard Pauli matrices forces an
arbitrary complex two-by-two matrix to be scalar. Its actual determinant
then reduces that scalar to the two signs when the determinant is one.

This finite algebraic helper has no Lorentz-image or covering premise.
The kernel of the represented Lorentz action is established separately
by deriving these commutation relations from the actual Pauli sandwich.
-/

@[expose] public section

noncomputable section
namespace FoliationQM.SpinLorentzCentralizer
open SpinorMatrix SpinLorentzPauli

/-- Commutation with the actual first and third Pauli matrices forces a complex matrix
to be the scalar matrix determined by its first diagonal entry. -/
theorem eq_scalar_of_commute_pauli (A : Mat2)
    (h3 : Commute A (pauli (Pi.single 3 1)))
    (h1 : Commute A (pauli (Pi.single 1 1))) :
    A = (A 0 0) • (1 : Mat2) := by
  rw [pauli_three_basis] at h3
  rw [pauli_one_basis] at h1
  have h01 : A 0 1 = 0 := by
    have he := congrArg (fun B : Mat2 => B 0 1) h3.eq
    simp [Matrix.mul_apply, Fin.sum_univ_succ] at he
    linear_combination (-1/2 : ℂ) * he
  have h10 : A 1 0 = 0 := by
    have he := congrArg (fun B : Mat2 => B 1 0) h3.eq
    simp [Matrix.mul_apply, Fin.sum_univ_succ] at he
    linear_combination (1/2 : ℂ) * he
  have hd : A 0 0 = A 1 1 := by
    have he := congrArg (fun B : Mat2 => B 0 1) h1.eq
    simpa [Matrix.mul_apply, Fin.sum_univ_succ] using he
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h01, h10, hd]

/-- A determinant-one complex matrix commuting with the actual first and third
Pauli matrices is exactly one of the two scalar signs. -/
theorem eq_one_or_neg_one_of_commute_pauli (A : Mat2)
    (h3 : Commute A (pauli (Pi.single 3 1)))
    (h1 : Commute A (pauli (Pi.single 1 1)))
    (hdet : A.det = 1) : A = 1 ∨ A = -1 := by
  have hscalar := eq_scalar_of_commute_pauli A h3 h1
  have hs : A 0 0 ^ 2 = 1 := by
    have h := hdet
    rw [hscalar, Matrix.det_smul] at h
    simpa using h
  rcases sq_eq_one_iff.mp hs with h | h
  · left
    simpa [h] using hscalar
  · right
    simpa [h] using hscalar

end FoliationQM.SpinLorentzCentralizer
