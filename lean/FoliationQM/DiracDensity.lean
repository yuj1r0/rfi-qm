module

public import FoliationQM.MatrixDifferential

/-!
# Actual algebra of the symmetric Dirac jet density

Source: v13 `eq:dirac_lagrangian_sym` and the first-order calculation in
`thm:dirac_lift` (i). The symmetric Dirac density is explicit physical input,
with the source i hbar c/2 kinetic coefficient and -m c^2 scalar term. Spinor
adjoints, matrix actions and contractions are actual operations in the fixed
Dirac representation. This module takes arbitrary spinor jets as data; actual
field differentiation and polar-field substitution are separate modules.

The density is proved real, and its real part reconstructs it faithfully.
Arbitrary real amplitude additions to each jet cancel exactly. For the polar
matrix jet, the amplitude term cancels, the chiral term becomes i times the
angle coefficient times the axial bilinear, and the anti-Dirac-adjoint matrix
term becomes the gamma anticommutator. No action principle or inverse polar
reconstruction is established by these algebraic identities.
-/

@[expose] public section

noncomputable section
namespace FoliationQM.DiracDensity
open DiracMatrices DiracAdjoint MatrixDifferential Matrix

/-- The actual antisymmetrized vector bilinear for one spinor jet and gamma index. -/
def directionalPair (psi dpsi : Spinor) (mu : Fin 4) : ℂ :=
  bilinear psi (gamma mu) dpsi - bilinear dpsi (gamma mu) psi

/-- The actual symmetric Dirac jet density with the stipulated source kinetic and mass coefficients. -/
def density (hbar c m : ℝ) (psi : Spinor) (jet : Fin 4 → Spinor) : ℂ :=
  (Complex.I * (hbar : ℂ) * (c : ℂ) / 2) * ∑ mu, directionalPair psi (jet mu) mu -
    ((m : ℂ) * (c : ℂ)^2) * bilinear psi 1 psi

/-- The real part of the actual symmetric Dirac jet density. -/
def densityRe (hbar c m : ℝ) (psi : Spinor) (jet : Fin 4 → Spinor) : ℝ :=
  (density hbar c m psi jet).re

/-- The actual Dirac bilinear is the contraction of the actual spinor-adjoint row with the matrix action. -/
theorem bilinear_eq_row (psi : Spinor) (A : Mat) (chi : Spinor) :
    bilinear psi A chi = dotProduct (spinorAdjoint psi) (A.mulVec chi) := by
  unfold bilinear spinorAdjoint
  simp only [dotProduct_mulVec, vecMul_vecMul]

/-- The directional pair is the source difference of actual spinor-adjoint row contractions. -/
theorem directionalPair_eq_row (psi dpsi : Spinor) (mu : Fin 4) :
    directionalPair psi dpsi mu =
      dotProduct (spinorAdjoint psi) ((gamma mu).mulVec dpsi) -
      dotProduct (spinorAdjoint dpsi) ((gamma mu).mulVec psi) := by
  simp only [directionalPair, bilinear_eq_row]

/-- The actual jet density has the source row-spinor kinetic expression and actual scalar mass contraction. -/
theorem density_eq_row (hbar c m : ℝ) (psi : Spinor) (jet : Fin 4 → Spinor) :
    density hbar c m psi jet =
      (Complex.I * (hbar : ℂ) * (c : ℂ) / 2) *
        ∑ mu, (dotProduct (spinorAdjoint psi) ((gamma mu).mulVec (jet mu)) -
          dotProduct (spinorAdjoint (jet mu)) ((gamma mu).mulVec psi)) -
      ((m : ℂ) * (c : ℂ)^2) * dotProduct (spinorAdjoint psi) psi := by
  simp only [density, directionalPair_eq_row, bilinear_eq_row, one_mulVec]

/-- The actual antisymmetrized directional pair is purely imaginary under complex conjugation. -/
theorem star_directionalPair (psi dpsi : Spinor) (mu : Fin 4) :
    star (directionalPair psi dpsi mu) = -directionalPair psi dpsi mu := by
  simp only [directionalPair, star_sub, star_bilinear, diracAdjoint_gamma]
  ring

/-- The actual symmetric Dirac jet density is fixed by complex conjugation for arbitrary spinor jets. -/
theorem density_star (hbar c m : ℝ) (psi : Spinor) (jet : Fin 4 → Spinor) :
    star (density hbar c m psi jet) = density hbar c m psi jet := by
  simp only [density, star_sub, star_mul, star_div₀, star_pow, star_sum,
    star_directionalPair, star_bilinear, diracAdjoint_one,
    Complex.star_def, Complex.conj_ofReal, Complex.conj_I, map_ofNat,
    Finset.sum_neg_distrib]
  ring

/-- The actual symmetric Dirac jet density has zero imaginary part. -/
theorem density_im_eq_zero (hbar c m : ℝ) (psi : Spinor) (jet : Fin 4 → Spinor) :
    (density hbar c m psi jet).im = 0 :=
  Complex.conj_eq_iff_im.mp (density_star hbar c m psi jet)

/-- The actual symmetric Dirac jet density is faithfully reconstructed from its real part. -/
theorem density_eq_ofReal (hbar c m : ℝ) (psi : Spinor) (jet : Fin 4 → Spinor) :
    density hbar c m psi jet = (densityRe hbar c m psi jet : ℂ) := by
  apply Complex.ext
  · rfl
  · simpa only [Complex.ofReal_im] using density_im_eq_zero hbar c m psi jet

private theorem bilinear_add_left (psi chi zeta : Spinor) (A : Mat) :
    bilinear (psi + chi) A zeta = bilinear psi A zeta + bilinear chi A zeta := by
  simp [bilinear, add_dotProduct]

private theorem bilinear_add_right (psi chi zeta : Spinor) (A : Mat) :
    bilinear psi A (chi + zeta) = bilinear psi A chi + bilinear psi A zeta := by
  simp [bilinear, Matrix.mulVec_add, dotProduct_add]

private theorem bilinear_real_smul_left (a : ℝ) (psi chi : Spinor) (A : Mat) :
    bilinear (a • psi) A chi = (a : ℂ) * bilinear psi A chi := by
  rw [← IsScalarTower.algebraMap_smul ℂ a psi, bilinear_smul_left]
  simp

private theorem bilinear_real_smul_right (a : ℝ) (psi chi : Spinor) (A : Mat) :
    bilinear psi A (a • chi) = (a : ℂ) * bilinear psi A chi := by
  rw [← IsScalarTower.algebraMap_smul ℂ a chi, bilinear_smul_right]
  rfl

/-- Adding any real multiple of the spinor to one actual jet leaves its antisymmetrized directional pair unchanged. -/
theorem directionalPair_add_real_smul (psi dpsi : Spinor) (mu : Fin 4) (a : ℝ) :
    directionalPair psi (dpsi + a • psi) mu = directionalPair psi dpsi mu := by
  simp only [directionalPair, bilinear_add_right, bilinear_add_left,
    bilinear_real_smul_left, bilinear_real_smul_right]
  ring

/-- Independent real amplitude additions in all four jet directions cancel exactly from the actual Dirac density. -/
theorem density_add_real_amplitude (hbar c m : ℝ) (psi : Spinor)
    (jet : Fin 4 → Spinor) (a : Fin 4 → ℝ) :
    density hbar c m psi (fun mu => jet mu + (a mu) • psi) = density hbar c m psi jet := by
  simp only [density, directionalPair_add_real_smul]

private theorem bilinear_sub_matrix (psi chi : Spinor) (A B : Mat) :
    bilinear psi (A-B) chi = bilinear psi A chi - bilinear psi B chi := by
  simp only [sub_eq_add_neg, bilinear_add_matrix, bilinear_neg_matrix]

private theorem adjoint_polar_matrix (a b : ℝ) (K : Mat) (hK : diracAdjoint K = -K) :
    diracAdjoint ((a : ℂ) • (1 : Mat) + (Complex.I * (b : ℂ) / 2) • gamma5 + K) =
      (a : ℂ) • (1 : Mat) + (Complex.I * (b : ℂ) / 2) • gamma5 - K := by
  simp only [diracAdjoint_add, diracAdjoint_smul, diracAdjoint_one,
    diracAdjoint_gamma5, hK, star_div₀, star_mul, Complex.star_def, Complex.conj_ofReal,
    Complex.conj_I, map_ofNat, smul_neg, sub_eq_add_neg]
  module

/-- The actual polar matrix jet cancels its real amplitude term and gives the chiral axial term plus the gamma-connection anticommutator. -/
theorem directionalPair_polar_matrix (psi : Spinor) (mu : Fin 4) (a b : ℝ)
    (K : Mat) (hK : diracAdjoint K = -K) :
    directionalPair psi
      ((((a : ℂ) • (1 : Mat)) + (Complex.I * (b : ℂ) / 2) • gamma5 + K).mulVec psi) mu =
      Complex.I * (b : ℂ) * bilinear psi (gamma mu * gamma5) psi +
        bilinear psi (gamma mu * K + K * gamma mu) psi := by
  let P : Mat := (a : ℂ) • (1 : Mat) + (Complex.I * (b : ℂ) / 2) • gamma5 + K
  have hm : gamma mu * P - diracAdjoint P * gamma mu =
      (Complex.I * (b : ℂ)) • (gamma mu * gamma5) + (gamma mu * K + K * gamma mu) := by
    dsimp only [P]
    rw [adjoint_polar_matrix a b K hK]
    simp only [mul_add, add_mul, sub_mul, smul_mul_assoc, mul_smul_comm,
      mul_one, one_mul, gamma5_anticomm, smul_neg]
    module
  change bilinear psi (gamma mu) (P.mulVec psi) - bilinear (P.mulVec psi) (gamma mu) psi = _
  rw [← bilinear_mul_matrix, bilinear_mulVec_left, ← bilinear_sub_matrix, hm,
    bilinear_add_matrix, bilinear_smul_matrix]

end FoliationQM.DiracDensity
