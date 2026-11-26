module
public import FoliationQM.DiracDensity

/-!
# Polarization of the symmetric Dirac density

For v13 `eq:dirac_lagrangian_sym` and the action in `thm:dirac_lift`,
the polarized density uses both the field value and its four first jets
in each argument. Its diagonal recovers the given symmetric Dirac density.
A real variation of all five spinors has an exact quadratic expansion,
with its linear term determined by the polarized contraction.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.DiracPolarizedDensity
open DiracMatrices DiracAdjoint DiracDensity Matrix

/-- The polarized kinetic and mass contractions of two independent first jets. -/
def mixed (hbar c m : ℝ) (u : Spinor) (du : Fin 4 → Spinor)
    (v : Spinor) (dv : Fin 4 → Spinor) : ℂ :=
  (Complex.I * (hbar : ℂ) * (c : ℂ) / 2) *
      ∑ μ, (bilinear u (gamma μ) (dv μ) - bilinear (du μ) (gamma μ) v) -
    ((m : ℂ) * (c : ℂ) ^ 2) * bilinear u 1 v

variable (hbar c m : ℝ)

/-- Evaluating the two-argument expression on one jet gives the original density. -/
theorem mixed_diag (u : Spinor) (du : Fin 4 → Spinor) :
    mixed hbar c m u du u du = density hbar c m u du := rfl

/-- The imaginary kinetic coefficient and its antisymmetrized pair terms make the
polarized density Hermitian for arbitrary independent jets. -/
theorem star_mixed (u : Spinor) (du : Fin 4 → Spinor) (v : Spinor) (dv : Fin 4 → Spinor) :
    star (mixed hbar c m u du v dv) = mixed hbar c m v dv u du := by
  simp only [mixed, star_sub, star_mul, star_div₀, star_pow, star_sum, star_bilinear,
    diracAdjoint_gamma, diracAdjoint_one, Complex.star_def, Complex.conj_ofReal,
    Complex.conj_I, map_ofNat, Finset.sum_sub_distrib]
  ring

/-- Interchanging the two full jets preserves the real part of the polarized density. -/
theorem mixed_re_swap (u : Spinor) (du : Fin 4 → Spinor) (v : Spinor) (dv : Fin 4 → Spinor) :
    (mixed hbar c m u du v dv).re = (mixed hbar c m v dv u du).re := by
  simpa only [Complex.star_def, Complex.conj_re] using
    congrArg Complex.re (star_mixed hbar c m u du v dv)

private theorem bilinear_add_right (u v w : Spinor) (A : Mat) :
    bilinear u A (v + w) = bilinear u A v + bilinear u A w := by
  simp [bilinear, Matrix.mulVec_add, dotProduct_add]

private theorem bilinear_real_smul_right (t : ℝ) (u v : Spinor) (A : Mat) :
    bilinear u A (t • v) = (t : ℂ) * bilinear u A v := by
  rw [← IsScalarTower.algebraMap_smul ℂ t v, bilinear_smul_right]
  rfl

/-- Adding two full jets in the second argument adds their polarized contractions. -/
theorem mixed_add_right (u : Spinor) (du : Fin 4 → Spinor)
    (v : Spinor) (dv : Fin 4 → Spinor) (w : Spinor) (dw : Fin 4 → Spinor) :
    mixed hbar c m u du (v + w) (dv + dw) =
      mixed hbar c m u du v dv + mixed hbar c m u du w dw := by
  simp only [mixed, Pi.add_apply, bilinear_add_right, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  ring

/-- Adding two full jets in the first argument adds their polarized contractions. -/
theorem mixed_add_left (u : Spinor) (du : Fin 4 → Spinor)
    (v : Spinor) (dv : Fin 4 → Spinor) (w : Spinor) (dw : Fin 4 → Spinor) :
    mixed hbar c m (u + v) (du + dv) w dw =
      mixed hbar c m u du w dw + mixed hbar c m v dv w dw := by
  rw [← star_mixed hbar c m w dw (u + v) (du + dv), mixed_add_right, star_add,
    star_mixed, star_mixed]

/-- A real multiple of the second jet scales the density by that real number. -/
theorem mixed_smul_right (t : ℝ) (u : Spinor) (du : Fin 4 → Spinor)
    (v : Spinor) (dv : Fin 4 → Spinor) :
    mixed hbar c m u du (t • v) (t • dv) = (t : ℂ) * mixed hbar c m u du v dv := by
  simp only [mixed, Pi.smul_apply, bilinear_real_smul_right, ← mul_sub, ← Finset.mul_sum]
  ring

/-- A real multiple of the first jet scales the density by that real number. -/
theorem mixed_smul_left (t : ℝ) (u : Spinor) (du : Fin 4 → Spinor)
    (v : Spinor) (dv : Fin 4 → Spinor) :
    mixed hbar c m (t • u) (t • du) v dv = (t : ℂ) * mixed hbar c m u du v dv := by
  rw [← star_mixed hbar c m v dv (t • u) (t • du), mixed_smul_right, star_mul, star_mixed]
  simp only [Complex.star_def, Complex.conj_ofReal, mul_comm]

/-- Exact quadratic variation of the real Dirac density along a full affine jet. -/
theorem densityRe_affine (t : ℝ) (psi : Spinor) (j : Fin 4 → Spinor)
    (eta : Spinor) (d : Fin 4 → Spinor) :
    densityRe hbar c m (psi + t • eta) (j + t • d) =
      densityRe hbar c m psi j + t * (2 * (mixed hbar c m eta d psi j).re) +
        t ^ 2 * densityRe hbar c m eta d := by
  simp only [densityRe, ← mixed_diag, mixed_add_left, mixed_add_right, mixed_smul_left,
    mixed_smul_right, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero]
  rw [mixed_re_swap hbar c m psi j eta d]
  ring

end FoliationQM.DiracPolarizedDensity
