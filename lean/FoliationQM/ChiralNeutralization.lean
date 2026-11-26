module
public import FoliationQM.PolarConnectionContraction

/-!
# Actual chiral neutralization and the complex polar jet square

Source: v13 `eq:spinor_quadratic_exact` and its proof. The neutralizing matrix
is identified with the genuine matrix exponential exp(-i beta gamma5).
The full complex bilinear, with the actual Dirac adjoint of the left spinor,
is evaluated on the forward polar ansatz. For a jet a I + i b gamma5 + K,
b is the half-angle derivative coefficient. The real amplitude and chiral
coefficients leave rho (a squared minus b squared), and the commuting
anti-Dirac-adjoint connection contributes its negative neutralized square.

The transported-generator specialization reduces that square to an actual
rest-spinor matrix product. It does not assume a derivative formula, a
connection contraction, or any kinetic equation, and it does not assert
existence of a polar reconstruction for arbitrary spinors.
-/

@[expose] public section
noncomputable section
open scoped Matrix.Norms.Operator
namespace FoliationQM.ChiralNeutralization
open DiracMatrices DiracAdjoint ChiralMatrix PolarSpinorBilinears
open MaurerCartanDifferential CliffordCommutators PolarConnectionContraction

/-- The actual inverse chiral factor neutralizing two full-angle polar factors. -/
def neutralizer (beta : ℝ) : Mat := chiral (-2 * beta)

/-- The neutralizer is the genuine normed-algebra exponential of minus i beta gamma5. -/
theorem neutralizer_eq_exp (beta : ℝ) :
    neutralizer beta = NormedSpace.exp ((-Complex.I * (beta : ℂ)) • gamma5) := by
  rw [neutralizer, ← exp_chiral]
  congr 2
  push_cast
  ring

/-- The neutralizer cancels the two actual polar chiral factors. -/
theorem chiral_neutralizer_chiral (beta : ℝ) :
    chiral beta * neutralizer beta * chiral beta = 1 := by
  rw [neutralizer, ← chiral_add, ← chiral_add]
  rw [show beta + -2 * beta + beta = 0 by ring, chiral_zero]

/-- Every gamma5-commuting matrix commutes with the actual chiral matrix. -/
theorem commute_chiral {M : Mat} (hM : Commute M gamma5) (beta : ℝ) :
    Commute M (chiral beta) := by
  change M * chiral beta = chiral beta * M
  simp only [chiral, mul_add, add_mul, mul_smul_comm, smul_mul_assoc, mul_one, one_mul, hM.eq]

/-- Every gamma5-commuting matrix commutes with the actual neutralizer. -/
theorem commute_neutralizer {M : Mat} (hM : Commute M gamma5) (beta : ℝ) :
    Commute M (neutralizer beta) := commute_chiral hM (-2 * beta)

/-- The actual neutralizer commutes with gamma5. -/
theorem neutralizer_gamma5_commute (beta : ℝ) : Commute (neutralizer beta) gamma5 :=
  chiral_gamma5_commute (-2 * beta)

/-- The actual Dirac adjoint fixes the neutralizer. -/
theorem neutralizer_diracAdjoint (beta : ℝ) : diracAdjoint (neutralizer beta) = neutralizer beta :=
  chiral_diracAdjoint (-2 * beta)

/-- A gamma5-commuting insertion survives the neutralized chiral sandwich unchanged. -/
theorem neutralized_chiral_sandwich (beta : ℝ) (M : Mat) (hM : Commute M gamma5) :
    chiral beta * (neutralizer beta * M) * chiral beta = M := by
  calc
    _ = (chiral beta * neutralizer beta) * (M * chiral beta) := by simp only [mul_assoc]
    _ = (chiral beta * neutralizer beta) * (chiral beta * M) := by rw [(commute_chiral hM beta).eq]
    _ = _ := by rw [← mul_assoc, chiral_neutralizer_chiral, one_mul]

/-- Neutralization removes the chiral sandwich from every gamma5-commuting polar bilinear. -/
theorem neutralized_polar_even (rho beta : ℝ) (L M : Mat) (hrho : 0 ≤ rho)
    (hM : Commute M gamma5) :
    bilinear (polarSpinor rho beta L) (neutralizer beta * M) (polarSpinor rho beta L) =
      (rho : ℂ) * bilinear restSpinor (diracAdjoint L * M * L) restSpinor := by
  rw [polar_bilinear rho beta L _ hrho, neutralized_chiral_sandwich beta M hM]

/-- The neutralized scalar bilinear is exactly the nonnegative polar density. -/
theorem neutralized_polar_scalar (rho beta : ℝ) (L : Mat) (hrho : 0 ≤ rho)
    (hiso : diracAdjoint L * L = 1) :
    bilinear (polarSpinor rho beta L) (neutralizer beta) (polarSpinor rho beta L) = (rho : ℂ) := by
  simpa only [mul_one, hiso, rest_scalar] using
    neutralized_polar_even rho beta L 1 hrho (Commute.one_left gamma5)

/-- The neutralized gamma5 bilinear vanishes for the forward polar rest-spinor ansatz. -/
theorem neutralized_polar_gamma5 (rho beta : ℝ) (L : Mat) (hrho : 0 ≤ rho)
    (hiso : diracAdjoint L * L = 1) (h5 : Commute L gamma5) :
    bilinear (polarSpinor rho beta L) (neutralizer beta * gamma5) (polarSpinor rho beta L) = 0 := by
  rw [neutralized_polar_even rho beta L gamma5 hrho (Commute.refl gamma5),
    diracAdjoint_mul_gamma5_mul L hiso h5, rest_pseudoscalar, mul_zero]

/-- A transported even insertion has its actual neutralized polar bilinear equal to the density times its rest bilinear. -/
theorem neutralized_polar_matrix (rho beta : ℝ) (L M : Mat) (hrho : 0 ≤ rho)
    (hunit : IsUnit L) (hiso : diracAdjoint L * L = 1) (h5 : Commute L gamma5)
    (hM : Commute M gamma5) :
    bilinear (polarSpinor rho beta L) (neutralizer beta * (L * M * L⁻¹))
      (polarSpinor rho beta L) = (rho : ℂ) * bilinear restSpinor M restSpinor := by
  have hi := Matrix.nonsing_inv_mul L ((Matrix.isUnit_iff_isUnit_det _).mp hunit)
  rw [neutralized_polar_even rho beta L _ hrho
    ((h5.mul_left hM).mul_left (inverse_commute hunit h5))]
  congr 2
  simp only [← mul_assoc, hiso, one_mul]
  rw [mul_assoc, hi, mul_one]

private theorem adjoint_jet (a b : ℝ) (K : Mat) (hK : diracAdjoint K = -K) :
    diracAdjoint ((a : ℂ) • (1 : Mat) + (Complex.I * (b : ℂ)) • gamma5 + K) =
      (a : ℂ) • (1 : Mat) + (Complex.I * (b : ℂ)) • gamma5 - K := by
  simp only [diracAdjoint_add, diracAdjoint_smul, diracAdjoint_one,
    diracAdjoint_gamma5, hK, star_mul, Complex.star_def, Complex.conj_ofReal,
    Complex.conj_I, smul_neg, sub_eq_add_neg]
  module

private theorem jet_product (a b : ℝ) (K : Mat) (hK : Commute K gamma5) :
    ((a : ℂ) • (1 : Mat) + (Complex.I * (b : ℂ)) • gamma5 - K) *
      ((a : ℂ) • (1 : Mat) + (Complex.I * (b : ℂ)) • gamma5 + K) =
      ((a : ℂ)^2 - (b : ℂ)^2) • (1 : Mat) +
        (2 * Complex.I * (a : ℂ) * (b : ℂ)) • gamma5 - K*K := by
  simp only [add_mul, mul_add, sub_mul, smul_mul_assoc, mul_smul_comm,
    one_mul, mul_one, gamma5_sq, hK.eq]
  match_scalars <;> ring_nf
  norm_num
  ring

private theorem bilinear_sub_matrix (psi chi : Spinor) (A B : Mat) :
    bilinear psi (A-B) chi = bilinear psi A chi - bilinear psi B chi := by
  simp only [sub_eq_add_neg, bilinear_add_matrix, bilinear_neg_matrix]

/-- The full complex neutralized polar jet square cancels the amplitude-connection and chiral-connection cross terms; b is the half-angle derivative coefficient. -/
theorem polar_jet_square (rho beta a b : ℝ) (L K : Mat) (hrho : 0 ≤ rho)
    (hiso : diracAdjoint L * L = 1) (h5 : Commute L gamma5)
    (hK : diracAdjoint K = -K) (hK5 : Commute K gamma5) :
    bilinear
      ((((a : ℂ) • (1 : Mat)) + (Complex.I * (b : ℂ)) • gamma5 + K).mulVec (polarSpinor rho beta L))
      (neutralizer beta)
      ((((a : ℂ) • (1 : Mat)) + (Complex.I * (b : ℂ)) • gamma5 + K).mulVec (polarSpinor rho beta L)) =
      (rho : ℂ) * ((a : ℂ)^2 - (b : ℂ)^2) -
        bilinear (polarSpinor rho beta L) (neutralizer beta * (K*K)) (polarSpinor rho beta L) := by
  rw [bilinear_mulVec_both, adjoint_jet a b K hK]
  have hcomm : Commute
      ((a : ℂ) • (1 : Mat) + (Complex.I * (b : ℂ)) • gamma5 - K) (neutralizer beta) := by
    apply commute_neutralizer
    change _ * gamma5 = gamma5 * _
    simp only [add_mul, mul_add, sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm,
      one_mul, mul_one, hK5.eq]
  rw [hcomm.eq, mul_assoc, jet_product a b K hK5]
  simp only [mul_sub, mul_add, mul_smul_comm, mul_one, bilinear_sub_matrix,
    bilinear_add_matrix, bilinear_smul_matrix,
    neutralized_polar_scalar rho beta L hrho hiso,
    neutralized_polar_gamma5 rho beta L hrho hiso h5, mul_zero, add_zero]
  ring

/-- The full complex neutralized polar jet with an actual transported Lorentz generator reduces to its rest-spinor square; b is the half-angle derivative coefficient. -/
theorem polar_generator_jet_square (rho beta a b : ℝ) (L : Mat)
    (omega : Fin 4 → Fin 4 → ℝ) (hrho : 0 ≤ rho) (hunit : IsUnit L)
    (hiso : diracAdjoint L * L = 1) (h5 : Commute L gamma5) :
    bilinear
      ((((a : ℂ) • (1 : Mat)) + (Complex.I * (b : ℂ)) • gamma5 +
        transportedGenerator L omega).mulVec (polarSpinor rho beta L))
      (neutralizer beta)
      ((((a : ℂ) • (1 : Mat)) + (Complex.I * (b : ℂ)) • gamma5 +
        transportedGenerator L omega).mulVec (polarSpinor rho beta L)) =
      (rho : ℂ) * ((a : ℂ)^2 - (b : ℂ)^2 -
        bilinear restSpinor (generator omega * generator omega) restSpinor) := by
  have hi := Matrix.nonsing_inv_mul L ((Matrix.isUnit_iff_isUnit_det _).mp hunit)
  have hadj : diracAdjoint (L⁻¹) = L := by
    rw [inverse_eq_diracAdjoint hiso, diracAdjoint_involutive]
  have hK : diracAdjoint (transportedGenerator L omega) = -transportedGenerator L omega := by
    simp only [transportedGenerator, diracAdjoint_mul, hadj,
      generator_diracAdjoint, ← inverse_eq_diracAdjoint hiso, mul_neg, neg_mul, mul_assoc]
  have hK5 : Commute (transportedGenerator L omega) gamma5 :=
    (h5.mul_left (generator_gamma5_commute omega)).mul_left (inverse_commute hunit h5)
  have hsquare : transportedGenerator L omega * transportedGenerator L omega =
      L * (generator omega * generator omega) * L⁻¹ := by
    simp only [transportedGenerator, mul_assoc, ← mul_assoc L⁻¹ L, hi, one_mul]
  rw [polar_jet_square rho beta a b L _ hrho hiso h5 hK hK5, hsquare,
    neutralized_polar_matrix rho beta L _ hrho hunit hiso h5
      ((generator_gamma5_commute omega).mul_left (generator_gamma5_commute omega))]
  ring

end FoliationQM.ChiralNeutralization
