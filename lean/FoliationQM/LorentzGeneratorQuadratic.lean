module

public import FoliationQM.CliffordCommutators
public import FoliationQM.SixTermConnection
public import Mathlib.Basic.Complex.BigOperators
/-!
# Actual rest-spinor quadratic Lorentz-generator contractions

Source: v13 `eq:spinor_quadratic_exact`, the sigma-anticommutator contraction
in its proof, and `eq:six_terms_omega`. The generator is the existing actual
ordered double sum -i omega_ab sigma^ab/4 in signature (+---).

The required first row and first column are derived from the actual gamma
and sigma matrices. Their actual matrix products and the rest Dirac bilinear
then give the signed six-pair quadratic contraction with factor one quarter.
The mixed result uses the genuine symmetric matrix product, and the finite
weighted version includes the diagonal spacetime metric as a specialization.
All finite matrix and scalar calculations are kernel checked. No connection
field, derivative identity, or quadratic kinetic conclusion is a premise.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.LorentzGeneratorQuadratic
open DiracMatrices DiracAdjoint CliffordCommutators SixTermConnection

private theorem rest_bilinear_entry (A : Mat) : bilinear restSpinor A restSpinor = A 0 0 := by
  simp [bilinear, restSpinor, gamma, Matrix.mulVec, dotProduct, Matrix.mul_apply,
    Fin.sum_univ_succ]

set_option maxHeartbeats 3000000 in
private theorem generator_first_row (omega : Fin 4 → Fin 4 → ℝ)
    (hanti : ∀ a b, omega a b = -omega b a) :
    (fun j => generator omega 0 j) =
      ![-Complex.I*(omega 1 2 : ℂ)/2,
        ((omega 1 3 : ℂ)-Complex.I*(omega 2 3 : ℂ))/2,
        (omega 0 3 : ℂ)/2,
        ((omega 0 1 : ℂ)-Complex.I*(omega 0 2 : ℂ))/2] := by
  funext j
  fin_cases j <;>
    simp [generator, sigma, gamma, Fin.sum_univ_succ, hanti 1 0, hanti 2 0, hanti 3 0,
      hanti 2 1, hanti 3 1, hanti 3 2] <;> ring_nf <;> norm_num <;> ring

set_option maxHeartbeats 3000000 in
private theorem generator_first_column (omega : Fin 4 → Fin 4 → ℝ)
    (hanti : ∀ a b, omega a b = -omega b a) :
    (fun i => generator omega i 0) =
      ![-Complex.I*(omega 1 2 : ℂ)/2,
        (-(omega 1 3 : ℂ)-Complex.I*(omega 2 3 : ℂ))/2,
        (omega 0 3 : ℂ)/2,
        ((omega 0 1 : ℂ)+Complex.I*(omega 0 2 : ℂ))/2] := by
  funext i
  fin_cases i <;>
    simp [generator, sigma, gamma, Fin.sum_univ_succ, hanti 1 0, hanti 2 0, hanti 3 0,
      hanti 2 1, hanti 3 1, hanti 3 2] <;> ring_nf <;> norm_num <;> ring

/-- The negative actual rest-spinor generator square is one quarter of the six-pair Minkowski contraction for real antisymmetric coefficients. -/
theorem rest_generator_square (omega : Fin 4 → Fin 4 → ℝ)
    (hanti : ∀ a b, omega a b = -omega b a) :
    -bilinear restSpinor (generator omega * generator omega) restSpinor =
      ((pairedProductSum omega omega /4 : ℝ):ℂ) := by
  rw [rest_bilinear_entry, Matrix.mul_apply]
  change -(∑ i, (fun j=>generator omega 0 j) i*(fun j=>generator omega j 0) i) = _
  rw [generator_first_row omega hanti, generator_first_column omega hanti,
    pairedProductSum_eq_six_terms]
  norm_num [Fin.sum_univ_succ]
  ring_nf
  norm_num
  ring

/-- The negative symmetric actual mixed generator product has the corresponding real six-pair contraction with factor one quarter. -/
theorem rest_generator_symmetric (omega theta : Fin 4 → Fin 4 → ℝ)
    (hω : ∀ a b, omega a b = -omega b a) (hθ : ∀ a b, theta a b = -theta b a) :
    -(1/2:ℂ)*bilinear restSpinor
      (generator omega*generator theta+generator theta*generator omega) restSpinor =
      ((pairedProductSum omega theta /4 : ℝ):ℂ) := by
  rw [rest_bilinear_entry]
  simp only [Matrix.add_apply, Matrix.mul_apply]
  change -(1/2:ℂ)*((∑ i, (fun j=>generator omega 0 j) i*(fun j=>generator theta j 0) i)+
    (∑i, (fun j=>generator theta 0 j) i*(fun j=>generator omega j 0) i)) = _
  rw [generator_first_row omega hω, generator_first_column theta hθ,
    generator_first_row theta hθ, generator_first_column omega hω, pairedProductSum_eq_six_terms]
  norm_num [Fin.sum_univ_succ]
  ring_nf
  norm_num
  ring

/-- Any finite real weighting of actual rest generator squares gives the same weighting of the verified six-pair contractions, including diagonal spacetime metric weights. -/
theorem rest_generator_weighted_sum {ι : Type*} [Fintype ι]
    (weight : ι → ℝ) (omega : ι → Fin 4 → Fin 4 → ℝ)
    (hanti : ∀ mu a b, omega mu a b = -omega mu b a) :
    -(∑ mu, (weight mu : ℂ)*bilinear restSpinor
      (generator (omega mu)*generator (omega mu)) restSpinor) =
      ((∑ mu, weight mu*pairedProductSum (omega mu) (omega mu)/4 : ℝ):ℂ) := by
  rw [← Finset.sum_neg_distrib, Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro mu _
  rw [← mul_neg, rest_generator_square (omega mu) (hanti mu)]
  push_cast
  ring

end FoliationQM.LorentzGeneratorQuadratic
