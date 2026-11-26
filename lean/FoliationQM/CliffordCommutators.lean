module

public import FoliationQM.DiracAdjoint

/-!
# Actual Clifford commutators and real connection coefficients

Source: the indexed Lorentz-generator commutator and its antisymmetric
coefficient contraction in v13 `lem:maurer_cartan`, particularly the proof
of `eq:ricci_rotation_coeffs`. All gamma and sigma matrices are the existing
explicit upper-index Dirac representation in signature (+---).

The real coefficient array is paired with these actual upper-index sigma
matrices in an ordered double sum with coefficient -i/4. The summed
commutator derives its normalization by exchanging the antisymmetric index
pair. The coefficient expansion is explicit input data; no claim is made
that arbitrary Dirac-isometric matrix derivatives have this expansion.
The actual adjoint and gamma5 constraints hold for every real input array.
-/

@[expose] public section

noncomputable section
namespace FoliationQM.CliffordCommutators
open DiracMatrices DiracAdjoint

private theorem gamma_pair_commutator (a b A : Fin 4) :
    gamma a * gamma b * gamma A - gamma A * (gamma a * gamma b) =
      (2 * eta b A) • gamma a - (2 * eta a A) • gamma b := by
  calc
    _ = gamma a * (gamma b * gamma A + gamma A * gamma b) -
        (gamma a * gamma A + gamma A * gamma a) * gamma b := by noncomm_ring
    _ = _ := by rw [clifford b A, clifford a A]; simp

/-- The actual indexed Lorentz-generator commutator has the source Minkowski coefficients and signs. -/
theorem sigma_gamma_commutator (a b A : Fin 4) :
    ((-Complex.I / 2 : ℂ) • sigma a b) * gamma A -
      gamma A * ((-Complex.I / 2 : ℂ) • sigma a b) =
      eta b A • gamma a - eta a A • gamma b := by
  have hc : (-Complex.I / 2 : ℂ) • sigma a b =
      (1/4 : ℂ) • (gamma a * gamma b - gamma b * gamma a) := by
    unfold sigma
    rw [smul_smul]
    congr 1
    norm_num [div_mul_div_comm, Complex.I_sq]
  rw [hc]
  calc
    _ = (1/4 : ℂ) • ((gamma a * gamma b * gamma A - gamma A * (gamma a * gamma b)) -
        (gamma b * gamma a * gamma A - gamma A * (gamma b * gamma a))) := by
      simp only [smul_mul_assoc, mul_smul_comm, ← smul_sub]
      congr 1
      noncomm_ring
    _ = _ := by
      rw [gamma_pair_commutator, gamma_pair_commutator]
      module

/-- The actual matrix generator formed from a real coefficient array with the ordered double-sum normalization minus i over four. -/
def generator (omega : Fin 4 → Fin 4 → ℝ) : Mat :=
  ∑ a, ∑ b, (-Complex.I * (omega a b : ℂ) / 4) • sigma a b

/-- The quarter-normalized generator equals one half of the weighted sum of the indexed minus-i-over-two generators. -/
theorem generator_eq_half_sum (omega : Fin 4 → Fin 4 → ℝ) :
    generator omega = (1/2 : ℂ) • ∑ a, ∑ b,
      (omega a b : ℂ) • ((-Complex.I/2 : ℂ) • sigma a b) := by
  simp only [generator, Finset.smul_sum, smul_smul]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  congr 1
  ring

private theorem weighted_swap (omega : Fin 4 → Fin 4 → ℝ)
    (hanti : ∀ a b, omega a b = -omega b a) (A : Fin 4) :
    (∑ a, ∑ b, ((omega a b : ℂ) * eta a A) • gamma b) =
      -(∑ a, ∑ b, ((omega a b : ℂ) * eta b A) • gamma a) := by
  rw [Finset.sum_comm]
  calc
    _ = ∑ a, ∑ b, -(((omega a b : ℂ) * eta b A) • gamma a) := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      rw [hanti b a]
      simp
    _ = _ := by simp

/-- Antisymmetry combines both index orders to give the source full coefficient contraction in the actual gamma commutator. -/
theorem generator_gamma_commutator (omega : Fin 4 → Fin 4 → ℝ)
    (hanti : ∀ a b, omega a b = -omega b a) (A : Fin 4) :
    generator omega * gamma A - gamma A * generator omega =
      ∑ a, ∑ b, ((omega a b : ℂ) * eta b A) • gamma a := by
  have hexp : generator omega * gamma A - gamma A * generator omega =
      (1/2 : ℂ) • ∑ a, ∑ b,
        (omega a b : ℂ) • (eta b A • gamma a - eta a A • gamma b) := by
    rw [generator_eq_half_sum]
    simp only [smul_mul_assoc, mul_smul_comm, Matrix.sum_mul, Matrix.mul_sum]
    rw [← smul_sub, ← Finset.sum_sub_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro a _
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro b _
    rw [← smul_sub]
    congr 1
    simpa only [smul_mul_assoc, mul_smul_comm] using sigma_gamma_commutator a b A
  rw [hexp]
  simp only [smul_sub, smul_smul, Finset.sum_sub_distrib]
  rw [weighted_swap omega hanti A]
  module

private theorem gamma5_pair (a b : Fin 4) :
    gamma5 * (gamma a * gamma b) = (gamma a * gamma b) * gamma5 := by
  rw [← mul_assoc, gamma5_anticomm, neg_mul, mul_assoc, gamma5_anticomm,
    mul_neg, neg_neg, ← mul_assoc]

/-- Every actual Lorentz bivector sigma matrix commutes with gamma5. -/
theorem sigma_gamma5_commute (a b : Fin 4) : Commute (sigma a b) gamma5 := by
  change sigma a b * gamma5 = gamma5 * sigma a b
  simp only [sigma, smul_mul_assoc, mul_smul_comm, sub_mul, mul_sub]
  rw [gamma5_pair, gamma5_pair]

/-- Every real coefficient expansion of actual Lorentz generators commutes with gamma5. -/
theorem generator_gamma5_commute (omega : Fin 4 → Fin 4 → ℝ) :
    Commute (generator omega) gamma5 := by
  change generator omega * gamma5 = gamma5 * generator omega
  simp only [generator, Matrix.sum_mul, Matrix.mul_sum, smul_mul_assoc, mul_smul_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  rw [(sigma_gamma5_commute a b).eq]

private theorem adjoint_sum {ι : Type*} [Fintype ι] (f : ι → Mat) :
    diracAdjoint (∑ i, f i) = ∑ i, diracAdjoint (f i) := by
  simp [diracAdjoint, Matrix.conjTranspose_sum, Matrix.mul_sum, Matrix.sum_mul]

/-- Every actual generator with real coefficients is anti-self-adjoint under the Dirac adjoint. -/
theorem generator_diracAdjoint (omega : Fin 4 → Fin 4 → ℝ) :
    diracAdjoint (generator omega) = -generator omega := by
  simp only [generator, adjoint_sum, diracAdjoint_smul, diracAdjoint_sigma]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro a _
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro b _
  rw [← neg_smul]
  congr 1
  simp only [star_div₀, star_mul, star_neg, Complex.star_def, Complex.conj_I,
    Complex.conj_ofReal, map_ofNat, neg_neg]
  ring

end FoliationQM.CliffordCommutators
