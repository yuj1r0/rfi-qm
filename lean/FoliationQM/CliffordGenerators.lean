module

public import FoliationQM.DiracAdjoint
public import Mathlib.Tactic.Ring

/-!
# The indexed Clifford generator anticommutators

Sources: v13 `eq:clifford_anticomm` and `eq:sigma_anticomm`, together with
their rest-spinor contractions in the proof of `thm:dirac_lift` (i)–(ii).
All matrices are the actual (+---) Dirac matrices from DiracMatrices. The
Levi-Civita coefficients have orientation epsilon0123 = +1; the signed
Vandermonde differences are taken only after coercion into the complex
numbers, so no natural-number subtraction occurs.

The full finite index identities are kernel-checked from those matrices.
A private sigma lookup table is itself proved equal to the original sigma
definition and is used only to avoid repeating large matrix expansions.
The exact rest contractions use the actual Dirac bilinear. No connection
field, differential spinor identity, or geometric Lagrangian conclusion is
assumed or established here.
-/

@[expose] public section
noncomputable section

namespace FoliationQM.CliffordGenerators
open DiracMatrices DiracAdjoint

/-- The oriented four-index Levi-Civita coefficient, given by signed coerced-index Vandermonde differences divided by twelve. -/
def epsilon (a b c d : Fin 4) : ℂ :=
  (((b.val : ℂ) - a.val) * ((c.val : ℂ) - a.val) * ((d.val : ℂ) - a.val) *
    ((c.val : ℂ) - b.val) * ((d.val : ℂ) - b.val) * ((d.val : ℂ) - c.val)) / 12

/-- The actual Levi-Civita coefficient has the source positive 0123 orientation. -/
theorem epsilon_0123 : epsilon 0 1 2 3 = 1 := by norm_num [epsilon]

/-- Swapping the first two actual Levi-Civita indices reverses its sign. -/
theorem epsilon_swap_first (a b c d : Fin 4) : epsilon b a c d = -epsilon a b c d := by
  unfold epsilon
  ring

/-- Swapping the two middle actual Levi-Civita indices reverses its sign. -/
theorem epsilon_swap_middle (a b c d : Fin 4) : epsilon a c b d = -epsilon a b c d := by
  unfold epsilon
  ring

/-- Swapping the last two actual Levi-Civita indices reverses its sign. -/
theorem epsilon_swap_last (a b c d : Fin 4) : epsilon a b d c = -epsilon a b c d := by
  unfold epsilon
  ring

/-- Any repeated pair of actual Levi-Civita indices gives zero. -/
theorem epsilon_eq_zero_of_repeated {a b c d : Fin 4}
    (h : a = b ∨ a = c ∨ a = d ∨ b = c ∨ b = d ∨ c = d) : epsilon a b c d = 0 := by
  rcases h with h | h | h | h | h | h <;> subst_vars <;> simp [epsilon]

private theorem zero_matrix :
    (!![0,0,0,0;0,0,0,0;0,0,0,0;0,0,0,0] : Mat) = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

private def sigmaTable : Fin 4 → Fin 4 → Mat :=
  ![![!![0, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0],
    !![0, 0, 0, Complex.I; 0, 0, Complex.I, 0; 0, Complex.I, 0, 0; Complex.I, 0, 0, 0],
    !![0, 0, 0, 1; 0, 0, -1, 0; 0, 1, 0, 0; -1, 0, 0, 0],
    !![0, 0, Complex.I, 0; 0, 0, 0, -Complex.I; Complex.I, 0, 0, 0; 0, -Complex.I, 0, 0]],
  ![!![0, 0, 0, -Complex.I; 0, 0, -Complex.I, 0; 0, -Complex.I, 0, 0; -Complex.I, 0, 0, 0],
    !![0, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0],
    !![1, 0, 0, 0; 0, -1, 0, 0; 0, 0, 1, 0; 0, 0, 0, -1],
    !![0, Complex.I, 0, 0; -Complex.I, 0, 0, 0; 0, 0, 0, Complex.I; 0, 0, -Complex.I, 0]],
  ![!![0, 0, 0, -1; 0, 0, 1, 0; 0, -1, 0, 0; 1, 0, 0, 0],
    !![-1, 0, 0, 0; 0, 1, 0, 0; 0, 0, -1, 0; 0, 0, 0, 1],
    !![0, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0],
    !![0, 1, 0, 0; 1, 0, 0, 0; 0, 0, 0, 1; 0, 0, 1, 0]],
  ![!![0, 0, -Complex.I, 0; 0, 0, 0, Complex.I; -Complex.I, 0, 0, 0; 0, Complex.I, 0, 0],
    !![0, -Complex.I, 0, 0; Complex.I, 0, 0, 0; 0, 0, 0, -Complex.I; 0, 0, Complex.I, 0],
    !![0, -1, 0, 0; -1, 0, 0, 0; 0, 0, 0, -1; 0, 0, -1, 0],
    !![0, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0]]]

set_option maxHeartbeats 5000000 in
private theorem sigma_table (a b : Fin 4) : sigma a b = sigmaTable a b := by
  fin_cases a <;> fin_cases b <;>
    norm_num [sigma, sigmaTable, gamma] <;>
    norm_num [funext_iff, Fin.forall_fin_succ, Matrix.mul_apply, Fin.sum_univ_succ,
      div_mul_eq_mul_div, mul_sub, mul_add] <;> ring_nf <;> norm_num [zero_matrix]

set_option maxHeartbeats 20000000 in
/-- The full indexed gamma–sigma anticommutator equals the source positive epsilon contraction with gamma5 times the lowered gamma matrix. -/
theorem gamma_sigma_anticomm (A a b : Fin 4) :
    gamma A * sigma a b + sigma a b * gamma A =
      (2 : ℂ) • ∑ d : Fin 4, epsilon A a b d • (gamma5 * gammaLower d) := by
  rw [gamma5_explicit, sigma_table]
  fin_cases A <;> fin_cases a <;> fin_cases b <;>
    norm_num [epsilon, gamma, gammaLower, sigmaTable, Fin.sum_univ_succ] <;>
    ring_nf <;> norm_num [zero_matrix]


/-- The actual chiral matrix anticommutes with every lowered-index Dirac matrix. -/
theorem gamma5_gammaLower_anticomm (d : Fin 4) :
    gamma5 * gammaLower d = -(gammaLower d * gamma5) := by
  by_cases h : d = 0 <;> simp [gammaLower, h, gamma5_anticomm]

/-- Reversing gamma5 and the lowered gamma matrix gives the source negative-two epsilon contraction. -/
theorem gamma_sigma_anticomm_reversed (A a b : Fin 4) :
    gamma A * sigma a b + sigma a b * gamma A =
      (-2 : ℂ) • ∑ d : Fin 4, epsilon A a b d • (gammaLower d * gamma5) := by
  rw [gamma_sigma_anticomm]
  simp only [gamma5_gammaLower_anticomm, smul_neg, Finset.sum_neg_distrib, neg_smul]

/-- The actual lowered-index axial rest bilinear is minus the delta selecting index three. -/
theorem rest_lower_axial (d : Fin 4) :
    bilinear restSpinor (gammaLower d * gamma5) restSpinor = if d = 3 then -1 else 0 := by
  fin_cases d <;> simp [gammaLower, neg_mul, bilinear_neg_matrix, rest_axial]

/-- The actual rest-spinor contraction of the full gamma–sigma anticommutator is exactly two epsilon Aab3. -/
theorem rest_gamma_sigma_anticomm (A a b : Fin 4) :
    bilinear restSpinor (gamma A * sigma a b + sigma a b * gamma A) restSpinor =
      2 * epsilon A a b 3 := by
  rw [gamma_sigma_anticomm_reversed]
  rw [bilinear_smul_matrix]
  simp only [Fin.sum_univ_succ, bilinear_smul_matrix,
    bilinear_add_matrix, rest_lower_axial]
  norm_num [bilinear]


set_option maxHeartbeats 40000000 in
/-- The full indexed sigma anticommutator is the exact source metric contraction plus positive i epsilon times gamma5. -/
theorem sigma_anticomm (a b c d : Fin 4) :
    (1 / 2 : ℂ) • (sigma a b * sigma c d + sigma c d * sigma a b) =
      (eta a c * eta b d - eta a d * eta b c) • (1 : Mat) +
        (Complex.I * epsilon a b c d) • gamma5 := by
  rw [sigma_table, sigma_table, gamma5_explicit]
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    norm_num [sigmaTable, eta, epsilon] <;>
    norm_num [funext_iff, Fin.forall_fin_succ, Matrix.mul_apply, Matrix.one_apply,
      Fin.sum_univ_succ, div_mul_eq_mul_div, mul_sub, mul_add] <;>
    ring_nf <;> norm_num [zero_matrix] <;>
    ext i j <;> fin_cases i <;> fin_cases j <;> norm_num [Matrix.one_apply]

/-- The actual rest-spinor sigma anticommutator contraction retains the metric term and eliminates the gamma5 term. -/
theorem rest_sigma_anticomm (a b c d : Fin 4) :
    bilinear restSpinor ((1 / 2 : ℂ) •
      (sigma a b * sigma c d + sigma c d * sigma a b)) restSpinor =
      eta a c * eta b d - eta a d * eta b c := by
  rw [sigma_anticomm]
  simp [bilinear_add_matrix, bilinear_smul_matrix, rest_scalar, rest_pseudoscalar]

end FoliationQM.CliffordGenerators
