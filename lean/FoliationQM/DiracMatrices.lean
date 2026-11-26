module

public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum

/-!
# Explicit Dirac representation and the rest-spinor rotor algebra

Sources: v13 `thm:contact_period` (iii), `eq:rotor_compton_evolution`,
`lem:maurer_cartan`, and the standard-Dirac-matrix conventions in `sec:spinor`.
The signature is (+---). All matrices and the reference spinor are explicit;
the Clifford and rest-spinor identities are verified in this representation.
This is a concrete matrix realization, not a classification of Clifford
representations or a construction of the full spin group.
-/

@[expose] public section
noncomputable section

namespace FoliationQM.DiracMatrices

open Complex

/-- The actual complex four-by-four matrices of the Dirac representation. -/
abbrev Mat := Matrix (Fin 4) (Fin 4) ℂ

/-- The actual four-component complex Dirac spinor space. -/
abbrev Spinor := Fin 4 → ℂ

/-- The standard upper-index Dirac matrices, with Pauli spatial blocks and signature (+---). -/
def gamma : Fin 4 → Mat :=
  ![!![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, -1, 0; 0, 0, 0, -1],
    !![0, 0, 0, 1; 0, 0, 1, 0; 0, -1, 0, 0; -1, 0, 0, 0],
    !![0, 0, 0, -I; 0, 0, I, 0; 0, I, 0, 0; -I, 0, 0, 0],
    !![0, 0, 1, 0; 0, 0, 0, -1; -1, 0, 0, 0; 0, 1, 0, 0]]

/-- The complex-valued diagonal Minkowski metric coefficients in signature (+---). -/
def eta (a b : Fin 4) : ℂ := if a = b then (if a = 0 then 1 else -1) else 0

/-- Lowering a Dirac-matrix index changes exactly the spatial signs. -/
def gammaLower (a : Fin 4) : Mat := if a = 0 then gamma a else -gamma a

/-- The chiral matrix is the actual ordered product i gamma0 gamma1 gamma2 gamma3. -/
def gamma5 : Mat := I • (gamma 0 * gamma 1 * gamma 2 * gamma 3)

/-- The actual antisymmetric Dirac bivector matrices sigma^{ab} = (i/2)[gamma^a,gamma^b]. -/
def sigma (a b : Fin 4) : Mat := (I / 2) • (gamma a * gamma b - gamma b * gamma a)

/-- The spatial 1–2-plane Clifford generator underlying the source rotor. -/
def planeGenerator : Mat := gamma 1 * gamma 2

/-- A fixed positive-energy spin-up rest spinor in the explicit Dirac representation. -/
def restSpinor : Spinor := ![1, 0, 0, 0]

set_option maxHeartbeats 1000000 in
/-- The explicit Dirac matrices exhaustively satisfy the Clifford relations in signature (+---). -/
theorem clifford (a b : Fin 4) :
    gamma a * gamma b + gamma b * gamma a = (2 * eta a b) • (1 : Mat) := by
  fin_cases a <;> fin_cases b <;>
    ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [gamma, eta, Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_succ]

/-- The actual spatial-plane generator is diagonal with entries -i, i, -i, i. -/
theorem planeGenerator_diagonal :
    planeGenerator = Matrix.diagonal ![-I, I, -I, I] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [planeGenerator, gamma, Matrix.mul_apply, Matrix.diagonal_apply, Fin.sum_univ_succ]

/-- The ordered chiral product is the standard off-diagonal Dirac gamma5 matrix. -/
theorem gamma5_explicit :
    gamma5 = !![0, 0, 1, 0; 0, 0, 0, 1; 1, 0, 0, 0; 0, 1, 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [gamma5, gamma, Matrix.mul_apply, Fin.sum_univ_succ]

/-- The actual temporal Dirac matrix squares to the identity. -/
theorem gamma_zero_sq : gamma 0 * gamma 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [gamma, Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_succ]

/-- The actual spatial 1–2-plane Clifford generator squares to minus the identity. -/
theorem generator_sq : planeGenerator * planeGenerator = -1 := by
  rw [planeGenerator_diagonal]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, Matrix.diagonal_apply, Matrix.one_apply, Fin.sum_univ_succ]

/-- The actual chiral matrix gamma5 squares to the identity. -/
theorem gamma5_sq : gamma5 * gamma5 = 1 := by
  rw [gamma5_explicit]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_succ]

/-- The actual chiral matrix anticommutes with every Dirac matrix. -/
theorem gamma5_anticomm (a : Fin 4) : gamma5 * gamma a = -(gamma a * gamma5) := by
  rw [gamma5_explicit]
  fin_cases a <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [gamma, Matrix.mul_apply, Fin.sum_univ_succ]

/-- The actual plane generator acts on the reference rest spinor with eigenvalue -i. -/
theorem generator_mulVec_restSpinor : planeGenerator.mulVec restSpinor = (-I) • restSpinor := by
  rw [planeGenerator_diagonal]
  ext i
  fin_cases i <;> norm_num [Matrix.mulVec, dotProduct, Matrix.diagonal_apply,
    restSpinor, Fin.sum_univ_succ]

/-- The actual sigma12 bivector is i times the actual spatial-plane Clifford generator. -/
theorem sigma12_eq_I_smul_generator : sigma 1 2 = I • planeGenerator := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [sigma, planeGenerator, gamma, Matrix.mul_apply, Fin.sum_univ_succ,
      div_mul_eq_mul_div, mul_sub, mul_add]

/-- The reference rest spinor has sigma12 eigenvalue +1, fixing the source rotor orientation. -/
theorem sigma12_mulVec_restSpinor : (sigma 1 2).mulVec restSpinor = restSpinor := by
  rw [sigma12_eq_I_smul_generator, Matrix.smul_mulVec, generator_mulVec_restSpinor, smul_smul]
  simp

/-- The reference rest spinor has temporal Dirac eigenvalue +1, as required for positive rest energy. -/
theorem gamma_zero_mulVec_restSpinor : (gamma 0).mulVec restSpinor = restSpinor := by
  ext i
  fin_cases i <;> norm_num [Matrix.mulVec, dotProduct, gamma, restSpinor, Fin.sum_univ_succ]

/-- The actual Dirac bivector matrices are antisymmetric in their two indices. -/
theorem sigma_swap (a b : Fin 4) : sigma b a = -sigma a b := by
  rw [sigma, sigma, ← smul_neg, neg_sub]

/-- A repeated index gives the zero Dirac bivector matrix. -/
theorem sigma_self (a : Fin 4) : sigma a a = 0 := by
  simp [sigma]

/-- The source generator -i sigma12 equals the actual spatial-plane Clifford generator. -/
theorem neg_I_smul_sigma12 : (-I) • sigma 1 2 = planeGenerator := by
  rw [sigma12_eq_I_smul_generator, smul_smul]
  simp

/-- The two lowered spatial matrices give the same plane generator as the two upper matrices. -/
theorem gammaLower_planeGenerator : gammaLower 1 * gammaLower 2 = planeGenerator := by
  simp [gammaLower, planeGenerator]

/-- The explicit reference rest spinor is nonzero. -/
theorem restSpinor_ne_zero : restSpinor ≠ 0 := by
  intro h
  have h0 := congrArg (fun v : Spinor => v 0) h
  simp [restSpinor] at h0

end FoliationQM.DiracMatrices
