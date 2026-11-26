module

public import FoliationQM.LatticeNeumannHamiltonian
public import Mathlib.LinearAlgebra.Matrix.Hermitian

/-!
# The replicated path matrix

This is the negative second difference before multiplication by the kinetic
coefficient. Its endpoint rows agree with the Neumann matrix in the reference
solver on every grid with at least two sites.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.LatticeNeumannMatrix

open LatticeConservation

/-- The Kronecker delta on the site indices. -/
def indicatorEntry {n : ℕ} (i j : Fin n) : ℂ := if i = j then 1 else 0

/-- Matrix of the negative second difference, with each missing neighbor
replaced by the boundary site itself. -/
def kinetic {n : ℕ} : Matrix (Fin n) (Fin n) ℂ :=
  fun i j => 2 * indicatorEntry i j - indicatorEntry (nextNode i) j - indicatorEntry (prevNode i) j

private theorem sum_delta {n : ℕ} (z : Fin n → ℂ) (i : Fin n) :
    ∑ j, indicatorEntry i j * z j = z i := by
  classical
  simp [indicatorEntry, ite_mul, Finset.sum_ite_eq]

/-- Applying the matrix gives the replicated second-difference stencil at
every row, including a single isolated site. -/
theorem mulVec_kinetic {n : ℕ} (z : Fin n → ℂ) (i : Fin n) :
    kinetic.mulVec z i = 2 * z i - z (nextNode i) - z (prevNode i) := by
  simp only [Matrix.mulVec_apply_eq_sum, kinetic, sub_mul, mul_assoc,
    Finset.sum_sub_distrib, ← Finset.mul_sum, sum_delta]

/-- The diagonal counts distinct neighbors. The isolated site has degree zero,
the two ends of a longer grid have degree one, and interior sites have degree two. -/
theorem kinetic_diag {n : ℕ} (i : Fin n) :
    kinetic i i = if n = 1 then 0 else if i.val = 0 ∨ i.val + 1 = n then 1 else 2 := by
  have hi := i.isLt
  have hnext : nextNode i = i ↔ i.val + 1 = n := by
    unfold nextNode
    split <;> simp [Fin.ext_iff] <;> omega
  have hprev : prevNode i = i ↔ i.val = 0 := by
    simp only [prevNode, Fin.ext_iff]
    omega
  by_cases hn : n = 1 <;> by_cases hl : i.val = 0 <;> by_cases hr : i.val + 1 = n <;>
    simp [kinetic, indicatorEntry, hnext, hprev, hn, hl, hr, eq_comm (a := 1) (b := n)] <;> first | omega | norm_num

/-- An off-diagonal entry equals minus one exactly between adjacent sites.
In particular the two ends of a grid with three or more sites have no wraparound link. -/
theorem kinetic_offdiag {n : ℕ} {i j : Fin n} (hij : i ≠ j) :
    kinetic i j = if i.val + 1 = j.val ∨ j.val + 1 = i.val then -1 else 0 := by
  have hi := i.isLt
  have hj := j.isLt
  simp only [kinetic, indicatorEntry, nextNode, prevNode]
  split_ifs <;> simp_all [Fin.ext_iff] <;> omega

/-- The complex matrix of the replicated path is Hermitian for every finite grid. -/
theorem kinetic_isHermitian {n : ℕ} : (kinetic (n := n)).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  by_cases h : i = j
  · subst j
    rw [kinetic_diag]
    split_ifs <;> simp
  · rw [kinetic_offdiag (Ne.symm h), kinetic_offdiag h]
    simp only [show (j.val + 1 = i.val ∨ i.val + 1 = j.val) ↔
      (i.val + 1 = j.val ∨ j.val + 1 = i.val) from or_comm]
    split_ifs <;> simp

/-- Neumann matrix in angular-frequency units with an arbitrary real potential at each site. -/
def frequencyMatrix {n : ℕ} (p : MassiveParameters) (h : ℝ) (V : Fin n → ℝ) :
    Matrix (Fin n) (Fin n) ℂ :=
  (p.omega0 : ℂ) • (Complex.ofReal (p.ellC ^ 2 / (2 * h ^ 2)) • kinetic +
    Matrix.diagonal (fun i => Complex.ofReal (V i / (p.m * p.c ^ 2))))

/-- Matrix multiplication realizes the angular-frequency Hamiltonian of the weighted energy. -/
theorem frequencyMatrix_mulVec {n : ℕ} (p : MassiveParameters) (h : ℝ)
    (V : Fin n → ℝ) (z : Fin n → ℂ) :
    (frequencyMatrix p h V).mulVec z = LatticeNeumannHamiltonian.frequency p h V z := by
  funext i
  simp only [frequencyMatrix, Matrix.smul_mulVec, Matrix.add_mulVec, Pi.smul_apply,
    Pi.add_apply, smul_eq_mul, Matrix.mulVec_diagonal, mulVec_kinetic,
    LatticeNeumannHamiltonian.frequency, LatticeNeumannHamiltonian.dimless,
    LatticeNeumannGreen.laplacian]
  ring

/-- Real kinetic and potential coefficients make the full angular-frequency matrix Hermitian. -/
theorem frequencyMatrix_isHermitian {n : ℕ} (p : MassiveParameters) (h : ℝ)
    (V : Fin n → ℝ) : (frequencyMatrix p h V).IsHermitian := by
  apply Matrix.IsHermitian.smul _ (Complex.conj_ofReal _)
  apply Matrix.IsHermitian.add (kinetic_isHermitian.smul (Complex.conj_ofReal _))
  apply Matrix.isHermitian_diagonal_of_self_adjoint
  funext i
  exact Complex.conj_ofReal _

end FoliationQM.LatticeNeumannMatrix
