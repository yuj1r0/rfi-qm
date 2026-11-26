module

public import FoliationQM.LatticeNeumannMatrix

/-!
# The tridiagonal matrix in the numerical reference

The independent reference in `simulate_foliation_qm_v9.py` (lines 216–231)
sets the mass and reduced Planck constant to one. Its real diagonal and
constant neighboring entries define an exact real-valued matrix acting
on complex site amplitudes. Two or more sites are required for the script
to obtain its spacing from the first two sample points.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.LatticeNeumannReferenceRows

open LatticeNeumannMatrix LatticeNeumannHamiltonian

/-- Parameters of the solver in units with ℏ = m = 1 and arbitrary positive light speed. -/
def parameters (c : ℝ) (hc : 0 < c) : MassiveParameters :=
  ⟨c, 1, 1, hc, by norm_num, by norm_num⟩

/-- In the simulation units the Compton length is 1/c and the clock frequency is c². -/
theorem clock_scales (c : ℝ) (hc : 0 < c) :
    (parameters c hc).ellC = 1/c ∧ (parameters c hc).omega0 = c^2 := by
  simp [parameters, MassiveParameters.ellC, MassiveParameters.omega0]

/-- The two physical kinetic factors give the coefficient 0.5/h² in the script. -/
theorem kinetic_coefficient (c : ℝ) (hc : 0 < c) (h : ℝ) :
    (parameters c hc).omega0 * ((parameters c hc).ellC^2/(2*h^2)) = (1/2)/h^2 := by
  rw [(clock_scales c hc).1, (clock_scales c hc).2]
  rw [div_pow, ← mul_div_assoc]
  field_simp [hc.ne']

/-- The clock frequency converts each normalized potential back to its input value. -/
theorem potential_coefficient (c : ℝ) (hc : 0 < c) (v : ℝ) :
    (parameters c hc).omega0 * (v/((parameters c hc).m*(parameters c hc).c^2)) = v := by
  rw [(clock_scales c hc).2]
  change c^2 * (v / (1 * c^2)) = v
  field_simp [hc.ne']

/-- The real diagonal array passed to the tridiagonal eigensolver. -/
def diagonal {n : ℕ} (h : ℝ) (V : Fin n → ℝ) (i : Fin n) : ℝ :=
  (if i.val = 0 ∨ i.val+1 = n then (1/2)/h^2 else 1/h^2) + V i

/-- Each entry of the neighboring off-diagonal array. -/
def offDiagonal (h : ℝ) : ℝ := -(1/2)/h^2

/-- Exact tridiagonal reference operator with the real entries acting on complex waves. -/
def referenceMatrix {n : ℕ} (h : ℝ) (V : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  fun i j => Complex.ofReal (if i = j then diagonal h V i
    else if i.val+1 = j.val ∨ j.val+1 = i.val then offDiagonal h else 0)

private theorem scaled_diagonal {n : ℕ} (c : ℝ) (hc : 0 < c)
    (h : ℝ) (V : Fin n → ℝ) (i : Fin n) :
    frequencyMatrix (parameters c hc) h V i i =
      Complex.ofReal ((1/2)/h^2) * kinetic i i + Complex.ofReal (V i) := by
  simp only [frequencyMatrix, Matrix.smul_apply, Matrix.add_apply, smul_eq_mul,
    Matrix.diagonal_apply_eq, mul_add, ← mul_assoc, ← Complex.ofReal_mul,
    kinetic_coefficient c hc, potential_coefficient c hc]

/-- Each endpoint diagonal carries half the interior kinetic weight plus its site potential. -/
theorem endpoint_entry {n : ℕ} (hn : 2 ≤ n) (c : ℝ) (hc : 0 < c)
    (h : ℝ) (V : Fin n → ℝ) (i : Fin n) (hi : i.val = 0 ∨ i.val+1 = n) :
    frequencyMatrix (parameters c hc) h V i i = Complex.ofReal ((1/2)/h^2 + V i) := by
  have hn' : n ≠ 1 := by omega
  rw [scaled_diagonal, kinetic_diag]
  simp [hn', hi]

/-- An interior diagonal entry is the full 1/h² kinetic weight plus its site potential. -/
theorem interior_entry {n : ℕ} (hn : 2 ≤ n) (c : ℝ) (hc : 0 < c)
    (h : ℝ) (V : Fin n → ℝ) (i : Fin n) (hi : ¬(i.val = 0 ∨ i.val+1 = n)) :
    frequencyMatrix (parameters c hc) h V i i = Complex.ofReal (1/h^2 + V i) := by
  have hn' : n ≠ 1 := by omega
  rw [scaled_diagonal, kinetic_diag]
  simp [hn', hi]
  ring

/-- Distinct sites have the script's −0.5/h² entry exactly when adjacent, and zero elsewhere. -/
theorem off_diagonal_entry {n : ℕ} (c : ℝ) (hc : 0 < c)
    (h : ℝ) (V : Fin n → ℝ) (i j : Fin n) (hij : i ≠ j) :
    frequencyMatrix (parameters c hc) h V i j =
      Complex.ofReal (if i.val+1 = j.val ∨ j.val+1 = i.val then offDiagonal h else 0) := by
  simp only [frequencyMatrix, Matrix.smul_apply, Matrix.add_apply, smul_eq_mul,
    Matrix.diagonal_apply_ne _ hij, add_zero, ← mul_assoc, ← Complex.ofReal_mul,
    kinetic_coefficient c hc, kinetic_offdiag hij]
  split_ifs <;> simp [offDiagonal, neg_div]

/-- On every grid accepted by the reference indexing, the frequency matrix is the
tridiagonal matrix of the exact reference coefficients. -/
theorem frequencyMatrix_eq_reference {n : ℕ} (hn : 2 ≤ n) (c : ℝ) (hc : 0 < c)
    (h : ℝ) (V : Fin n → ℝ) :
    frequencyMatrix (parameters c hc) h V = referenceMatrix h V := by
  ext i j
  by_cases hij : i = j
  · subst j
    by_cases hi : i.val = 0 ∨ i.val+1 = n
    · simpa [referenceMatrix, diagonal, hi] using endpoint_entry hn c hc h V i hi
    · simpa [referenceMatrix, diagonal, hi] using interior_entry hn c hc h V i hi
  · simpa [referenceMatrix, hij] using off_diagonal_entry c hc h V i j hij

/-- Matrix multiplication by the real reference rows gives the physical-frequency
operator on each complex wave, for every positive light speed in the simulation units. -/
theorem reference_mulVec {n : ℕ} (hn : 2 ≤ n) (c : ℝ) (hc : 0 < c)
    (h : ℝ) (V : Fin n → ℝ) (z : Fin n → ℂ) :
    (referenceMatrix h V).mulVec z = frequency (parameters c hc) h V z := by
  rw [← frequencyMatrix_eq_reference hn c hc, frequencyMatrix_mulVec]

end FoliationQM.LatticeNeumannReferenceRows
