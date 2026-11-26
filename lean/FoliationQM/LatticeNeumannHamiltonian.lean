module

public import FoliationQM.LatticeNeumannGreen
public import FoliationQM.LatticeComplexEnergy
public import Mathlib.Algebra.Star.BigOperators
public import Mathlib.Basic.Complex.BigOperators

/-!
# The Neumann Hamiltonian of the polar lattice

The finite kinetic and potential terms in v13 lines 209–215 define a
Hermitian operator for the rectangular site measure. Its dimensionless
expectation recovers the geometric polar energy. Multiplication by the
Compton frequency gives the operator in angular-frequency units.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.LatticeNeumannHamiltonian

open LatticeNeumannGreen LatticeComplexEnergy
open scoped BigOperators

/-- Rectangular site pairing, conjugate-linear in the first profile. -/
def pair {n : ℕ} (h : ℝ) (u v : Fin n → ℂ) : ℂ :=
  (h : ℂ) * ∑ i, star (u i) * v i

/-- The dimensionless Neumann Hamiltonian with real site potential in units of mc². -/
def dimless {n : ℕ} (p : MassiveParameters) (h : ℝ) (V : Fin n → ℝ)
    (z : Fin n → ℂ) (i : Fin n) : ℂ :=
  -(Complex.ofReal (p.ellC ^ 2 / (2 * h ^ 2)) * laplacian z i) + Complex.ofReal (V i / (p.m * p.c ^ 2)) * z i

/-- The same Hamiltonian in angular-frequency units. -/
def frequency {n : ℕ} (p : MassiveParameters) (h : ℝ) (V : Fin n → ℝ)
    (z : Fin n → ℂ) (i : Fin n) : ℂ :=
  (p.omega0 : ℂ) * dimless p h V z i

/-- Complex conjugation interchanges the arguments of the rectangular site pairing. -/
theorem star_pair {n : ℕ} (h : ℝ) (u v : Fin n → ℂ) :
    star (pair h u v) = pair h v u := by
  have hs (r : ℝ) : star (r : ℂ) = (r : ℂ) := Complex.conj_ofReal r
  simp only [pair, star_mul, star_sum, star_star, hs, mul_comm (h : ℂ)]

/-- A constant complex multiplier in the second profile factors out of the pairing. -/
theorem pair_mul_right {n : ℕ} (h : ℝ) (u v : Fin n → ℂ) (a : ℂ) :
    pair h u (fun i => a * v i) = a * pair h u v := by
  unfold pair
  rw [mul_left_comm a]
  apply congrArg (fun s : ℂ => (h : ℂ) * s)
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => mul_left_comm _ _ _

/-- The mixed Neumann form is the forward-link Dirichlet form plus the real potential term. -/
theorem pair_dimless {n : ℕ} (p : MassiveParameters) (h : ℝ) (V : Fin n → ℝ)
    (u v : Fin n → ℂ) :
    pair h u (dimless p h V v) = (h : ℂ) * ∑ i,
      (Complex.ofReal (p.ellC ^ 2 / (2 * h ^ 2)) * (star (forward u i) * forward v i) +
        Complex.ofReal (V i / (p.m * p.c ^ 2)) * (star (u i) * v i)) := by
  unfold pair dimless
  apply congrArg (fun s : ℂ => (h : ℂ) * s)
  calc
    _ = ∑ i, (Complex.ofReal (p.ellC ^ 2 / (2 * h ^ 2)) * (star (u i) * (-laplacian v i)) +
        Complex.ofReal (V i / (p.m * p.c ^ 2)) * (star (u i) * v i)) := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = _ := by simp only [Finset.sum_add_distrib, ← Finset.mul_sum, green]

/-- The dimensionless Hamiltonian is Hermitian in the rectangular site pairing. -/
theorem dimless_hermitian {n : ℕ} (p : MassiveParameters) (h : ℝ) (V : Fin n → ℝ)
    (u v : Fin n → ℂ) : pair h (dimless p h V u) v = pair h u (dimless p h V v) := by
  rw [← star_pair h v, pair_dimless, pair_dimless]
  have hs (r : ℝ) : star (r : ℂ) = (r : ℂ) := Complex.conj_ofReal r
  simp only [star_mul, star_sum, star_add, star_star, hs]
  rw [mul_comm _ (h : ℂ)]
  apply congrArg (fun s : ℂ => (h : ℂ) * s)
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Multiplying by the real Compton frequency preserves Hermitian symmetry. -/
theorem frequency_hermitian {n : ℕ} (p : MassiveParameters) (h : ℝ) (V : Fin n → ℝ)
    (u v : Fin n → ℂ) : pair h (frequency p h V u) v = pair h u (frequency p h V v) := by
  have hs : star (p.omega0 : ℂ) = (p.omega0 : ℂ) := Complex.conj_ofReal _
  rw [← star_pair h v]
  unfold frequency
  rw [pair_mul_right, pair_mul_right, star_mul, star_pair, hs, dimless_hermitian, mul_comm]

/-- The dimensionless expectation is exactly the real finite complex energy. -/
theorem dimless_expectation {n : ℕ} (p : MassiveParameters) (h : ℝ) (V : Fin n → ℝ)
    (z : Fin n → ℂ) : pair h z (dimless p h V z) = (energy p h z V : ℂ) := by
  have hsq (x : ℂ) : star x * x = (Complex.normSq x : ℂ) := by
    rw [mul_comm, Complex.star_def, Complex.mul_conj]
  simp only [pair_dimless, energy, forward, hsq, Complex.ofReal_mul,
    Complex.ofReal_sum, Complex.ofReal_add]

/-- In angular-frequency units the expectation acquires the factor ω₀. -/
theorem frequency_expectation {n : ℕ} (p : MassiveParameters) (h : ℝ) (V : Fin n → ℝ)
    (z : Fin n → ℂ) : pair h z (frequency p h V z) = (p.omega0 * energy p h z V : ℝ) := by
  unfold frequency
  rw [pair_mul_right, dimless_expectation, Complex.ofReal_mul]

/-- Multiplying the frequency expectation by ℏ gives the physical energy in units of mc². -/
theorem physical_expectation {n : ℕ} (p : MassiveParameters) (h : ℝ) (V : Fin n → ℝ)
    (z : Fin n → ℂ) : (p.hbar : ℂ) * pair h z (frequency p h V z) =
      (p.m * p.c ^ 2 * energy p h z V : ℝ) := by
  rw [frequency_expectation, ← Complex.ofReal_mul, ← mul_assoc]
  have hscale : p.hbar * p.omega0 = p.m * p.c ^ 2 := by
    unfold MassiveParameters.omega0
    field_simp [p.hbar_pos.ne']
  rw [hscale]

/-- The source's normalized geometric Hamiltonian is the Neumann expectation of its signed wave. -/
theorem geometric_expectation {n : ℕ} (p : MassiveParameters) {h : ℝ} (hh : 0 < h)
    (R φ V : Fin n → ℝ) : pair h (wave R φ) (dimless p h V (wave R φ)) =
      (WeightedLatticeHamiltonian.geometric p h R φ V : ℂ) := by
  rw [dimless_expectation, geometric_eq_energy p hh]

end FoliationQM.LatticeNeumannHamiltonian
