module

public import FoliationQM.LatticeUnitaryPropagator
public import FoliationQM.LatticeSchrodingerResidual

/-!
# The exact global trajectory in site coordinates

The Neumann matrix exponential evolves any initial site profile for every real
time. Its site velocities solve the linear Schrödinger equation. Unitarity
preserves the rectangular mass and, because the Hamiltonian commutes with the
propagator, also the geometric energy in v13 Section 2.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.LatticeUnitaryTrajectory

open LatticeNeumannHamiltonian LatticeNeumannMatrix LatticeUnitaryPropagator
open LatticeComplexEnergy LatticeSchrodingerResidual WeightedLatticeHamiltonian
open WithLp
open scoped InnerProductSpace

/-- The unitary trajectory as an ordinary site profile at physical time `t`. -/
def trajectory {n : ℕ} (p : MassiveParameters) (h : ℝ) (V : Fin n → ℝ)
    (z₀ : Fin n → ℂ) (t : ℝ) : Fin n → ℂ :=
  ofLp (propagator p h V t (toLp 2 z₀))

/-- At time zero the trajectory gives the prescribed initial data. -/
theorem trajectory_zero {n : ℕ} (p : MassiveParameters) (h : ℝ) (V : Fin n → ℝ)
    (z₀ : Fin n → ℂ) : trajectory p h V z₀ 0 = z₀ := by
  simp [trajectory, propagator_zero]

open scoped Matrix.Norms.L2Operator in
/-- Site evolution is matrix-vector multiplication by the exponential of −itH. -/
theorem trajectory_matrix_exp {n : ℕ} (p : MassiveParameters) (h : ℝ) (V : Fin n → ℝ)
    (z₀ : Fin n → ℂ) (t : ℝ) :
    trajectory p h V z₀ t =
      (NormedSpace.exp (((t : ℂ) * -Complex.I) • frequencyMatrix p h V)).mulVec z₀ := by
  rw [trajectory, ← matrix_exp_eq_propagator, Matrix.ofLp_toEuclideanCLM, ofLp_toLp]

private theorem ham_sites {n : ℕ} (p : MassiveParameters) (h : ℝ) (V : Fin n → ℝ)
    (x : Space n) : ofLp (ham p h V x) = frequency p h V (ofLp x) := by
  rw [ham, Matrix.ofLp_toEuclideanCLM, frequencyMatrix_mulVec]

/-- Each site of the global trajectory has the physical-frequency Schrödinger velocity. -/
theorem site_ode {n : ℕ} (p : MassiveParameters) (h : ℝ) (V : Fin n → ℝ)
    (z₀ : Fin n → ℂ) (t : ℝ) (i : Fin n) :
    HasDerivAt (fun s => trajectory p h V z₀ s i) (schrodinger p h V (trajectory p h V z₀ t) i) t := by
  let ev : Space n →L[ℝ] ℂ := PiLp.proj 2 (fun _ : Fin n => ℂ) i
  have hd := ev.hasFDerivAt.comp_hasDerivAt t (trajectory_deriv p h V t (toLp 2 z₀))
  apply hd.congr_deriv
  change -Complex.I * ofLp (ham p h V (propagator p h V t (toLp 2 z₀))) i = _
  rw [ham_sites]
  rfl

private theorem pair_as_inner {n : ℕ} (h : ℝ) (u v : Fin n → ℂ) :
    pair h u v = (h : ℂ) * inner ℂ (toLp 2 u) (toLp 2 v) := by
  simp only [pair, EuclideanSpace.inner_toLp_toLp, dotProduct, Pi.star_apply, mul_comm (v _)]

/-- Rectangular inner products between two evolving profiles are constant in time. -/
theorem pair_preserved {n : ℕ} (p : MassiveParameters) (h : ℝ) (V : Fin n → ℝ)
    (u v : Fin n → ℂ) (t : ℝ) :
    pair h (trajectory p h V u t) (trajectory p h V v t) = pair h u v := by
  rw [pair_as_inner, pair_as_inner, trajectory, trajectory, toLp_ofLp, toLp_ofLp,
    propagator_inner]

/-- The rectangular complex mass, including both full endpoint weights, is constant for all real times. -/
theorem mass_preserved {n : ℕ} (p : MassiveParameters) (h : ℝ) (V : Fin n → ℝ)
    (z₀ : Fin n → ℂ) (t : ℝ) :
    h * ∑ i, Complex.normSq (trajectory p h V z₀ t i) = h * ∑ i, Complex.normSq (z₀ i) := by
  have hn := congrArg (fun r : ℝ => r^2) (propagator_norm p h V t (toLp 2 z₀))
  simp only [EuclideanSpace.norm_sq_eq] at hn
  simpa only [Complex.normSq_eq_norm_sq, trajectory] using congrArg (h * ·) hn

/-- Evolving a profile commutes with applying its time-independent Neumann Hamiltonian. -/
theorem frequency_trajectory {n : ℕ} (p : MassiveParameters) (h : ℝ) (V : Fin n → ℝ)
    (z₀ : Fin n → ℂ) (t : ℝ) :
    frequency p h V (trajectory p h V z₀ t) = trajectory p h V (frequency p h V z₀) t := by
  have hc := congrArg (fun T : Space n →L[ℂ] Space n => ofLp (T (toLp 2 z₀)))
    (ham_commute_propagator p h V t).eq
  change ofLp (ham p h V (propagator p h V t (toLp 2 z₀))) =
    ofLp (propagator p h V t (ham p h V (toLp 2 z₀))) at hc
  rw [ham_sites] at hc
  have hv : ham p h V (toLp 2 z₀) = toLp 2 (frequency p h V z₀) :=
    congrArg (toLp 2) (ham_sites p h V (toLp 2 z₀))
  exact hc.trans (congrArg (fun x => ofLp (propagator p h V t x)) hv)

/-- Unitarity and Hamiltonian commutation give exact global conservation of the complex lattice energy. -/
theorem energy_preserved {n : ℕ} (p : MassiveParameters) (h : ℝ) (V : Fin n → ℝ)
    (z₀ : Fin n → ℂ) (t : ℝ) : energy p h (trajectory p h V z₀ t) V = energy p h z₀ V := by
  have he := pair_preserved p h V z₀ (frequency p h V z₀) t
  rw [← frequency_trajectory, frequency_expectation, frequency_expectation] at he
  exact mul_left_cancel₀ (ClockScales.omega0_pos p).ne' (Complex.ofReal_injective he)

/-- Two signed polar representatives of an initial and an evolved wave have equal geometric energies. -/
theorem geometric_preserved {n : ℕ} (p : MassiveParameters) {h : ℝ} (hh : 0 < h)
    (V R₀ φ₀ R φ : Fin n → ℝ) (t : ℝ)
    (hw : wave R φ = trajectory p h V (wave R₀ φ₀) t) :
    geometric p h R φ V = geometric p h R₀ φ₀ V := by
  rw [geometric_eq_energy p hh, geometric_eq_energy p hh, hw, energy_preserved]

end FoliationQM.LatticeUnitaryTrajectory
