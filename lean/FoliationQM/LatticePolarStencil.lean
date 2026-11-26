module

public import FoliationQM.LatticeNeumannHamiltonian

/-!
# Radial and angular components of the replicated complex stencil

The real source equations in v13 lines 215–220 use a forward phase
difference φ₊−φ and a backward difference φ−φ₋. Multiplication by the
conjugate local phase recovers the two real components of the complex
Neumann Hamiltonian directly at signed or zero amplitudes.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.LatticePolarStencil

open LatticeConservation LatticeComplexEnergy LatticeNeumannGreen LatticeNeumannHamiltonian

/-- Radial component of the unscaled Neumann second difference. -/
def radial {n : ℕ} (R φ : Fin n → ℝ) (i : Fin n) : ℝ :=
  R (nextNode i) * Real.cos (φ (nextNode i) - φ i) +
    R (prevNode i) * Real.cos (φ i - φ (prevNode i)) - 2 * R i

/-- Angular component with the forward and backward link orientations from the source. -/
def angular {n : ℕ} (R φ : Fin n → ℝ) (i : Fin n) : ℝ :=
  R (nextNode i) * Real.sin (φ (nextNode i) - φ i) -
    R (prevNode i) * Real.sin (φ i - φ (prevNode i))

/-- Removing the phase at the first site gives the directed phase difference. -/
theorem relative_phase (a b : ℝ) : star (phase a) * phase b = phase (b-a) := by
  simp only [phase, Complex.star_def, ← Complex.exp_conj, map_mul,
    Complex.conj_ofReal, Complex.conj_I, ← Complex.exp_add, Complex.ofReal_sub]
  congr 1
  ring

/-- Local phase rotation is invertible at every amplitude, including a node. -/
theorem unit_phase (a : ℝ) : star (phase a) * phase a = 1 := by
  rw [relative_phase, sub_self]
  simp [phase]

/-- The rotated three-point stencil is the complex number with the displayed
radial and angular coefficients, also on the replicated boundary rows. -/
theorem dephase_laplacian {n : ℕ} (R φ : Fin n → ℝ) (i : Fin n) :
    star (phase (φ i)) * laplacian (wave R φ) i =
      (radial R φ i : ℂ) + Complex.I * (angular R φ i : ℂ) := by
  have hw (j : Fin n) : star (phase (φ i)) * wave R φ j =
      (R j : ℂ) * phase (φ j - φ i) := by
    rw [wave, mul_left_comm, relative_phase]
  have self : star (phase (φ i)) * wave R φ i = (R i : ℂ) := by
    rw [wave, mul_left_comm, unit_phase, mul_one]
  rw [laplacian, mul_add, mul_sub, mul_left_comm _ (2 : ℂ), self, hw, hw]
  rw [show φ (prevNode i) - φ i = -(φ i - φ (prevNode i)) by ring]
  simp only [phase, Complex.exp_ofReal_mul_I, Real.cos_neg, Real.sin_neg]
  simp only [radial, angular, Complex.ofReal_neg, Complex.ofReal_sub,
    Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_ofNat]
  ring

/-- The dephased dimensionless Hamiltonian has real component R·V/(mc²)
minus the kinetic coefficient times the radial stencil, and imaginary
component minus the same coefficient times the angular stencil. -/
theorem dephase_dimless {n : ℕ} (p : MassiveParameters) (h : ℝ) (R φ V : Fin n → ℝ)
    (i : Fin n) :
    star (phase (φ i)) * dimless p h V (wave R φ) i =
      ((R i * (V i / (p.m*p.c^2)) - (p.ellC^2/(2*h^2))*radial R φ i : ℝ) : ℂ) +
        Complex.I * ((-(p.ellC^2/(2*h^2))*angular R φ i : ℝ) : ℂ) := by
  have self : star (phase (φ i)) * wave R φ i = (R i : ℂ) := by
    rw [wave, mul_left_comm, unit_phase, mul_one]
  rw [dimless, mul_add, mul_neg, mul_left_comm _ (Complex.ofReal (p.ellC^2/(2*h^2))),
    dephase_laplacian, mul_left_comm _ (Complex.ofReal (V i/(p.m*p.c^2))), self]
  push_cast
  ring

end FoliationQM.LatticePolarStencil
