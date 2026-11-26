module

public import FoliationQM.LatticeNeumannHamiltonian
public import Mathlib.Analysis.Calculus.Deriv.Star
public import Mathlib.Analysis.Complex.RealDeriv

/-!
# First variation of the finite Neumann energy

For a time-independent real potential and rectangular mesh measure, the
derivative of the normalized lattice energy in v13 lines 209–215 along
a complex profile is twice its velocity's real pairing with the Neumann
Hamiltonian applied to the profile.
-/

@[expose] public section
namespace FoliationQM.LatticeEnergyDifferential

open LatticeConservation LatticeNeumannGreen LatticeNeumannHamiltonian LatticeComplexEnergy

/-- Product rule for the rectangular pairing of two differentiable complex profiles. -/
theorem pair_path {n : ℕ} (h : ℝ) (u v : ℝ → Fin n → ℂ) (du dv : Fin n → ℂ) (t : ℝ)
    (hu : ∀ i, HasDerivAt (fun s => u s i) (du i) t)
    (hv : ∀ i, HasDerivAt (fun s => v s i) (dv i) t) :
    HasDerivAt (fun s => pair h (u s) (v s)) (pair h du (v t) + pair h (u t) dv) t := by
  unfold pair
  rw [← mul_add, ← Finset.sum_add_distrib]
  apply HasDerivAt.const_mul
  apply HasDerivAt.fun_sum
  intro i _
  exact (hu i).star.mul (hv i)

/-- The derivative of the fixed Neumann Hamiltonian along a path is the Hamiltonian
applied to the path velocity, site by site, including the replicated endpoints. -/
theorem dimless_path {n : ℕ} (p : MassiveParameters) (h : ℝ) (V : Fin n → ℝ)
    (z : ℝ → Fin n → ℂ) (d : Fin n → ℂ) (t : ℝ)
    (hz : ∀ i, HasDerivAt (fun s => z s i) (d i) t) (i : Fin n) :
    HasDerivAt (fun s => dimless p h V (z s) i) (dimless p h V d i) t := by
  have hL := ((hz (nextNode i)).sub ((hz i).const_mul (2 : ℂ))).add (hz (prevNode i))
  exact ((hL.const_mul _).neg).add ((hz i).const_mul _)

/-- First variation of the real finite energy for an arbitrary sitewise differentiable
complex curve, with fixed mesh and potential and unrestricted site amplitudes. -/
theorem energy_path {n : ℕ} (p : MassiveParameters) (h : ℝ) (V : Fin n → ℝ)
    (z : ℝ → Fin n → ℂ) (d : Fin n → ℂ) (t : ℝ)
    (hz : ∀ i, HasDerivAt (fun s => z s i) (d i) t) :
    HasDerivAt (fun s => energy p h (z s) V) (2 * (pair h d (dimless p h V (z t))).re) t := by
  have hp := pair_path h z (fun s => dimless p h V (z s)) d (dimless p h V d) t hz
    (dimless_path p h V z d t hz)
  have hsym : (pair h (z t) (dimless p h V d)).re = (pair h d (dimless p h V (z t))).re := by
    rw [← dimless_hermitian, ← star_pair, Complex.star_def, Complex.conj_re]
  simpa only [Function.comp_def, Complex.reCLM_apply, dimless_expectation,
    Complex.ofReal_re, Complex.add_re, hsym, two_mul] using
    Complex.reCLM.hasFDerivAt.comp_hasDerivAt t hp

end FoliationQM.LatticeEnergyDifferential
