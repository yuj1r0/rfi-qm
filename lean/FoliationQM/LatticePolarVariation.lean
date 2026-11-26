module

public import FoliationQM.LatticeEnergyDifferential
public import FoliationQM.LatticePolarStencil
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.Complex.RealDeriv

/-!
# First variation of the finite polar Hamiltonian

The complex Neumann energy differentiates along any differentiable signed-amplitude
and phase path. Resolving its gradient into the radial and angular directions gives
the two site derivatives of the geometric Hamiltonian, with the rectangular site
weight and the replicated endpoint stencils from v13 lines 209–215.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.LatticePolarVariation

open LatticeComplexEnergy LatticeNeumannHamiltonian LatticePolarStencil
open WeightedLatticeHamiltonian

/-- Derivative of the complex unit phase along a real phase path. -/
theorem phase_path {φ : ℝ → ℝ} {dφ t : ℝ} (hφ : HasDerivAt φ dφ t) :
    HasDerivAt (fun s => phase (φ s)) (phase (φ t) * ((dφ : ℂ) * Complex.I)) t :=
  (hφ.ofReal_comp.mul_const Complex.I).cexp

/-- The time derivative of the reconstructed polar wave at a site, including nodes. -/
theorem wave_path {n : ℕ} (R φ : ℝ → Fin n → ℝ) (t : ℝ) (i : Fin n)
    {dR dφ : ℝ} (hR : HasDerivAt (fun s => R s i) dR t)
    (hφ : HasDerivAt (fun s => φ s i) dφ t) :
    HasDerivAt (fun s => wave (R s) (φ s) i)
      (phase (φ t i) * ((dR : ℂ) + Complex.I * ((R t i * dφ : ℝ) : ℂ))) t := by
  apply (hR.ofReal_comp.mul (phase_path hφ)).congr_deriv
  rw [Complex.ofReal_mul]
  ring

/-- Site coefficient of the signed amplitude variation in the normalized Hamiltonian. -/
def radialGradient {n : ℕ} (p : MassiveParameters) (h : ℝ) (R φ V : Fin n → ℝ) (i : Fin n) : ℝ :=
  2 * h * (R i * (V i / (p.m * p.c^2)) - p.ellC^2 / (2 * h^2) * radial R φ i)

/-- Site coefficient of the dimensionless phase variation in the normalized Hamiltonian. -/
def phaseGradient {n : ℕ} (p : MassiveParameters) (h : ℝ) (R φ : Fin n → ℝ) (i : Fin n) : ℝ :=
  -2 * h * (p.ellC^2 / (2 * h^2)) * R i * angular R φ i

private theorem re_conj_mul (a b c d : ℝ) :
    (star ((a : ℂ) + Complex.I * b) * ((c : ℂ) + Complex.I * d)).re = a*c + b*d := by
  simp [Complex.mul_re, Complex.mul_im]

/-- Along an arbitrary differentiable signed polar path, the energy derivative is the
sum of the radial and phase gradients applied to their respective site velocities. -/
theorem geometric_path {n : ℕ} (p : MassiveParameters) {h : ℝ} (hh : 0 < h)
    (R φ : ℝ → Fin n → ℝ) (V dR dφ : Fin n → ℝ) (t : ℝ)
    (hR : ∀ i, HasDerivAt (fun s => R s i) (dR i) t)
    (hφ : ∀ i, HasDerivAt (fun s => φ s i) (dφ i) t) :
    HasDerivAt (fun s => geometric p h (R s) (φ s) V)
      (∑ i, (radialGradient p h (R t) (φ t) V i * dR i +
        phaseGradient p h (R t) (φ t) i * dφ i)) t := by
  let dz (i : Fin n) := phase (φ t i) * ((dR i : ℂ) + Complex.I * ((R t i * dφ i : ℝ) : ℂ))
  have hd (i : Fin n) : HasDerivAt (fun s => wave (R s) (φ s) i) (dz i) t :=
    wave_path R φ t i (hR i) (hφ i)
  simp_rw [geometric_eq_energy p hh]
  apply (LatticeEnergyDifferential.energy_path p h V (fun s => wave (R s) (φ s)) dz t hd).congr_deriv
  rw [pair, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    sub_zero, Complex.re_sum]
  rw [← mul_assoc, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  unfold dz
  rw [star_mul, mul_assoc _ (star (phase (φ t i))), dephase_dimless, re_conj_mul]
  unfold radialGradient phaseGradient
  ring

end FoliationQM.LatticePolarVariation
