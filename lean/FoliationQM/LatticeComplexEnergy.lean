module

public import FoliationQM.WeightedLatticeHamiltonian

/-!
# Complex form of the finite polar energy

The weighted polar Hamiltonian in v13 lines 209–212 is the sum of the
complex forward-difference energy and the site-potential energy. The
rectangular site measure and replicated terminal neighbor are those of
the source dynamics. A half turn at each negative amplitude preserves
the reconstructed wave for every choice of the full-turn phase lift.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.LatticeComplexEnergy

open LatticeConservation WeightedLatticeHamiltonian PolarKahlerLattice

/-- Complex reconstruction of each signed polar lattice site. -/
def wave {n : ℕ} (R φ : Fin n → ℝ) (i : Fin n) : ℂ := (R i : ℂ) * phase (φ i)

/-- The normalized complex lattice energy with rectangular site measure,
replicated forward differences and the physical potential divided by mc². -/
def energy {n : ℕ} (p : MassiveParameters) (h : ℝ) (z : Fin n → ℂ) (V : Fin n → ℝ) : ℝ :=
  h * ∑ i, (p.ellC^2/(2*h^2) * Complex.normSq (z (nextNode i) - z i) +
    V i/(p.m*p.c^2) * Complex.normSq (z i))

/-- The squared modulus of the reconstructed wave is the site density R²,
including at a negative or zero amplitude. -/
theorem wave_normSq {n : ℕ} (R φ : Fin n → ℝ) (i : Fin n) :
    Complex.normSq (wave R φ i) = (R i)^2 := by
  simp only [Complex.normSq_eq_norm_sq, wave, phase, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, Complex.norm_exp_ofReal_mul_I, mul_one, sq_abs]

/-- The full finite geometric Hamiltonian evaluated on arbitrary signed
polar data equals the complex energy of the reconstructed wave. -/
theorem geometric_eq_energy {n : ℕ} (p : MassiveParameters) {h : ℝ} (hh : 0 < h)
    (R φ V : Fin n → ℝ) :
    geometric p h R φ V = energy p h (wave R φ) V := by
  rw [geometric, energy, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [weightedSite, wave_normSq]
  apply congrArg (fun u : ℝ => h*u)
  unfold forwardDiff
  let j := nextNode i
  calc
    _ = p.ellC^2/h^2 * (R j * R i * (1 - Real.cos (φ j - φ i)) + (R j - R i)^2/2) +
        V i/(p.m*p.c^2) * (R i)^2 := by
      dsimp only [j]
      rw [div_pow]
      ring
    _ = _ := by
      rw [geometric_edge_normSq]
      unfold wave
      dsimp only [j]
      field_simp [hh.ne', p.m_pos.ne', p.c_pos.ne']

/-- Choosing positive amplitudes, shifting negative sites by π and changing
the lift by whole turns leaves the complex wave unchanged at every site. -/
theorem wave_canonicalization {n : ℕ} (R φ : Fin n → ℝ) (k : Fin n → ℤ) :
    wave (fun i => |R i|) (fun i =>
      (φ i + Real.pi * (if R i < 0 then 1 else 0)) + (k i : ℝ)*(2*Real.pi)) =
      wave R φ := by
  funext i
  unfold wave
  rw [phase_add_int_mul_two_pi]
  exact (signed_amplitude_canonicalization (R i) (φ i)).symm

/-- Sitewise positive-amplitude canonicalization preserves the full weighted
geometric energy for every potential and every choice of integer phase lifts. -/
theorem canonicalization {n : ℕ} (p : MassiveParameters) {h : ℝ} (hh : 0 < h)
    (R φ V : Fin n → ℝ) (k : Fin n → ℤ) :
    geometric p h (fun i => |R i|) (fun i =>
        (φ i + Real.pi * (if R i < 0 then 1 else 0)) + (k i : ℝ)*(2*Real.pi)) V =
      geometric p h R φ V := by
  rw [geometric_eq_energy p hh, geometric_eq_energy p hh, wave_canonicalization]

end FoliationQM.LatticeComplexEnergy
