module

public import FoliationQM.LatticeLagHamiltonian

/-!
# Changing signed polar representatives

The source solver may represent the same wave using the opposite amplitude
and a half-turn of the local phase. Each site can make this choice independently.
The dephased second difference transforms with the sign at the observation site.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.LatticePolarSignChange

open LatticeComplexEnergy LatticePolarStencil LatticeConservation PolarKahlerLattice

/-- Reverse the signed amplitude at exactly the selected sites. -/
def amplitude {n : ℕ} (flip : Fin n → Bool) (R : Fin n → ℝ) (i : Fin n) : ℝ :=
  if flip i then -R i else R i

/-- Add a half turn to the phase at each selected site. -/
def angle {n : ℕ} (flip : Fin n → Bool) (φ : Fin n → ℝ) (i : Fin n) : ℝ :=
  if flip i then φ i + Real.pi else φ i

/-- Simultaneous local amplitude and phase changes preserve the reconstructed wave. -/
theorem wave_change {n : ℕ} (flip : Fin n → Bool) (R φ : Fin n → ℝ) :
    wave (amplitude flip R) (angle flip φ) = wave R φ := by
  funext i
  cases hf : flip i <;> simp [wave, amplitude, angle, hf, phase_add_pi]

/-- Both real coefficients of the rotated Neumann stencil transform with the
local sign, even if adjacent sites choose different representatives. -/
theorem stencil_change {n : ℕ} (flip : Fin n → Bool) (R φ : Fin n → ℝ) (i : Fin n) :
    radial (amplitude flip R) (angle flip φ) i = amplitude flip (radial R φ) i ∧
    angular (amplitude flip R) (angle flip φ) i = amplitude flip (angular R φ) i := by
  have h := dephase_laplacian (amplitude flip R) (angle flip φ) i
  rw [wave_change] at h
  cases hf : flip i
  · simp only [angle, hf, Bool.false_eq_true, ite_false, dephase_laplacian] at h
    constructor
    · simpa [Complex.mul_re, amplitude, hf] using congrArg Complex.re h.symm
    · simpa [Complex.mul_im, amplitude, hf] using congrArg Complex.im h.symm
  · simp only [angle, hf, ite_true, phase_add_pi, star_neg, neg_mul, dephase_laplacian] at h
    constructor
    · simpa [Complex.mul_re, amplitude, hf] using congrArg Complex.re h.symm
    · simpa [Complex.mul_im, amplitude, hf] using congrArg Complex.im h.symm

/-- The amplitude velocity changes sign precisely where the amplitude changes sign. -/
theorem amplitude_rate_change {n : ℕ} (flip : Fin n → Bool) (p : MassiveParameters)
    (h : ℝ) (R φ : Fin n → ℝ) (i : Fin n) :
    sourceAmplitudeRHS p.ellC p.c h (amplitude flip R) (angle flip φ) i =
      amplitude flip (sourceAmplitudeRHS p.ellC p.c h R φ) i := by
  change _ * angular (amplitude flip R) (angle flip φ) i = _
  rw [(stencil_change flip R φ i).2]
  cases hf : flip i <;> simp [amplitude, hf, sourceAmplitudeRHS, angular]
  ring

/-- The regularized lag velocity is invariant under independent changes of signed
representative because its kinetic term contains both odd factors. -/
theorem lag_rate_change {n : ℕ} (flip : Fin n → Bool) (p : MassiveParameters)
    (h ε : ℝ) (R φ V : Fin n → ℝ) (i : Fin n) :
    LatticeClockRegularization.lagRate p h ε (amplitude flip R) (angle flip φ) V i =
      LatticeClockRegularization.lagRate p h ε R φ V i := by
  unfold LatticeClockRegularization.lagRate
  rw [(stencil_change flip R φ i).1]
  cases hf : flip i <;> simp [amplitude, hf, LatticeClockRegularization.reciprocal]
  ring

/-- In the solver's positive lag convention, adding half the clock period is
exactly the half turn used to reconstruct a negative signed amplitude. -/
theorem lag_half_period {n : ℕ} (flip : Fin n → Bool) (p : MassiveParameters) (τ : Fin n → ℝ) :
    LatticeLagHamiltonian.lagPhase p (fun i => if flip i then τ i + p.period / 2 else τ i) =
      angle flip (LatticeLagHamiltonian.lagPhase p τ) := by
  have turn : (p.c / p.ellC) * (p.period / 2) = Real.pi := by
    unfold MassiveParameters.ellC MassiveParameters.period
    field_simp [p.m_pos.ne', p.c_pos.ne', p.hbar_pos.ne']
  funext i
  cases hf : flip i <;> simp [angle, hf, LatticeLagHamiltonian.lagPhase, mul_add, turn]

end FoliationQM.LatticePolarSignChange
