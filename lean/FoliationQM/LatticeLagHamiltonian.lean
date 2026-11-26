module

public import FoliationQM.LatticeSiteVariation
public import FoliationQM.LatticeClockRegularization
public import FoliationQM.ClockScales

/-!
# Canonical derivatives in signed amplitude and lag-clock coordinates

The positive lag-phase convention of v13 lines 203–220 converts the
dimensionless phase derivative into the Hamiltonian derivative in the
physical lag coordinate. On the chart where the site amplitude is nonzero,
the two signed one-site derivatives recover the source amplitude rate
and the unregularized lag rate with the rectangular site weight.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.LatticeLagHamiltonian

open LatticeConservation LatticePolarStencil LatticePolarVariation
open LatticeSiteVariation LatticeClockRegularization WeightedLatticeHamiltonian

/-- The dimensionless phase obtained from the source's positive lag-clock convention. -/
def lagPhase {n : ℕ} (p : MassiveParameters) (τ : Fin n → ℝ) (i : Fin n) : ℝ :=
  (p.c / p.ellC) * τ i

/-- The frequency multiplying the lag clock is the Compton angular frequency. -/
theorem omega0_eq_clock_scale (p : MassiveParameters) : p.omega0 = p.c / p.ellC := by
  unfold MassiveParameters.omega0 MassiveParameters.ellC
  field_simp [p.hbar_pos.ne', p.m_pos.ne', p.c_pos.ne']

/-- Multiplying the dimensionless kinetic coefficient by ω₀ gives the source
amplitude equation's kinetic coefficient. -/
theorem omega0_mul_kinetic (p : MassiveParameters) (h : ℝ) :
    p.omega0 * (p.ellC ^ 2 / (2 * h ^ 2)) = p.ellC * p.c / (2 * h ^ 2) := by
  rw [omega0_eq_clock_scale, ← mul_div_assoc]
  congr 1
  field_simp [(ClockScales.ellC_pos p).ne']

/-- A one-site lag shift induces a one-site phase shift with slope c/ℓ_C. -/
theorem lagPhase_siteShift {n : ℕ} (p : MassiveParameters) (τ : Fin n → ℝ)
    (i : Fin n) (s : ℝ) :
    lagPhase p (siteShift τ i s) = siteShift (lagPhase p τ) i ((p.c / p.ellC) * s) := by
  funext j
  unfold lagPhase siteShift
  ring

/-- The literal lag-coordinate derivative of the weighted energy is its phase
gradient multiplied by the lag-to-phase conversion factor. -/
theorem lag_partial {n : ℕ} (p : MassiveParameters) {h : ℝ} (hh : 0 < h)
    (R τ V : Fin n → ℝ) (i : Fin n) :
    HasDerivAt (fun s => geometric p h R (lagPhase p (siteShift τ i s)) V)
      (phaseGradient p h R (lagPhase p τ) i * (p.c / p.ellC)) 0 := by
  have hk : HasDerivAt (fun s : ℝ => (p.c / p.ellC) * s) (p.c / p.ellC) 0 := by
    simpa only [id_eq, mul_one] using (hasDerivAt_id (0 : ℝ)).const_mul (p.c / p.ellC)
  have hp : HasDerivAt (fun u => geometric p h R (siteShift (lagPhase p τ) i u) V)
      (phaseGradient p h R (lagPhase p τ) i) ((p.c / p.ellC) * 0) := by
    simpa only [mul_zero] using phase_partial p hh R (lagPhase p τ) V i
  simpa only [Function.comp_def, lagPhase_siteShift] using hp.comp 0 hk

/-- The lag gradient equals the source amplitude rate times 2hR, also at a zero amplitude. -/
theorem lag_gradient_eq_amplitude_rate {n : ℕ} (p : MassiveParameters) (h : ℝ)
    (R τ : Fin n → ℝ) (i : Fin n) :
    phaseGradient p h R (lagPhase p τ) i * (p.c / p.ellC) =
      2 * h * R i * sourceAmplitudeRHS p.ellC p.c h R (lagPhase p τ) i := by
  unfold phaseGradient sourceAmplitudeRHS angular
  rw [← omega0_eq_clock_scale, ← omega0_mul_kinetic]
  ring

/-- The derivative along a single physical lag shift equals the weighted amplitude rate. -/
theorem lag_partial_amplitude_rate {n : ℕ} (p : MassiveParameters) {h : ℝ} (hh : 0 < h)
    (R τ V : Fin n → ℝ) (i : Fin n) :
    HasDerivAt (fun s => geometric p h R (lagPhase p (siteShift τ i s)) V)
      (2 * h * R i * sourceAmplitudeRHS p.ellC p.c h R (lagPhase p τ) i) 0 := by
  rw [← lag_gradient_eq_amplitude_rate]
  exact lag_partial p hh R τ V i

/-- On a nonzero signed-amplitude chart the radial gradient equals minus 2hR
times the unregularized source lag rate. -/
theorem radial_gradient_eq_lag_rate {n : ℕ} (p : MassiveParameters) (h : ℝ)
    (R τ V : Fin n → ℝ) (i : Fin n) (hi : R i ≠ 0) :
    radialGradient p h R (lagPhase p τ) V i =
      -2 * h * R i * lagRate p h 0 R (lagPhase p τ) V i := by
  rw [radialGradient, lagRate_zero_of_ne p h R (lagPhase p τ) V i hi]
  generalize p.ellC ^ 2 / (2 * h ^ 2) = k
  generalize V i / (p.m * p.c ^ 2) = w
  field_simp [hi]
  ring

/-- Dividing the actual one-site lag derivative by 2hR recovers the source
amplitude rate wherever the signed amplitude is nonzero. -/
theorem canonical_amplitude {n : ℕ} (p : MassiveParameters) {h : ℝ} (hh : 0 < h)
    (R τ V : Fin n → ℝ) (i : Fin n) (hi : R i ≠ 0) :
    sourceAmplitudeRHS p.ellC p.c h R (lagPhase p τ) i =
      deriv (fun s => geometric p h R (lagPhase p (siteShift τ i s)) V) 0 /
        (2 * h * R i) := by
  rw [(lag_partial_amplitude_rate p hh R τ V i).deriv]
  field_simp [hh.ne', hi]

/-- The negative one-site amplitude derivative divided by 2hR recovers the
unregularized source lag rate on the same signed chart. -/
theorem canonical_lag {n : ℕ} (p : MassiveParameters) {h : ℝ} (hh : 0 < h)
    (R τ V : Fin n → ℝ) (i : Fin n) (hi : R i ≠ 0) :
    lagRate p h 0 R (lagPhase p τ) V i =
      -deriv (fun s => geometric p h (siteShift R i s) (lagPhase p τ) V) 0 /
        (2 * h * R i) := by
  rw [(radial_partial p hh R (lagPhase p τ) V i).deriv, radial_gradient_eq_lag_rate p h R τ V i hi]
  field_simp [hh.ne', hi]

end FoliationQM.LatticeLagHamiltonian
