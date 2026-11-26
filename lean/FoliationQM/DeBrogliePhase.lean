module

public import FoliationQM.LorentzCoordinates
public import Mathlib.Analysis.Calculus.FDeriv.Linear
public import Mathlib.Analysis.Calculus.FDeriv.Add

/-!
# Uniform-boost de Broglie phase and its actual differential

Source: v13 `prop:debroglie`, particularly its uniform-boost integration,
de Broglie wavelength, and exact rest-energy/simultaneity cancellation.
Spatial magnitude always means the explicit positive Euclidean square root
from `LorentzCoordinates`, never the function-space norm. Real parameter
formulas permit actual limits in c; positivity and subluminality are stated
where physical nonzero momentum and positive wavelength are asserted.
The wavelength formula uses total division outside that physical domain.
-/

@[expose] public section
noncomputable section

namespace FoliationQM.DeBrogliePhase
open LorentzCoordinates

/-- Laboratory spacetime coordinates with time measured in seconds. -/
abbrev Spacetime := ℝ × Spatial

/-- The spatial relativistic momentum of a uniform laboratory velocity. -/
def momentum (m c : ℝ) (v : Spatial) : Spatial := (gamma c v * m) • v

/-- The positive-energy relativistic energy on the physical subluminal domain. -/
def energy (m c : ℝ) (v : Spatial) : ℝ := gamma c v * m * c ^ 2

/-- The de Broglie spatial wave vector, momentum divided by the action scale. -/
def waveVector (m c h : ℝ) (v : Spatial) : Spatial := h⁻¹ • momentum m c v

/-- The uniform-boost phase as an actual scalar function of laboratory time and position. -/
def phase (m c h : ℝ) (v : Spatial) (tx : Spacetime) : ℝ :=
  (spatialDot (momentum m c v) tx.2 - energy m c v * tx.1) / h

/-- Euclidean pairing with a fixed spatial vector as an actual continuous linear map. -/
def spatialLinear (p : Spatial) : Spatial →L[ℝ] ℝ :=
  p 0 • ContinuousLinearMap.proj 0 + p 1 • ContinuousLinearMap.proj 1 +
    p 2 • ContinuousLinearMap.proj 2

/-- The actual continuous linear laboratory phase differential. -/
def phaseLinear (m c h : ℝ) (v : Spatial) : Spacetime →L[ℝ] ℝ :=
  h⁻¹ • ((spatialLinear (momentum m c v)).comp (ContinuousLinearMap.snd ℝ ℝ Spatial) -
    energy m c v • ContinuousLinearMap.fst ℝ ℝ Spatial)

/-- The spatial Euclidean gradient, defined from actual coordinate derivatives of the phase. -/
def spatialGradient (m c h : ℝ) (v x : Spatial) (t : ℝ) : Spatial :=
  fun i => fderiv ℝ (fun y => phase m c h v (t, y)) x (Pi.single i 1)

/-- The Euclidean de Broglie wavelength; its physical positivity requires nonzero wave vector. -/
def wavelength (m c h : ℝ) (v : Spatial) : ℝ :=
  2 * Real.pi / euclideanSpeed (waveVector m c h v)

/-- The proper-clock projection of a uniform boost, including its simultaneity tilt. -/
def clockProjection (c : ℝ) (v : Spatial) (tx : Spacetime) : ℝ :=
  gamma c v * (tx.1 - spatialDot v tx.2 / c ^ 2)

/-- The rest-energy clock frequency for real varying parameters. -/
def frequency (m c h : ℝ) : ℝ := m * c ^ 2 / h

/-- A spatial momentum component has the source factor gamma times mass times velocity. -/
theorem momentum_apply (m c : ℝ) (v : Spatial) (i : Fin 3) :
    momentum m c v i = gamma c v * m * v i := rfl

/-- A wave-vector component is the corresponding momentum component divided by the action scale. -/
theorem waveVector_apply (m c h : ℝ) (v : Spatial) (i : Fin 3) :
    waveVector m c h v i = momentum m c v i / h := by
  simp [waveVector, div_eq_mul_inv, mul_comm]

/-- The bundled spatial linear map is the explicit Euclidean dot product. -/
theorem spatialLinear_apply (p x : Spatial) : spatialLinear p x = spatialDot p x := by
  simp [spatialLinear, spatialDot]

/-- The phase is the function underlying its displayed continuous linear map. -/
theorem phaseLinear_apply (m c h : ℝ) (v : Spatial) (tx : Spacetime) :
    phaseLinear m c h v tx = phase m c h v tx := by
  simp [phaseLinear, spatialLinear_apply, phase, div_eq_mul_inv]
  ring

/-- The actual Frechet derivative of the uniform phase is its continuous linear phase map. -/
theorem hasFDerivAt_phase (m c h : ℝ) (v : Spatial) (tx : Spacetime) :
    HasFDerivAt (phase m c h v) (phaseLinear m c h v) tx := by
  have heq : phase m c h v = phaseLinear m c h v :=
    funext fun y => (phaseLinear_apply m c h v y).symm
  rw [heq]
  exact (phaseLinear m c h v).hasFDerivAt

/-- Identify Mathlib's actual phase derivative with the continuous linear phase map. -/
theorem fderiv_phase (m c h : ℝ) (v : Spatial) (tx : Spacetime) :
    fderiv ℝ (phase m c h v) tx = phaseLinear m c h v :=
  (hasFDerivAt_phase m c h v tx).fderiv

/-- The actual phase differential is (momentum dot dx minus energy dt) divided by hbar. -/
theorem fderiv_phase_apply (m c h : ℝ) (v : Spatial) (tx dtx : Spacetime) :
    fderiv ℝ (phase m c h v) tx dtx =
      (spatialDot (momentum m c v) dtx.2 - energy m c v * dtx.1) / h := by
  rw [fderiv_phase, phaseLinear_apply]
  rfl

/-- The fixed-time phase has its actual spatial derivative given by Euclidean pairing with the wave vector. -/
theorem hasFDerivAt_spatialPhase (m c h : ℝ) (v x : Spatial) (t : ℝ) :
    HasFDerivAt (fun y => phase m c h v (t, y)) (spatialLinear (waveVector m c h v)) x := by
  have heq : (fun y => phase m c h v (t, y)) =
      fun y => spatialLinear (waveVector m c h v) y - energy m c v * t / h := by
    funext y
    simp [phase, spatialLinear_apply, waveVector, spatialDot, div_eq_mul_inv]
    ring
  rw [heq]
  simpa only [sub_eq_add_neg] using
    (spatialLinear (waveVector m c h v)).hasFDerivAt.add_const (-(energy m c v * t / h))

/-- The actual fixed-time spatial derivative is the Euclidean dot product with the wave vector. -/
theorem fderiv_spatialPhase_apply (m c h : ℝ) (v x dx : Spatial) (t : ℝ) :
    fderiv ℝ (fun y => phase m c h v (t, y)) x dx =
      spatialDot (waveVector m c h v) dx := by
  rw [(hasFDerivAt_spatialPhase m c h v x t).fderiv, spatialLinear_apply]

/-- The actual Euclidean coordinate gradient is precisely the de Broglie wave vector. -/
theorem spatialGradient_eq_waveVector (m c h : ℝ) (v x : Spatial) (t : ℝ) :
    spatialGradient m c h v x t = waveVector m c h v := by
  ext i
  rw [spatialGradient, fderiv_spatialPhase_apply]
  fin_cases i <;> simp [spatialDot]

/-- The actual spatial phase derivative is Euclidean pairing with its coordinate gradient. -/
theorem spatialGradient_represents_derivative (m c h : ℝ) (v x dx : Spatial) (t : ℝ) :
    fderiv ℝ (fun y => phase m c h v (t, y)) x dx =
      spatialDot (spatialGradient m c h v x t) dx := by
  rw [spatialGradient_eq_waveVector, fderiv_spatialPhase_apply]

/-- The explicit Euclidean square sum scales quadratically under scalar multiplication. -/
theorem speedSq_smul (a : ℝ) (v : Spatial) : speedSq (a • v) = a ^ 2 * speedSq v := by
  simp [speedSq, spatialDot]
  ring

/-- The actual Euclidean magnitude scales by the absolute value of the scalar. -/
theorem euclideanSpeed_smul (a : ℝ) (v : Spatial) :
    euclideanSpeed (a • v) = |a| * euclideanSpeed v := by
  rw [euclideanSpeed, speedSq_smul, Real.sqrt_mul (sq_nonneg a), Real.sqrt_sq_eq_abs]
  rfl

/-- The explicit Euclidean magnitude vanishes exactly at the zero spatial vector. -/
theorem euclideanSpeed_eq_zero_iff (v : Spatial) : euclideanSpeed v = 0 ↔ v = 0 := by
  constructor
  · intro h
    apply (speedSq_eq_zero_iff v).mp
    rw [← euclideanSpeed_sq v, h, zero_pow (by decide : 2 ≠ 0)]
  · rintro rfl
    simp [euclideanSpeed, speedSq, spatialDot]

/-- A nonzero spatial vector has strictly positive actual Euclidean magnitude. -/
theorem euclideanSpeed_pos {v : Spatial} (hv : v ≠ 0) : 0 < euclideanSpeed v := by
  have hn : 0 ≤ euclideanSpeed v := Real.sqrt_nonneg _
  exact lt_of_le_of_ne hn (fun h => hv ((euclideanSpeed_eq_zero_iff v).mp h.symm))

/-- On the massive subluminal domain, momentum magnitude is gamma times mass times Euclidean speed. -/
theorem momentum_magnitude {m c : ℝ} {v : Spatial} (hm : 0 < m) (hc : 0 < c)
    (hv : speedSq v < c ^ 2) :
    euclideanSpeed (momentum m c v) = gamma c v * m * euclideanSpeed v := by
  rw [momentum, euclideanSpeed_smul, abs_of_pos (mul_pos (gamma_pos hc hv) hm)]

/-- Positive action scale divides the actual Euclidean momentum magnitude to give wave-vector magnitude. -/
theorem waveVector_magnitude (m c : ℝ) {h : ℝ} (hh : 0 < h) (v : Spatial) :
    euclideanSpeed (waveVector m c h v) = euclideanSpeed (momentum m c v) / h := by
  rw [waveVector, euclideanSpeed_smul, abs_of_pos (inv_pos.mpr hh)]
  ring

/-- A massive subluminal nonzero velocity has nonzero spatial momentum. -/
theorem momentum_ne_zero {m c : ℝ} {v : Spatial} (hm : 0 < m) (hc : 0 < c)
    (hv : speedSq v < c ^ 2) (hv0 : v ≠ 0) : momentum m c v ≠ 0 :=
  smul_ne_zero (mul_ne_zero (gamma_pos hc hv).ne' hm.ne') hv0

/-- A positive action scale preserves nonzero spatial wave vector for nonzero massive subluminal velocity. -/
theorem waveVector_ne_zero {m c h : ℝ} {v : Spatial} (hm : 0 < m) (hc : 0 < c)
    (hh : 0 < h) (hv : speedSq v < c ^ 2) (hv0 : v ≠ 0) : waveVector m c h v ≠ 0 :=
  smul_ne_zero (inv_ne_zero hh.ne') (momentum_ne_zero hm hc hv hv0)

/-- The actual energy is positive on the massive subluminal physical domain. -/
theorem energy_pos {m c : ℝ} {v : Spatial} (hm : 0 < m) (hc : 0 < c)
    (hv : speedSq v < c ^ 2) : 0 < energy m c v :=
  mul_pos (mul_pos (gamma_pos hc hv) hm) (sq_pos_of_pos hc)

/-- The de Broglie wavelength identity uses actual Euclidean momentum and wave-vector magnitudes. -/
theorem wavelength_eq (m c : ℝ) {h : ℝ} (hh : 0 < h) (v : Spatial) :
    wavelength m c h v = 2 * Real.pi * h / euclideanSpeed (momentum m c v) := by
  rw [wavelength, waveVector_magnitude m c hh v]
  simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
  ring

/-- The actual de Broglie wavelength is strictly positive for nonzero massive subluminal velocity. -/
theorem wavelength_pos {m c h : ℝ} {v : Spatial} (hm : 0 < m) (hc : 0 < c)
    (hh : 0 < h) (hv : speedSq v < c ^ 2) (hv0 : v ≠ 0) :
    0 < wavelength m c h v :=
  div_pos Real.two_pi_pos (euclideanSpeed_pos (waveVector_ne_zero hm hc hh hv hv0))

/-- The projected clock is the already proved proper-time form evaluated on the laboratory displacement. -/
theorem clockProjection_eq_properTime {c : ℝ} (hc : 0 < c) (v : Spatial) (tx : Spacetime) :
    clockProjection c v tx = properTime c v (displacement c tx.1 tx.2) := by
  rw [properTime_displacement hc]
  rfl

/-- The uniform-boost phase equals minus the rest clock frequency times the actual projected clock. -/
theorem phase_eq_negative_clock {c : ℝ} (hc : 0 < c) (m h : ℝ) (v : Spatial) (tx : Spacetime) :
    phase m c h v tx = -frequency m c h * clockProjection c v tx := by
  simp [phase, momentum, energy, frequency, clockProjection, spatialDot]
  field_simp
  ring

/-- The frequency formula agrees with the project's derived positive physical Compton frequency. -/
theorem frequency_parameters (p : MassiveParameters) : frequency p.m p.c p.hbar = p.omega0 := rfl

/-- The rest-energy factor cancels the exact inverse-c-squared simultaneity factor in the wave vector. -/
theorem rest_energy_tilt_cancellation {c : ℝ} (hc : 0 < c) (m h : ℝ) (v : Spatial) :
    (m * c ^ 2 / h) • ((gamma c v / c ^ 2) • v) = waveVector m c h v := by
  ext i
  simp [waveVector, momentum]
  field_simp

end FoliationQM.DeBrogliePhase
