module
public import FoliationQM.RotorODE
public import FoliationQM.RotorUnitary
public import FoliationQM.PlaneTetrad
public import FoliationQM.RotorPeriods
public import FoliationQM.RotorClocks
public import Mathlib.Tactic.NoncommRing

/-!
# Actual rotor evolution from an arbitrary invertible initial frame

Sources: v13 `eq:rotor_compton_evolution`, `thm:contact_period` (iii), and
the constant-plane specialization of `lem:maurer_cartan`.
The frame uses the actual evolved matrix and its actual nonsingular inverse.
Matrix conjugation transfers the Clifford relations and, under initial
invertibility, transfers the entire period set. The arbitrary initial matrix
need not have a real Lorentz coefficient expansion; no such expansion or
full spin-group classification is asserted by this module.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.RotorFrameEvolution
open DiracMatrices PlaneRotor RotorEvolution

/-- Actual conjugation by a complex matrix using its nonsingular inverse. -/
def conjugate (A X : Mat) : Mat := A * X * A⁻¹

/-- Conjugation by an invertible matrix is injective on actual matrices. -/
theorem conjugate_injective {A : Mat} (hA : IsUnit A) : Function.Injective (conjugate A) := by
  intro X Y h
  have hi := Matrix.nonsing_inv_mul A ((Matrix.isUnit_iff_isUnit_det A).mp hA)
  have undo (X : Mat) : A⁻¹ * (conjugate A X) * A = X := by
    calc
      _ = (A⁻¹ * A) * X * (A⁻¹ * A) := by unfold conjugate; noncomm_ring
      _ = X := by rw [hi]; simp
  have he := congrArg (fun B : Mat => A⁻¹ * B * A) h
  simpa only [undo] using he

/-- Actual matrix conjugation preserves addition. -/
theorem conjugate_add (A X Y : Mat) : conjugate A (X+Y) = conjugate A X+conjugate A Y := by
  simp [conjugate, mul_add, add_mul]

/-- Actual matrix conjugation preserves complex scalar multiplication. -/
theorem conjugate_smul (A X : Mat) (z : ℂ) : conjugate A (z • X) = z • conjugate A X := by
  simp [conjugate]

/-- Conjugation by an invertible matrix fixes the identity. -/
theorem conjugate_one {A : Mat} (hA : IsUnit A) : conjugate A 1 = 1 := by
  simpa [conjugate] using Matrix.mul_nonsing_inv A ((Matrix.isUnit_iff_isUnit_det A).mp hA)

/-- Conjugation by an invertible matrix preserves matrix multiplication. -/
theorem conjugate_mul {A : Mat} (hA : IsUnit A) (X Y : Mat) :
    conjugate A (X*Y) = conjugate A X * conjugate A Y := by
  have hi := Matrix.nonsing_inv_mul A ((Matrix.isUnit_iff_isUnit_det A).mp hA)
  calc
    _ = A * X * (A⁻¹ * A) * Y * A⁻¹ := by rw [hi]; simp [conjugate, mul_assoc]
    _ = _ := by unfold conjugate; noncomm_ring

/-- The actual evolved gamma frame formed from the evolved matrix and its actual inverse. -/
def frame (L0 : Mat) (omega t : ℝ) (a : Fin 4) : Mat :=
  conjugate (evolution L0 omega t) (gamma a)

/-- The actual evolved frame satisfies the Clifford relation for every invertible initial matrix. -/
theorem frame_clifford {L0 : Mat} (hL0 : IsUnit L0) (omega t : ℝ) (a b : Fin 4) :
    frame L0 omega t a * frame L0 omega t b + frame L0 omega t b * frame L0 omega t a =
      (2 * eta a b) • (1 : Mat) := by
  have h := evolution_isUnit hL0 omega t
  simp only [frame, ← conjugate_mul h, ← conjugate_add, clifford, conjugate_smul,
    conjugate_one h]

/-- An invertible initial matrix preserves the exact period set of the actual rotor evolution. -/
theorem evolution_periodic_iff {L0 : Mat} (hL0 : IsUnit L0) (omega T : ℝ) :
    Function.Periodic (evolution L0 omega) T ↔
      Function.Periodic (fun t => rotor (omega*t/2)) T := by
  constructor
  · intro h t
    exact hL0.mul_left_cancel (h t)
  · intro h t
    exact congrArg (fun A : Mat => L0*A) (h t)

/-- The actual evolved frame equals the normalized plane tetrad conjugated by the initial matrix. -/
theorem frame_eq_initial_conjugation (L0 : Mat) (omega t : ℝ) (a : Fin 4) :
    frame L0 omega t a = conjugate L0 (PlaneTetrad.tetrad (omega*t/2) a) := by
  simp only [frame, conjugate, evolution, Matrix.mul_inv_rev, RotorExponential.rotor_inv,
    PlaneTetrad.tetrad]
  noncomm_ring

/-- An invertible initial frame preserves the exact period set of the actual full tetrad family. -/
theorem frame_periodic_iff {L0 : Mat} (hL0 : IsUnit L0) (omega T : ℝ) :
    Function.Periodic (frame L0 omega) T ↔
      Function.Periodic (fun t => PlaneTetrad.tetrad (omega*t/2)) T := by
  constructor
  · intro h t
    funext a
    apply conjugate_injective hL0
    simpa only [frame_eq_initial_conjugation] using congr_fun (h t) a
  · intro h t
    funext a
    simp only [frame_eq_initial_conjugation]
    exact congrArg (conjugate L0) (congr_fun (h t) a)

/-- At nonzero rate, the exact periods of every invertible-initial evolution are integer multiples of 4*pi/omega. -/
theorem evolution_periodic_exact {L0 : Mat} (hL0 : IsUnit L0) {omega : ℝ}
    (hω : omega ≠ 0) (T : ℝ) :
    Function.Periodic (evolution L0 omega) T ↔ ∃ n : ℤ, T = (n : ℝ)*(4*Real.pi/omega) := by
  rw [evolution_periodic_iff hL0, RotorPeriods.scaled_rotor_periodic_iff hω]

/-- At nonzero rate, the actual full evolved frame periods are exactly integer multiples of 2*pi/omega. -/
theorem frame_periodic_exact {L0 : Mat} (hL0 : IsUnit L0) {omega : ℝ}
    (hω : omega ≠ 0) (T : ℝ) :
    Function.Periodic (frame L0 omega) T ↔ ∃ n : ℤ, T = (n : ℝ)*(2*Real.pi/omega) := by
  rw [frame_periodic_iff hL0, RotorPeriods.scaled_tetrad_periodic_iff hω]

/-- Every invertible-initial rotor evolution at positive rate has least positive period 4*pi/omega. -/
theorem evolution_least_positive_period {L0 : Mat} (hL0 : IsUnit L0) {omega : ℝ}
    (hω : 0 < omega) :
    IsLeast {T : ℝ | 0<T ∧ Function.Periodic (evolution L0 omega) T} (4*Real.pi/omega) := by
  simpa only [evolution_periodic_iff hL0] using RotorPeriods.scaled_rotor_least_positive_period hω

/-- Every actual invertible-initial full frame at positive rate has least positive period 2*pi/omega. -/
theorem frame_least_positive_period {L0 : Mat} (hL0 : IsUnit L0) {omega : ℝ}
    (hω : 0 < omega) :
    IsLeast {T : ℝ | 0<T ∧ Function.Periodic (frame L0 omega) T} (2*Real.pi/omega) := by
  simpa only [frame_periodic_iff hL0] using RotorPeriods.scaled_tetrad_least_positive_period hω

/-- For any invertible initial matrix, the omega0-rate rotor has the source least positive period 2T0. -/
theorem omega0_evolution_least_positive_period (p : MassiveParameters) {L0 : Mat} (hL0 : IsUnit L0) :
    IsLeast {T : ℝ | 0<T ∧ Function.Periodic (evolution L0 p.omega0) T} (2*p.period) := by
  simpa only [RotorClocks.four_pi_div_omega0] using
    evolution_least_positive_period hL0 (ClockScales.omega0_pos p)

/-- For any invertible initial matrix, the doubled-rate rotor has the source least positive period T0. -/
theorem twice_omega0_evolution_least_positive_period (p : MassiveParameters) {L0 : Mat} (hL0 : IsUnit L0) :
    IsLeast {T : ℝ | 0<T ∧ Function.Periodic (evolution L0 (2*p.omega0)) T} p.period := by
  simpa only [RotorClocks.four_pi_div_twice_omega0] using
    evolution_least_positive_period hL0 (mul_pos (by norm_num : (0:ℝ)<2) (ClockScales.omega0_pos p))

/-- The actual full frame from any invertible initial matrix at rate omega0 has least positive period T0. -/
theorem omega0_frame_least_positive_period (p : MassiveParameters) {L0 : Mat} (hL0 : IsUnit L0) :
    IsLeast {T : ℝ | 0<T ∧ Function.Periodic (frame L0 p.omega0) T} p.period := by
  simpa only [← RotorClocks.period_eq_two_pi_div_omega0] using
    frame_least_positive_period hL0 (ClockScales.omega0_pos p)

/-- The actual full frame from any invertible initial matrix at doubled rate has least positive period T0/2. -/
theorem twice_omega0_frame_least_positive_period (p : MassiveParameters) {L0 : Mat} (hL0 : IsUnit L0) :
    IsLeast {T : ℝ | 0<T ∧ Function.Periodic (frame L0 (2*p.omega0)) T} (p.period/2) := by
  simpa only [RotorClocks.two_pi_div_twice_omega0] using
    frame_least_positive_period hL0 (mul_pos (by norm_num : (0:ℝ)<2) (ClockScales.omega0_pos p))

/-- Advancing by T0 negates the omega0-rate evolution for every initial matrix. -/
theorem omega0_evolution_antiperiod (p : MassiveParameters) (L0 : Mat) (t : ℝ) :
    evolution L0 p.omega0 (t+p.period) = -evolution L0 p.omega0 t := by
  have h := congrArg (fun A : Mat => L0*A) (RotorClocks.omega0Rotor_add_period p t)
  simpa only [RotorClocks.omega0Rotor, evolution, one_mul, mul_neg] using h

/-- Advancing by T0/2 negates the doubled-rate evolution for every initial matrix. -/
theorem twice_omega0_evolution_antiperiod (p : MassiveParameters) (L0 : Mat) (t : ℝ) :
    evolution L0 (2*p.omega0) (t+p.period/2) = -evolution L0 (2*p.omega0) t := by
  have h := congrArg (fun A : Mat => L0*A) (RotorClocks.twiceOmega0Rotor_add_half_period p t)
  simpa only [RotorClocks.twiceOmega0Rotor, evolution, one_mul, mul_neg] using h

end FoliationQM.RotorFrameEvolution
