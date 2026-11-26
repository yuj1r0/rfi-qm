module

public import FoliationQM.RotorODE
public import FoliationQM.ClockScales
public import FoliationQM.PlaneTetrad
public import FoliationQM.RotorPeriods

/-!
# The two source rotor-clock conventions

Sources: v13 `thm:contact_period` (iii), `eq:rotor_compton_evolution`,
and the two frequency conventions in `lem:maurer_cartan`. The positive
Compton frequency and proper period are derived from MassiveParameters.
The rotor clocks are actual matrix evolutions from the identity, while the
observable frames are the actual conjugated Dirac tetrad families.

At tetrad rate omega0 the rotor has least positive period 2T0, reverses sign
after T0, and has rest-spinor phase exp(-i omega0 t/2); the tetrad has least
positive period T0. At rate 2omega0 the rotor has least positive period T0,
the tetrad has least positive period T0/2, and the rest phase is exp(-i omega0 t).
Arbitrary-initial rest-action formulas explicitly require an invertible initial
matrix. These internal matrix/frame periods do not assert that a spacetime
or Reeb trajectory closes.
-/

@[expose] public section

noncomputable section
namespace FoliationQM.RotorClocks
open DiracMatrices PlaneRotor RotorEvolution

/-- The actual identity-initial rotor evolution at the source tetrad angular rate omega0. -/
def omega0Rotor (p : MassiveParameters) (t : ℝ) : Mat := evolution 1 p.omega0 t

/-- The actual identity-initial rotor evolution at the source doubled tetrad angular rate 2omega0. -/
def twiceOmega0Rotor (p : MassiveParameters) (t : ℝ) : Mat := evolution 1 (2*p.omega0) t

/-- The derived positive Compton frequency times the derived proper period equals two pi. -/
theorem omega0_mul_period (p : MassiveParameters) : p.omega0*p.period=2*Real.pi := by
  rw [ClockScales.omega0_eq_two_pi_div_period]
  exact div_mul_cancel₀ _ (ClockScales.period_pos p).ne'

/-- The derived proper period is two pi divided by the derived positive Compton frequency. -/
theorem period_eq_two_pi_div_omega0 (p : MassiveParameters) :
    p.period=2*Real.pi/p.omega0 := by
  apply (eq_div_iff (ClockScales.omega0_pos p).ne').mpr
  simpa only [mul_comm] using omega0_mul_period p

/-- The generic rotor period at rate omega0 is twice the derived proper period. -/
theorem four_pi_div_omega0 (p : MassiveParameters) : 4*Real.pi/p.omega0=2*p.period := by
  rw [period_eq_two_pi_div_omega0]
  ring

/-- The generic rotor period at doubled rate is the derived proper period. -/
theorem four_pi_div_twice_omega0 (p : MassiveParameters) :
    4*Real.pi/(2*p.omega0)=p.period := by
  rw [period_eq_two_pi_div_omega0]
  ring

/-- The generic tetrad period at doubled rate is half the derived proper period. -/
theorem two_pi_div_twice_omega0 (p : MassiveParameters) :
    2*Real.pi/(2*p.omega0)=p.period/2 := by
  rw [period_eq_two_pi_div_omega0]
  ring

/-- The actual omega0 evolution has half-angle omega0 times time divided by two. -/
theorem omega0Rotor_apply (p : MassiveParameters) (t : ℝ) :
    omega0Rotor p t=rotor (p.omega0*t/2) := by simp [omega0Rotor,evolution]

/-- The actual doubled-rate evolution has half-angle omega0 times time. -/
theorem twiceOmega0Rotor_apply (p : MassiveParameters) (t : ℝ) :
    twiceOmega0Rotor p t=rotor (p.omega0*t) := by
  simp only [twiceOmega0Rotor,evolution,one_mul]
  congr 1
  ring

/-- At tetrad rate omega0, advancing by T0 reverses the actual rotor sign. -/
theorem omega0Rotor_add_period (p : MassiveParameters) (t : ℝ) :
    omega0Rotor p (t+p.period)= -omega0Rotor p t := by
  rw [omega0Rotor_apply,omega0Rotor_apply]
  have ht : p.omega0*(t+p.period)/2=p.omega0*t/2+Real.pi := by
    nlinarith [omega0_mul_period p]
  rw [ht,rotor_add_pi]

/-- At tetrad rate 2omega0, advancing by T0/2 reverses the actual rotor sign. -/
theorem twiceOmega0Rotor_add_half_period (p : MassiveParameters) (t : ℝ) :
    twiceOmega0Rotor p (t+p.period/2)= -twiceOmega0Rotor p t := by
  rw [twiceOmega0Rotor_apply,twiceOmega0Rotor_apply]
  have ht : p.omega0*(t+p.period/2)=p.omega0*t+Real.pi := by
    nlinarith [omega0_mul_period p]
  rw [ht,rotor_add_pi]

/-- The actual omega0-rate rotor gives the source negative half-frequency rest-spinor phase. -/
theorem omega0Rotor_restSpinor (p : MassiveParameters) (t : ℝ) :
    (omega0Rotor p t).mulVec restSpinor=
      Complex.exp (-Complex.I*((p.omega0*t/2:ℝ):ℂ)) • restSpinor := by
  rw [omega0Rotor_apply,rotor_mulVec_restSpinor]

/-- The actual doubled-rate rotor gives the full negative Compton-frequency rest-spinor phase. -/
theorem twiceOmega0Rotor_restSpinor (p : MassiveParameters) (t : ℝ) :
    (twiceOmega0Rotor p t).mulVec restSpinor=
      Complex.exp (-Complex.I*((p.omega0*t:ℝ):ℂ)) • restSpinor := by
  rw [twiceOmega0Rotor_apply,rotor_mulVec_restSpinor]

/-- After canceling an invertible initial matrix, omega0-rate evolution has the source negative half-frequency rest phase. -/
theorem omega0_initial_restSpinor (p : MassiveParameters) {L0 : Mat} (hL0 : IsUnit L0) (t : ℝ) :
    (L0⁻¹*evolution L0 p.omega0 t).mulVec restSpinor=
      Complex.exp (-Complex.I*((p.omega0*t/2:ℝ):ℂ)) • restSpinor :=
  RotorODE.initial_inverse_evolution_restSpinor hL0 p.omega0 t

/-- After canceling an invertible initial matrix, doubled-rate evolution has the source full negative Compton-frequency rest phase. -/
theorem twiceOmega0_initial_restSpinor (p : MassiveParameters) {L0 : Mat} (hL0 : IsUnit L0) (t : ℝ) :
    (L0⁻¹*evolution L0 (2*p.omega0) t).mulVec restSpinor=
      Complex.exp (-Complex.I*((p.omega0*t:ℝ):ℂ)) • restSpinor := by
  rw [RotorODE.initial_inverse_evolution_restSpinor hL0]
  have ht : (2*p.omega0)*t/2=p.omega0*t := by ring
  rw [ht]

/-- The actual observable tetrad family at tetrad angular rate omega0. -/
def omega0Tetrad (p : MassiveParameters) (t : ℝ) : Fin 4 → Mat :=
  PlaneTetrad.tetrad (p.omega0*t/2)

/-- The actual observable tetrad family at doubled tetrad angular rate 2omega0. -/
def twiceOmega0Tetrad (p : MassiveParameters) (t : ℝ) : Fin 4 → Mat :=
  PlaneTetrad.tetrad ((2*p.omega0)*t/2)

/-- The doubled-rate observable tetrad uses half-angle omega0 times time. -/
theorem twiceOmega0Tetrad_apply (p : MassiveParameters) (t : ℝ) :
    twiceOmega0Tetrad p t=PlaneTetrad.tetrad (p.omega0*t) := by
  unfold twiceOmega0Tetrad
  congr 1
  ring

/-- At tetrad rate omega0 the actual rotor is periodic with period 2T0. -/
theorem omega0Rotor_periodic (p : MassiveParameters) :
    Function.Periodic (omega0Rotor p) (2*p.period) := by
  intro t
  have ht : t+2*p.period=(t+p.period)+p.period := by ring
  rw [ht,omega0Rotor_add_period,omega0Rotor_add_period,neg_neg]

/-- At doubled tetrad rate the actual rotor is periodic with period T0. -/
theorem twiceOmega0Rotor_periodic (p : MassiveParameters) :
    Function.Periodic (twiceOmega0Rotor p) p.period := by
  intro t
  have ht : t+p.period=(t+p.period/2)+p.period/2 := by ring
  rw [ht,twiceOmega0Rotor_add_half_period,twiceOmega0Rotor_add_half_period,neg_neg]

/-- At tetrad rate omega0 the actual observable tetrad has period T0. -/
theorem omega0Tetrad_periodic (p : MassiveParameters) :
    Function.Periodic (omega0Tetrad p) p.period := by
  intro t
  funext a
  have ht : p.omega0*(t+p.period)/2=p.omega0*t/2+Real.pi := by
    nlinarith [omega0_mul_period p]
  unfold omega0Tetrad
  rw [ht,PlaneTetrad.tetrad_add_pi]

/-- At doubled tetrad rate the actual observable tetrad has period T0/2. -/
theorem twiceOmega0Tetrad_periodic (p : MassiveParameters) :
    Function.Periodic (twiceOmega0Tetrad p) (p.period/2) := by
  intro t
  rw [twiceOmega0Tetrad_apply,twiceOmega0Tetrad_apply]
  funext a
  have ht : p.omega0*(t+p.period/2)=p.omega0*t+Real.pi := by
    nlinarith [omega0_mul_period p]
  rw [ht,PlaneTetrad.tetrad_add_pi]

/-- The half-frequency rest-spinor phase agrees with the existing negative physical phase convention. -/
theorem omega0Rotor_restSpinor_phase (p : MassiveParameters) (t : ℝ) :
    (omega0Rotor p t).mulVec restSpinor=FoliationQM.phase (-p.omega0*t/2) • restSpinor := by
  rw [omega0Rotor_restSpinor]
  congr 2
  push_cast
  ring

/-- The full-frequency rest-spinor phase agrees with the existing negative physical phase convention. -/
theorem twiceOmega0Rotor_restSpinor_phase (p : MassiveParameters) (t : ℝ) :
    (twiceOmega0Rotor p t).mulVec restSpinor=FoliationQM.phase (-p.omega0*t) • restSpinor := by
  rw [twiceOmega0Rotor_restSpinor]
  congr 2
  push_cast
  ring

/-- The actual omega0-rate rotor has least positive period exactly 2T0. -/
theorem omega0Rotor_least_positive_period (p : MassiveParameters) :
    IsLeast {T : ℝ | 0<T ∧ Function.Periodic (omega0Rotor p) T} (2*p.period) := by
  rw [show omega0Rotor p=(fun t => rotor (p.omega0*t/2)) from funext (omega0Rotor_apply p)]
  simpa only [four_pi_div_omega0] using
    RotorPeriods.scaled_rotor_least_positive_period (ClockScales.omega0_pos p)

/-- The actual doubled-rate rotor has least positive period exactly T0. -/
theorem twiceOmega0Rotor_least_positive_period (p : MassiveParameters) :
    IsLeast {T : ℝ | 0<T ∧ Function.Periodic (twiceOmega0Rotor p) T} p.period := by
  rw [show twiceOmega0Rotor p=(fun t => rotor ((2*p.omega0)*t/2)) by
    funext t
    simp [twiceOmega0Rotor,evolution]]
  have hω : 0<(2:ℝ)*p.omega0 := mul_pos (by norm_num) (ClockScales.omega0_pos p)
  simpa only [four_pi_div_twice_omega0] using
    RotorPeriods.scaled_rotor_least_positive_period hω

/-- The actual omega0-rate observable tetrad has least positive period exactly T0. -/
theorem omega0Tetrad_least_positive_period (p : MassiveParameters) :
    IsLeast {T : ℝ | 0<T ∧ Function.Periodic (omega0Tetrad p) T} p.period := by
  change IsLeast {T : ℝ | 0<T ∧ Function.Periodic (fun t => PlaneTetrad.tetrad (p.omega0*t/2)) T} p.period
  simpa only [← period_eq_two_pi_div_omega0] using
    RotorPeriods.scaled_tetrad_least_positive_period (ClockScales.omega0_pos p)

/-- The actual doubled-rate observable tetrad has least positive period exactly T0/2. -/
theorem twiceOmega0Tetrad_least_positive_period (p : MassiveParameters) :
    IsLeast {T : ℝ | 0<T ∧ Function.Periodic (twiceOmega0Tetrad p) T} (p.period/2) := by
  change IsLeast {T : ℝ | 0<T ∧ Function.Periodic (fun t => PlaneTetrad.tetrad ((2*p.omega0)*t/2)) T} (p.period/2)
  have hω : 0<(2:ℝ)*p.omega0 := mul_pos (by norm_num) (ClockScales.omega0_pos p)
  simpa only [two_pi_div_twice_omega0] using
    RotorPeriods.scaled_tetrad_least_positive_period hω

end FoliationQM.RotorClocks
