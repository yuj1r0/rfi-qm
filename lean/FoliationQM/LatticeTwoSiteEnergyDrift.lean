module

public import FoliationQM.LatticePolarEnergyBalance

/-!
# An explicit two-site energy loss

On the unit lattice, take signed amplitudes (1, 2), lag clocks (0, π/2),
and zero potential. The replicated Neumann rows give two kinetic drift
contributions with opposite signs and different regularization fractions.
The total initial energy derivative is strictly negative at every positive
width, although both site amplitudes are nonzero.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.LatticeTwoSiteEnergyDrift

open LatticeConservation LatticePolarStencil LatticeClockRegularization
open LatticeLagHamiltonian LatticePolarEnergyBalance

/-- Physical parameters in units with mass, light speed and reduced Planck constant one. -/
def units : MassiveParameters := ⟨1, 1, 1, by norm_num, by norm_num, by norm_num⟩

/-- Positive initial amplitudes on the left and right endpoints. -/
def amplitude : Fin 2 → ℝ := ![1, 2]

/-- Initial lag-clock values giving a quarter-turn phase increment. -/
def lag : Fin 2 → ℝ := ![0, Real.pi/2]

/-- The zero potential for the two-site example. -/
def potential : Fin 2 → ℝ := fun _ => 0

/-- Initial state of the regularized polar flow in amplitude and lag coordinates. -/
def seed : LatticeRegularizedFlow.State 2 := (amplitude, lag)

/-- Both sites of the initial state are strictly away from zero amplitude. -/
theorem amplitude_pos (i : Fin 2) : 0 < amplitude i := by
  fin_cases i <;> norm_num [amplitude]

/-- The initial state has rectangularly weighted mass five. -/
theorem mass_seed : sourceMass 1 amplitude = 5 := by
  norm_num [sourceMass, Fin.sum_univ_two, amplitude]

/-- The lag and dimensionless phase coordinates agree in these units. -/
theorem phase_eq_lag : lagPhase units lag = lag := by
  funext i
  simp [lagPhase, units, MassiveParameters.ellC]

/-- The replicated endpoint rows have radial stencils −1 and −2. -/
theorem radial_values : radial amplitude (lagPhase units lag) = ![-1, -2] := by
  rw [phase_eq_lag]
  funext i
  fin_cases i <;>
    norm_num [radial, amplitude, lag, nextNode, prevNode, Real.cos_pi_div_two]

/-- At the same endpoints the source amplitude velocities are −1 and 1/2. -/
theorem amplitude_rates :
    sourceAmplitudeRHS units.ellC units.c 1 amplitude (lagPhase units lag) = ![-1, 1/2] := by
  rw [phase_eq_lag]
  funext i
  fin_cases i <;> norm_num [sourceAmplitudeRHS, amplitude, lag, nextNode, prevNode,
    units, MassiveParameters.ellC, Real.sin_pi_div_two]

/-- The exact signed energy derivative at the initial two-site state. -/
theorem drift_eq (ε : ℝ) :
    drift units 1 ε amplitude (lagPhase units lag) = -3*ε^2/((1+ε^2)*(4+ε^2)) := by
  rw [drift, Fin.sum_univ_two, amplitude_rates, radial_values]
  norm_num [defectFraction, amplitude, units, MassiveParameters.ellC]
  have h₁ : 0 < 1 + ε^2 := by positivity
  have h₄ : 0 < 4 + ε^2 := by positivity
  field_simp [h₁.ne', h₄.ne']
  ring

/-- Every positive regularizer width gives strictly decreasing energy at this state. -/
theorem drift_neg (ε : ℝ) (hε : 0 < ε) :
    drift units 1 ε amplitude (lagPhase units lag) < 0 := by
  rw [drift_eq]
  exact div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (by norm_num) (sq_pos_of_pos hε))
    (mul_pos (by positivity) (by positivity))

end FoliationQM.LatticeTwoSiteEnergyDrift
