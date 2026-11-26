module
public import FoliationQM.TwistedRegularStationarity
public import FoliationQM.RestPlaneWave

/-!
# A nonzero chiral potential with stationary rest waves

For the fixed-background variational sector of v13 `thm:dirac_lift`, a
timelike linear chiral angle gives a constant positive shift in the
squared mass term. Its exact stationary mode is the ordinary massive
scalar rest wave with this adjusted mass.
-/

@[expose] public section
noncomputable section
open scoped ContDiff
namespace FoliationQM.ChiralEffectiveMass
open TwistedScalarAngles TwistedScalarDensity TwistedScalarVariation TwistedScalarStationarity
open DiracFieldDensity

/-- Positive mass parameter for the timelike angle κx⁰; c and ℏ retain their original values. -/
def shifted (p : MassiveParameters) (k : ℝ) : MassiveParameters where
  c := p.c
  hbar := p.hbar
  m := Real.sqrt (p.m^2 + (p.hbar*k/(2*p.c))^2)
  c_pos := p.c_pos
  hbar_pos := p.hbar_pos
  m_pos := Real.sqrt_pos_of_pos (add_pos_of_pos_of_nonneg (sq_pos_of_pos p.m_pos) (sq_nonneg _))

/-- The squared mass coefficient increases by ℏ²κ²/4. -/
theorem shifted_sq (p : MassiveParameters) (k : ℝ) :
    (shifted p k).m^2 * p.c^2 = p.m^2 * p.c^2 + p.hbar^2/4*k^2 := by
  change (Real.sqrt _) ^ 2 * _ = _
  rw [Real.sq_sqrt (by positivity)]
  field_simp [p.c_pos.ne']
  ring

/-- The potential of the timelike linear angle is the added mass coefficient. -/
theorem potential_time (p : MassiveParameters) (k : ℝ) (x : Covector) :
    potential p (linearAngle 0 k) x = p.hbar^2/4*k^2 := by
  rw [potential_linearAngle]
  simp [RealLorentzFrame.sign]

/-- The rest mode of the shifted mass. -/
def mode (p : MassiveParameters) (k : ℝ) : Covector → ℂ := RestPlaneWave.restWave (shifted p k)

/-- The time-linear chirally rotated rest mode is stationary along all compact scalar variations
on every open domain for every real κ. -/
theorem mode_stationary (p : MassiveParameters) (k : ℝ) {U : Set Covector} (hU : IsOpen U) :
    StationaryOn p (linearAngle 0 k) (mode p k) U := by
  unfold mode
  rw [stationary_iff_wave p hU (fun _ _ => (smooth_linearAngle 0 k 1).contDiffAt)
    (fun _ _ => (RestPlaneWave.contDiff_restWave (shifted p k) ∞).contDiffAt)]
  intro x _
  rw [potential_time, ← shifted_sq]
  exact RestPlaneWave.restWave_kg (shifted p k) x

/-- These physical spinors are strictly regular everywhere, including for nonzero chiral gradients. -/
theorem regular_mode (p : MassiveParameters) (k : ℝ) (x : Covector) :
    SpinorRegularity.Regular (TwistedScalarField.field (linearAngle 0 k) (mode p k) x) :=
  (TwistedScalarField.regular_field_iff _ _ _).mpr (RestPlaneWave.restWave_ne_zero _ x)

/-- For the linear time angle the full twisted density equals the scalar density
with the shifted mass, including for fields with zeros. -/
theorem density_eq_shifted (p : MassiveParameters) (k : ℝ) {z : Covector → ℂ} {x : Covector}
    (hz : DifferentiableAt ℝ z x) :
    density p (linearAngle 0 k) z x = TwistedScalarAction.scalarDensity (shifted p k) z x := by
  have hm : ((shifted p k).m : ℂ)^2 * (p.c : ℂ)^2 = (p.m : ℂ)^2 * (p.c : ℂ)^2 +
      ((p.hbar^2 / 4 * k^2 : ℝ) : ℂ) := by exact_mod_cast shifted_sq p k
  have he : ActionVariation.fieldPairing (shifted p k) z z coordinateDirections x =
      ActionVariation.fieldPairing p z z coordinateDirections x -
        (potential p (linearAngle 0 k) x : ℂ) * (Complex.normSq (z x) : ℂ) := by
    simp only [ActionVariation.fieldPairing, ActionVariation.pairing,
      show (shifted p k).hbar = p.hbar from rfl, show (shifted p k).c = p.c from rfl,
      hm, potential_time, Complex.normSq_eq_conj_mul_self]
    ring
  rw [density_eq_pairing p ((smooth_linearAngle 0 k 1).differentiable (by norm_num) x) hz,
    TwistedScalarAction.scalarDensity, he]
  simp

/-- The stationary plane mode has zero true twisted density. -/
theorem mode_density_zero (p : MassiveParameters) (k : ℝ) (x : Covector) :
    density p (linearAngle 0 k) (mode p k) x = 0 := by
  unfold mode
  rw [density_eq_shifted p k ((RestPlaneWave.contDiff_restWave (shifted p k) 1).differentiable (by norm_num) x)]
  exact congrArg Complex.re (RestPlaneWave.fieldPairing_restWave_self (shifted p k) x)

/-- The example is stationary with finite ordinary action even on unbounded open regions. -/
theorem mode_finite (p : MassiveParameters) (k : ℝ) {U : Set Covector} (hU : IsOpen U) :
    FiniteStationary p (linearAngle 0 k) (mode p k) U ∧
      TwistedScalarAction.action p (linearAngle 0 k) (mode p k) U = 0 := by
  have hi : MeasureTheory.IntegrableOn (density p (linearAngle 0 k) (mode p k)) U :=
    MeasureTheory.integrableOn_zero.congr_fun (fun x _ => (mode_density_zero p k x).symm) hU.measurableSet
  exact ⟨(finite_iff p hU (fun _ _ => (smooth_linearAngle 0 k 1).contDiffAt) hi).mpr (mode_stationary p k hU),
    MeasureTheory.setIntegral_eq_zero_of_forall_eq_zero (fun x _ => mode_density_zero p k x)⟩

/-- On a nonzero-gradient mode the bare original Klein–Gordon residual is nonzero at every point. -/
theorem scalar_residual_ne_zero (p : MassiveParameters) {k : ℝ} (hk : k ≠ 0) (x : Covector) :
    FlatIntegrationByParts.kgOperator p (mode p k) coordinateDirections x ≠ 0 := by
  have he := (stationary_iff_force p isOpen_univ (fun _ _ => (smooth_linearAngle 0 k 1).contDiffAt)
    (fun _ _ => (RestPlaneWave.contDiff_restWave (shifted p k) ∞).contDiffAt)).mp
      (mode_stationary p k isOpen_univ) x (Set.mem_univ _)
  intro hz
  change FlatIntegrationByParts.kgOperator p (mode p k) coordinateDirections x +
    (potential p (linearAngle 0 k) x : ℂ) * mode p k x = 0 at he
  rw [hz, zero_add, potential_time] at he
  have hpos : 0 < p.hbar^2/4*k^2 := mul_pos (div_pos (sq_pos_of_pos p.hbar_pos) (by norm_num)) (sq_pos_of_ne_zero hk)
  exact mul_ne_zero (Complex.ofReal_ne_zero.mpr hpos.ne') (RestPlaneWave.restWave_ne_zero _ x) he

end FoliationQM.ChiralEffectiveMass
