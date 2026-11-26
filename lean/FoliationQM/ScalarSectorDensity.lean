module
public import FoliationQM.ScalarRestKinetic
public import FoliationQM.ScalarSpinDefect
public import FoliationQM.ScalarPlanePhase
public import FoliationQM.PolarChartAction

/-!
# An actual plane-rotor sector of the second-order action

For v13 `eq:spinor_quadratic_exact` and `eq:coupled_action`, the spinor
built from this rotor and a positive density has the scalar integrand
at each differentiable point. The statement uses its true spatial jets.
-/

@[expose] public section
noncomputable section
open scoped Matrix.Norms.Operator Topology ContDiff
namespace FoliationQM.ScalarSectorDensity
open DiracMatrices DiracFieldDensity ScalarPlanePhase ScalarRestKinetic ActionDensity
open SpinorRegularity PolarChartAction

/-- The plane-rotor field at zero chiral angle with amplitude √ρ. -/
def field (p : MassiveParameters) (ρ S : Covector → ℝ) (x : Covector) : Spinor :=
  PolarSpinorBilinears.polarSpinor (ρ x) 0 (phaseRotor p S x)

/-- The plane-rotor construction realizes the scalar wave along the rest-spinor line. -/
theorem field_eq_lift (p : MassiveParameters) (ρ S : Covector → ℝ) :
    field p ρ S = lift (actionField p ρ S) :=
  funext (polarSpinor_eq_actionField p ρ S)

/-- On the original chart, the invariant spinor density is the scalar density. -/
theorem invariantDensity_field (p : MassiveParameters) {ρ S : Covector → ℝ} {x : Covector} (hρ : 0 ≤ ρ x) :
    invariantDensity (field p ρ S x) = ρ x := by
  rw [field_eq_lift, lift, invariantDensity_embed]
  exact polarField_normSq ρ _ x hρ

/-- A positive scalar density gives a strictly regular plane-rotor spinor. -/
theorem regular_field (p : MassiveParameters) {ρ S : Covector → ℝ} {x : Covector} (hρ : 0 < ρ x) :
    Regular (field p ρ S x) := by
  change 0 < invariantDensity _
  rwa [invariantDensity_field p hρ.le]

/-- The massive spinor density on the actual phase-rotor field equals the scalar Lagrangian. -/
theorem density_eq_hydroIntegrand (p : MassiveParameters) {ρ S : Covector → ℝ} {x : Covector}
    (hρ : DifferentiableAt ℝ ρ x) (hS : DifferentiableAt ℝ S x) (hpos : 0 < ρ x) :
    MassiveSpinKinetic.density p 0 (field p ρ S) x = hydroIntegrand p ρ S coordinateDirections x := by
  have hphase : DifferentiableAt ℝ (fun y => S y / p.hbar) x := by
    simpa only [div_eq_mul_inv, mul_comm] using hS.const_mul p.hbar⁻¹
  have hd : DifferentiableAt ℝ (actionField p ρ S) x :=
    PolarDifferential.differentiableAt_polarField hρ hphase hpos
  rw [field_eq_lift, completed_eq_pairing p hd, hydroIntegrand_eq p hρ hS hpos]

/-- The explicit plane matrix gives local determinant-one factors for the represented field. -/
def factors (p : MassiveParameters) {ρ S : Covector → ℝ} {x : Covector}
    (hρ : ContDiffAt ℝ 1 ρ x) (hS : ContDiffAt ℝ 1 S x) (hp : 0 < ρ x) :
    DiracHSDensity.LocalFactors (field p ρ S) x where
  angle := fun _ => 0
  rotor y := planeMatrix (-(S y / p.hbar))
  density_smooth := hρ.congr_of_eventuallyEq (hρ.continuousAt.eventually (lt_mem_nhds hp) |>.mono
    (fun _ hy => invariantDensity_field p hy.le))
  angle_smooth := contDiffAt_const
  rotor_smooth := (contDiff_planeMatrix 1).contDiffAt.comp x (hS.div_const p.hbar).neg
  realization := by
    filter_upwards [hρ.continuousAt.eventually (lt_mem_nhds hp)] with y hy
    rw [invariantDensity_field p hy.le, spin_planeMatrix]
    exact ⟨hy, det_planeMatrix _, rfl⟩

/-- The actual body connection of these local factors is the scalar phase differential. -/
theorem connection_factors (p : MassiveParameters) {ρ S : Covector → ℝ} {x : Covector}
    (hρ : ContDiffAt ℝ 1 ρ x) (hS : ContDiffAt ℝ 1 S x) (hp : 0 < ρ x) :
    ScalarSpinDefect.connection p (factors p hρ hS hp).rotor x = ScalarSpinDefect.gradient S x := by
  funext μ
  change -(p.hbar / 2) * SpecialLinearConnection.bodyOmega
    (fun y => planeMatrix (-(S y / p.hbar))) x (coordinateDirections μ) 1 2 = _
  rw [bodyOmega_planeMatrix p hS.differentiableAt_one]
  exact spinConnection_eq_fderiv p S x (coordinateDirections μ)

/-- The nonconstant rest-wave phase gives an everywhere regular field of zero massive density. -/
theorem rest_density (p : MassiveParameters) (x : Covector) :
    MassiveSpinKinetic.density p 0 (field p (fun _ => 1) (RestPlaneWave.restAction p)) x = 0 := by
  rw [density_eq_hydroIntegrand p (differentiableAt_const 1)
    ((RestPlaneWave.contDiff_restAction p 1).differentiable (by norm_num) x) (by norm_num)]
  exact hydroIntegrand_rest p x

end FoliationQM.ScalarSectorDensity
