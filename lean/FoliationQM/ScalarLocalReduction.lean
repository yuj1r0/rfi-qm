module
public import FoliationQM.ScalarSpinPrimitive
public import FoliationQM.ScalarSpinDefect
public import FoliationQM.ScalarSectorAction
public import FoliationQM.ScalarPhaseReversal

/-!
# Local scalar reduction and quadratic stationarity

For v13 `thm:dirac_lift`, vanishing curvature of the true spin-axis
connection gives a scalar phase on an interior ball of a polar chart.
The explicit frame and chiral terms enter both the pointwise and the
integrated comparison. The reversed rest-phase example separates the
field equations of the massive quadratic and first-order actions.
-/

@[expose] public section
noncomputable section
open scoped Matrix.Norms.Operator Topology ContDiff
namespace FoliationQM.ScalarLocalReduction
open MeasureTheory DiracMatrices DiracFieldDensity SpinorRegularity SpinorMatrix SpecialLinearSpin
open ScalarSpinDefect DiracHSDensity ScalarSpinPrimitive

/-- A common polar chart for a spinor field on U, with enough matrix smoothness to compute curvature. -/
structure Chart (U : Set Covector) (ψ : Covector → Spinor) where
  angle : Covector → ℝ
  rotor : Covector → Mat2
  density_smooth : ∀ x ∈ U, ContDiffAt ℝ 1 (fun y => invariantDensity (ψ y)) x
  angle_smooth : ∀ x ∈ U, ContDiffAt ℝ 1 angle x
  rotor_smooth : ∀ x ∈ U, ContDiffAt ℝ 2 rotor x
  realization : ∀ y ∈ U, 0 < invariantDensity (ψ y) ∧ (rotor y).det = 1 ∧
    ψ y = PolarSpinorBilinears.polarSpinor (invariantDensity (ψ y)) (angle y) (spin (rotor y))

variable {U : Set Covector} {ψ : Covector → Spinor}

/-- An open chart supplies a genuine germ of differentiable factors at each of its points. -/
def Chart.factors (P : Chart U ψ) (hU : IsOpen U) {x : Covector} (hx : x ∈ U) : LocalFactors ψ x where
  angle := P.angle
  rotor := P.rotor
  density_smooth := P.density_smooth x hx
  angle_smooth := P.angle_smooth x hx
  rotor_smooth := (P.rotor_smooth x hx).of_le (by norm_num)
  realization := Filter.mem_of_superset (hU.mem_nhds hx) (fun y hy => P.realization y hy)

/-- The signed remainder of the scalar density on a common chart. -/
def correction (p : MassiveParameters) (P : Chart U ψ) (x : Covector) : ℝ :=
  auxiliary p (invariantDensity (ψ x)) (gradient P.angle x) (spinGradient p ψ x) (velocityGradient p ψ x)

/-- Closed spin connection on an open chart yields an interior ball and one phase
that gives the density identity throughout that ball. -/
theorem exists_ball_comparison (p : MassiveParameters) (hU : IsOpen U) (P : Chart U ψ)
    (hf : FlatOn P.rotor U) {x : Covector} (hx : x ∈ U) :
    ∃ r > 0, Metric.ball x r ⊆ U ∧ ∃ S : Covector → ℝ, ∀ y ∈ Metric.ball x r,
      HasFDerivAt S (oneForm p P.rotor y) y ∧
      MassiveSpinKinetic.density p (P.angle y) ψ y =
        PolarChartAction.hydroIntegrand p (fun z => invariantDensity (ψ z)) S coordinateDirections y +
          correction p P y := by
  obtain ⟨r, hr, hs, S, hS⟩ := exists_primitive_ball p hU P.rotor_smooth (fun y hy => (P.realization y hy).2.1) hf hx
  refine ⟨r, hr, hs, S, fun y hy => ⟨hS y hy, ?_⟩⟩
  exact density_of_primitive p (P.factors hU (hs hy)) S (connection_eq_gradient p (hS y hy))

/-- On any measurable part of a chart with a phase primitive, integrating the massive density
retains precisely the integral of the signed correction when the two terms are integrable. -/
theorem integral_comparison (p : MassiveParameters) (hU : IsOpen U) (P : Chart U ψ) {V : Set Covector}
    (hV : MeasurableSet V) (hs : V ⊆ U) (S : Covector → ℝ) (hS : ∀ x ∈ V, HasFDerivAt S (oneForm p P.rotor x) x)
    (hi : IntegrableOn (PolarChartAction.hydroIntegrand p (fun z => invariantDensity (ψ z)) S coordinateDirections) V)
    (hc : IntegrableOn (correction p P) V) :
    (∫ x in V, MassiveSpinKinetic.density p (P.angle x) ψ x) =
      (∫ x in V, PolarChartAction.hydroIntegrand p (fun z => invariantDensity (ψ z)) S coordinateDirections x) +
        ∫ x in V, correction p P x := by
  rw [← integral_add hi hc]
  exact setIntegral_congr_fun hV fun x hx => density_of_primitive p (P.factors hU (hs hx)) S
    (connection_eq_gradient p (hS x hx))

/-- On the same measurable domain the actual massive density is integrable whenever
the scalar integrand and its correction are integrable. -/
theorem integrableOn_comparison (p : MassiveParameters) (hU : IsOpen U) (P : Chart U ψ) {V : Set Covector}
    (hV : MeasurableSet V) (hs : V ⊆ U) (S : Covector → ℝ) (hS : ∀ x ∈ V, HasFDerivAt S (oneForm p P.rotor x) x)
    (hi : IntegrableOn (PolarChartAction.hydroIntegrand p (fun z => invariantDensity (ψ z)) S coordinateDirections) V)
    (hc : IntegrableOn (correction p P) V) :
    IntegrableOn (fun x => MassiveSpinKinetic.density p (P.angle x) ψ x) V :=
  (hi.add hc).congr_fun (fun x hx => (density_of_primitive p (P.factors hU (hs hx)) S
    (connection_eq_gradient p (hS x hx))).symm) hV

/-- The reversed rest phase is quadratic-stationary and strictly regular, and its
first-order positive-mass Dirac residual is nonzero at every point of U. -/
theorem reversed_quadratic_stationary (p : MassiveParameters) (hU : IsOpen U) :
    ScalarSectorAction.StationaryOn p (fun _ => 1) (-RestPlaneWave.restAction p) U ∧
      ∀ x ∈ U, Regular (ScalarSectorDensity.field p (fun _ => 1) (-RestPlaneWave.restAction p) x) ∧
      DiracEquation.diracField p.hbar p.m p.c
        (ScalarSectorDensity.field p (fun _ => 1) (-RestPlaneWave.restAction p)) x ≠ 0 :=
  ⟨(ScalarSectorAction.stationaryOn_iff_relativePolar p hU (fun _ _ => contDiffAt_const)
    (fun _ _ => (RestPlaneWave.contDiff_restAction p ∞).neg.contDiffAt) (fun _ _ => zero_lt_one)).mpr
      (ScalarPhaseReversal.reversed_rest_stationary p hU), fun x _ =>
        ⟨ScalarSectorDensity.regular_field p (by exact zero_lt_one), ScalarPhaseReversal.reversed_rest_not_dirac p x⟩⟩

end FoliationQM.ScalarLocalReduction
