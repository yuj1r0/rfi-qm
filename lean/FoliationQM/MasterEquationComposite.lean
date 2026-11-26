module

public import FoliationQM.CurvedGlobalMaster
public import FoliationQM.CurvedAtlasVariation
public import FoliationQM.CurvedPolarKG
public import FoliationQM.CurvedQuantumVelocity
public import FoliationQM.MasterEquation

/-!
# The three master statements for one density and clock

Source: v13 `sec:master_equation`, the overview combining
`eq:master_local_metric`, `eq:master_variational_equivalence` and
`eq:master_dressed_mass`, component kinds B and C. On a regular Lorentzian
metric atlas, let `ρ > 0` be a twice continuously differentiable density and
`τ` a twice continuously differentiable real clock, with wave
`ψ = √ρ exp(-i (2π/T₀) τ)`. Then:

* (I) in every chart, `|dψ|² = (ρ/ℓ_C²) [c² (dτ)² + (c T₀/4π)² (d ln ρ)²]`
  for every tangent direction;
* (II) if the action density and boundary scalar are integrable and the
  integrated boundary term vanishes, the operator action of `ψ` equals the
  density–clock action;
* (III) if the action is stationary under all chart-supported variations of
  `ψ`, then in every chart `g^{μν} ∂_μ S ∂_ν S / m² = c² (1 + q)` with
  `S = -mc² τ` and `q = ℓ_C² (□_g √ρ / √ρ - 𝓡/6)`, which is
  `M_eff² c⁴ = (mc²)² (1 + q)`; and where `1 + q > 0` the velocity
  `U = -∇S / (m √(1 + q))` has `g(U, U) = c²`.

Each statement is an existing theorem of this development specialised to the
same pair `(ρ, τ)`. In (III) stationarity is under all variations of the
wave; that variation of the density alone suffices is proved only in flat
coordinates. The clock is a real function on the whole space, so circle-valued
clocks around nodes and the nodal extension are outside this statement.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.MasterEquationComposite

open MeasureTheory LorentzMatrixGroup CurvedMetricChartMeasure CurvedAtlasDescent
open CurvedAtlasAction CurvedClockNormalization CurvedGlobalMaster CurvedAtlasVariation
open CurvedPolarKG CurvedGradientCovariance CurvedScalarGradient CurvedQuantumVelocity
open PolarSecondDifferential PolarDifferential CurvedKGTestResidual RNCHalfDensityJet
open scoped Topology Matrix.Norms.Operator

variable {X : Type*} [TopologicalSpace X]

/-- In a chart, the action field of the clock phase is the clock wave. -/
theorem repr_actionField_clockPhase (p : MassiveParameters) (A : MetricAtlas X) (i : ℕ)
    (ρ τ : X → ℝ) :
    repr A i (ActionDensity.actionField p ρ (clockPhase p τ)) =
      MasterEquation.clockWave p (repr A i ρ) (repr A i τ) := by
  funext y
  simp only [CurvedAtlasDescent.repr, Function.comp_apply, ActionDensity.actionField,
    MasterEquation.clockWave, clockPhase, polarField]
  congr 2
  rw [MassiveParameters.period]
  have hm := p.m_pos.ne'
  have hc := p.c_pos.ne'
  have hh := p.hbar_pos.ne'
  have hpi := Real.pi_pos.ne'
  field_simp

/-- (I) The local metric identity in every chart. -/
theorem local_metric (p : MassiveParameters) (A : MetricAtlas X) {ρ τ : X → ℝ}
    (hρ : Regular A 2 ρ) (hτ : Regular A 2 τ) (hp : ∀ x, 0 < ρ x) (i : ℕ) {y : Covector}
    (hy : y ∈ (A.chart i).target) (v : Covector) :
    ‖fderiv ℝ (repr A i (ActionDensity.actionField p ρ (clockPhase p τ))) y v‖ ^ 2 =
      (repr A i ρ y / p.ellC ^ 2) *
        (p.c ^ 2 * (fderiv ℝ (repr A i τ) y v) ^ 2 +
          (p.c * p.period / (4 * Real.pi)) ^ 2 *
            (fderiv ℝ (fun z => Real.log (repr A i ρ z)) y v) ^ 2) := by
  rw [repr_actionField_clockPhase]
  exact (MasterEquation.master_local_metric p ((hρ i y hy).differentiableAt (by norm_num))
    ((hτ i y hy).differentiableAt (by norm_num)) (hp _) v).2

variable [MeasurableSpace X] [BorelSpace X] [T2Space X]

/-- (III) At a stationary point of the action, the phase gradient lies on the
dressed mass shell in every chart. -/
theorem dressed_mass (p : MassiveParameters) (A : MetricAtlas X) (hA : SmoothLorentz A)
    {ρ τ : X → ℝ} (hρ : Regular A 2 ρ) (hτ : Regular A 2 τ) (hp : ∀ x, 0 < ρ x)
    (hstat : ChartStationary p A (ActionDensity.actionField p ρ (clockPhase p τ))) (i : ℕ)
    {y : Covector} (hy : y ∈ (A.chart i).target) :
    pairing (A.metric i) (repr A i (clockPhase p τ)) (repr A i (clockPhase p τ)) y / p.m ^ 2 =
      p.c ^ 2 * (1 + defect p (A.metric i) (fun z => √(repr A i ρ z)) y) := by
  have hψ := regular_actionField A p hρ (regular_clockPhase p A hτ) hp
  have hx : (A.chart i).symm y ∈ (A.chart i).source := (A.chart i).map_target hy
  have hkg := (chart_stationary_iff p A hA hψ).mp hstat ((A.chart i).symm y)
  rw [kgOperatorField_chart p A hA hψ i hx, (A.chart i).right_inv hy] at hkg
  have hfield : repr A i (ActionDensity.actionField p ρ (clockPhase p τ)) =
      amplitudeField (fun z => √(repr A i ρ z))
        (fun z => repr A i (clockPhase p τ) z / p.hbar) := rfl
  rw [hfield] at hkg
  exact mass_shell p ((hA.metric_smooth i y hy).differentiableAt (by norm_num))
    (hA.negative i y hy) (hA.symmetric i y hy)
    ((hρ i y hy).sqrt (hp _).ne') (regular_clockPhase p A hτ i y hy)
    (Real.sqrt_pos.mpr (hp _)) hkg

/-- (III) On the timelike domain `1 + q > 0` the dressed velocity is
normalized to `c²`. -/
theorem dressed_velocity (p : MassiveParameters) {g : Covector → Mat4} {R S : Covector → ℝ}
    {y : Covector} (hd : (g y).det < 0)
    (hshell : pairing g S S y / p.m ^ 2 = p.c ^ 2 * (1 + defect p g R y))
    (hq : 0 < 1 + defect p g R y) :
    form (g y) ((√(1 + defect p g R y))⁻¹ • velocity p g S y)
      ((√(1 + defect p g R y))⁻¹ • velocity p g S y) = p.c ^ 2 := by
  have hu : IsUnit (g y).det := isUnit_iff_ne_zero.mpr hd.ne
  have hs : 0 < √(1 + defect p g R y) := Real.sqrt_pos.mpr hq
  simp only [map_smul, _root_.smul_apply, smul_eq_mul, form_velocity_self p hu S, hshell]
  have hsq : √(1 + defect p g R y) * √(1 + defect p g R y) = 1 + defect p g R y :=
    Real.mul_self_sqrt hq.le
  field_simp
  nlinarith

/-- The three master statements for one density and clock. -/
theorem master_equivalence (p : MassiveParameters) (A : MetricAtlas X) (hA : SmoothLorentz A)
    {ρ τ : X → ℝ} (hρ : Regular A 2 ρ) (hτ : Regular A 2 τ) (hp : ∀ x, 0 < ρ x)
    (hfin : Integrable
      (kgDensityField p A (ActionDensity.actionField p ρ (clockPhase p τ))) A.measure)
    (hboundary : Integrable
      (boundaryField A (ActionDensity.actionField p ρ (clockPhase p τ))) A.measure)
    (hz : ∫ x, boundaryField A (ActionDensity.actionField p ρ (clockPhase p τ)) x ∂A.measure = 0)
    (hstat : ChartStationary p A (ActionDensity.actionField p ρ (clockPhase p τ))) :
    (∀ i y, y ∈ (A.chart i).target → ∀ v : Covector,
      ‖fderiv ℝ (repr A i (ActionDensity.actionField p ρ (clockPhase p τ))) y v‖ ^ 2 =
        (repr A i ρ y / p.ellC ^ 2) *
          (p.c ^ 2 * (fderiv ℝ (repr A i τ) y v) ^ 2 +
            (p.c * p.period / (4 * Real.pi)) ^ 2 *
              (fderiv ℝ (fun z => Real.log (repr A i ρ z)) y v) ^ 2)) ∧
    operatorAction p A (ActionDensity.actionField p ρ (clockPhase p τ)) =
      (clockAction p A ρ τ : ℂ) ∧
    ∀ i y, y ∈ (A.chart i).target →
      pairing (A.metric i) (repr A i (clockPhase p τ)) (repr A i (clockPhase p τ)) y /
          p.m ^ 2 =
        p.c ^ 2 * (1 + defect p (A.metric i) (fun z => √(repr A i ρ z)) y) :=
  ⟨fun i _ hy v => local_metric p A hρ hτ hp i hy v,
    clock_operator_action_boundary_zero p A hA hρ hτ hp hfin hboundary hz,
    fun i _ hy => dressed_mass p A hA hρ hτ hp hstat i hy⟩

end FoliationQM.MasterEquationComposite
