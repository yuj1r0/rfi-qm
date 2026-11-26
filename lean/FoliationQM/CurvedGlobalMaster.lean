module

public import FoliationQM.CurvedAtlasAction
public import FoliationQM.CurvedMasterEquivalence

/-!
# Global normalized clock and operator actions

The computed wave, kinetic pairing and curvature define global fields on
the regular metric atlas. The boundary scalar evaluates to the actual
coordinate flux divergence divided by the metric volume factor. Its
integral gives the exact global correction in the normalized master action.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.CurvedGlobalMaster

open MeasureTheory CurvedMetricChartMeasure CurvedAtlasDescent CurvedAtlasAction
  CurvedClockNormalization RNCVolumeDensity
open scoped Matrix.Norms.Operator
set_option backward.isDefEq.respectTransparency false
variable {X : Type*} [TopologicalSpace X]

/-- The global normalized master operator uses the computed global wave and scalar curvature. -/
def masterOp (p : MassiveParameters) (A : MetricAtlas X) (ψ : X → ℂ) (x : X) : ℂ :=
  (-(p.ellC ^ 2)) • waveField A ψ x + (-1 + p.ellC ^ 2 * scalarField A x / 6) • ψ x

/-- The master operator evaluates in every chart by its actual coordinate expression. -/
theorem masterOp_chart (p : MassiveParameters) (A : MetricAtlas X) (hA : SmoothLorentz A)
    {ψ : X → ℂ} (hψ : Regular A 2 ψ) (i : ℕ) {x : X} (hx : x ∈ (A.chart i).source) :
    masterOp p A ψ x = CurvedNormalizedOperator.masterOp p (A.metric i) (repr A i ψ) (A.chart i x) := by
  rw [masterOp, CurvedNormalizedOperator.masterOp, waveField_chart A hA hψ i hx,
    scalarField_chart A hA i hx, repr_chart A i ψ hx]

/-- The invariant boundary scalar is the divergence of the conjugate-field flux per unit metric volume. -/
def boundaryField (A : MetricAtlas X) (ψ : X → ℂ) (x : X) : ℂ :=
  kineticField A ψ ψ x + star (ψ x) * waveField A ψ x

/-- Multiplication by the coordinate volume factor recovers the actual coordinate flux divergence. -/
theorem boundaryField_chart (A : MetricAtlas X) (hA : SmoothLorentz A) {ψ : X → ℂ}
    (hψ : Regular A 2 ψ) (i : ℕ) {x : X} (hx : x ∈ (A.chart i).source) :
    volumeFactor (A.metric i (A.chart i x)) • boundaryField A ψ x =
      CurvedGreenBoundary.boundaryDivergence (A.metric i) (repr A i ψ) (repr A i ψ) (A.chart i x) := by
  have hy := (A.chart i).map_source hx
  rw [boundaryField, kineticField_chart A hA hψ hψ i hx, waveField_chart A hA hψ i hx,
    ← repr_chart A i ψ hx, smul_add]
  exact (CurvedGreenBoundary.first_green
    ((hA.metric_smooth i _ hy).differentiableAt (by decide)) (hA.negative i _ hy)
    ((hψ i _ hy).differentiableAt (by decide)) (hψ i _ hy)).symm

/-- The normalized complex operator density differs from the real action density by the computed global divergence. -/
theorem density_boundary (p : MassiveParameters) (A : MetricAtlas X) (hA : SmoothLorentz A)
    {ψ : X → ℂ} (hψ : Regular A 2 ψ) (x : X) :
    star (ψ x) * masterOp p A ψ x =
      (1 / (p.m ^ 2 * p.c ^ 2)) • (kgDensityField p A ψ x : ℂ) -
        p.ellC ^ 2 • boundaryField A ψ x := by
  obtain ⟨i, hi⟩ := exists_chart A x
  have hy := (A.chart i).map_source hi
  have hμ : volumeFactor (A.metric i (A.chart i x)) ≠ 0 :=
    (Real.sqrt_pos.2 (neg_pos.2 (hA.negative i _ hy))).ne'
  apply smul_right_injective ℂ hμ
  dsimp only
  rw [smul_sub, smul_comm _ (p.ellC ^ 2), boundaryField_chart A hA hψ i hi,
    masterOp_chart p A hA hψ i hi, kgDensityField_chart p A hA hψ i hi,
    ← repr_chart A i ψ hi, smul_smul]
  have he := CurvedNormalizedOperator.density_boundary p
    ((hA.metric_smooth i _ hy).differentiableAt (by decide)) (hA.negative i _ hy)
    (hA.symmetric i _ hy) (hψ i _ hy)
  simpa only [mul_one_div] using he

/-- The clock phase of a C² global clock has the same coordinate regularity. -/
theorem regular_clockPhase (p : MassiveParameters) (A : MetricAtlas X) {τ : X → ℝ}
    (hτ : Regular A 2 τ) : Regular A 2 (clockPhase p τ) := by
  intro i y hy
  exact contDiffAt_const.mul (hτ i y hy)

/-- The global normalized clock density is selected from the literal local eikonal, Fisher and curvature expressions. -/
def clockDensityField (p : MassiveParameters) (A : MetricAtlas X) (ρ τ : X → ℝ) : X → ℝ :=
  descend A (fun i => normalizedClockDensity p (A.metric i) (repr A i ρ) (repr A i τ))

/-- The full global polar density normalizes to the clock expression at every point. -/
theorem hydro_density_normalized (p : MassiveParameters) (A : MetricAtlas X) {ρ τ : X → ℝ}
    (hτ : Regular A 2 τ) (x : X) :
    hydroDensityField p A ρ (clockPhase p τ) x / (p.m ^ 2 * p.c ^ 2) =
      clockDensityField p A ρ τ x := by
  let i := Classical.choose (exists_chart A x)
  have hi := Classical.choose_spec (exists_chart A x)
  exact CurvedClockNormalization.hydro_density_normalized p (A.metric i) (repr A i ρ)
    ((hτ i _ ((A.chart i).map_source hi)).differentiableAt (by decide))

/-- Clock densities in two charts agree because the actual polar density and its mass normalization agree. -/
theorem clockDensityField_chart (p : MassiveParameters) (A : MetricAtlas X) (hA : SmoothLorentz A)
    {ρ τ : X → ℝ} (hρ : Regular A 2 ρ) (hτ : Regular A 2 τ) (hp : ∀ x, 0 < ρ x)
    (i : ℕ) {x : X} (hx : x ∈ (A.chart i).source) :
    clockDensityField p A ρ τ x =
      normalizedClockDensity p (A.metric i) (repr A i ρ) (repr A i τ) (A.chart i x) := by
  rw [← hydro_density_normalized p A hτ,
    hydroDensityField_chart p A hA hρ (regular_clockPhase p A hτ) hp i hx]
  exact CurvedClockNormalization.hydro_density_normalized p (A.metric i) (repr A i ρ)
    ((hτ i _ ((A.chart i).map_source hx)).differentiableAt (by decide))

variable [MeasurableSpace X]

/-- The global normalized clock action integrates its compatible literal clock density. -/
def clockAction (p : MassiveParameters) (A : MetricAtlas X) (ρ τ : X → ℝ) : ℝ :=
  ∫ x, clockDensityField p A ρ τ x ∂A.measure

/-- The global master operator action pairs the conjugate field with the computed wave operator. -/
def operatorAction (p : MassiveParameters) (A : MetricAtlas X) (ψ : X → ℂ) : ℂ :=
  ∫ x, star (ψ x) * masterOp p A ψ x ∂A.measure

/-- The global complex-field action normalizes to the global clock action for positive regular fields. -/
theorem kg_action_normalized (p : MassiveParameters) (A : MetricAtlas X) (hA : SmoothLorentz A)
    {ρ τ : X → ℝ} (hρ : Regular A 2 ρ) (hτ : Regular A 2 τ) (hp : ∀ x, 0 < ρ x) :
    kgAction p A (ActionDensity.actionField p ρ (clockPhase p τ)) / (p.m ^ 2 * p.c ^ 2) =
      clockAction p A ρ τ := by
  rw [action_eq p A hA hρ (regular_clockPhase p A hτ) hp, hydroAction, ← integral_div, clockAction]
  exact integral_congr_ae (Filter.Eventually.of_forall (hydro_density_normalized p A hτ))

/-- The global operator action retains the explicit integral of the actual boundary divergence. -/
theorem operator_action_boundary (p : MassiveParameters) (A : MetricAtlas X) (hA : SmoothLorentz A)
    {ψ : X → ℂ} (hψ : Regular A 2 ψ)
    (hfin : Integrable (kgDensityField p A ψ) A.measure)
    (hboundary : Integrable (boundaryField A ψ) A.measure) :
    operatorAction p A ψ + p.ellC ^ 2 • ∫ x, boundaryField A ψ x ∂A.measure =
      ((kgAction p A ψ / (p.m ^ 2 * p.c ^ 2) : ℝ) : ℂ) := by
  have he : (fun x => star (ψ x) * masterOp p A ψ x) =
      fun x => (1 / (p.m ^ 2 * p.c ^ 2)) • (kgDensityField p A ψ x : ℂ) -
        p.ellC ^ 2 • boundaryField A ψ x := funext (density_boundary p A hA hψ)
  have hi : Integrable (fun x => (1 / (p.m ^ 2 * p.c ^ 2)) •
      (kgDensityField p A ψ x : ℂ)) A.measure := hfin.ofReal.fun_smul _
  have hb : Integrable (fun x => p.ellC ^ 2 • boundaryField A ψ x) A.measure := hboundary.fun_smul _
  rw [operatorAction, he, integral_sub hi hb,
    integral_smul, integral_smul, sub_add_cancel, integral_complex_ofReal, kgAction]
  simp only [Complex.real_smul, Complex.ofReal_div, Complex.ofReal_one]
  ring

/-- The global normalized master identity equals the actual clock action with its explicit integrated boundary correction. -/
theorem clock_operator_action (p : MassiveParameters) (A : MetricAtlas X) (hA : SmoothLorentz A)
    {ρ τ : X → ℝ} (hρ : Regular A 2 ρ) (hτ : Regular A 2 τ) (hp : ∀ x, 0 < ρ x)
    (hfin : Integrable (kgDensityField p A (ActionDensity.actionField p ρ (clockPhase p τ))) A.measure)
    (hboundary : Integrable (boundaryField A (ActionDensity.actionField p ρ (clockPhase p τ))) A.measure) :
    operatorAction p A (ActionDensity.actionField p ρ (clockPhase p τ)) +
      p.ellC ^ 2 • ∫ x, boundaryField A (ActionDensity.actionField p ρ (clockPhase p τ)) x ∂A.measure =
      (clockAction p A ρ τ : ℂ) := by
  rw [operator_action_boundary p A hA (regular_actionField A p hρ (regular_clockPhase p A hτ) hp)
    hfin hboundary, kg_action_normalized p A hA hρ hτ hp]

/-- With the source's zero integrated boundary condition, the global master operator and clock actions coincide. -/
theorem clock_operator_action_boundary_zero (p : MassiveParameters) (A : MetricAtlas X) (hA : SmoothLorentz A)
    {ρ τ : X → ℝ} (hρ : Regular A 2 ρ) (hτ : Regular A 2 τ) (hp : ∀ x, 0 < ρ x)
    (hfin : Integrable (kgDensityField p A (ActionDensity.actionField p ρ (clockPhase p τ))) A.measure)
    (hboundary : Integrable (boundaryField A (ActionDensity.actionField p ρ (clockPhase p τ))) A.measure)
    (hz : ∫ x, boundaryField A (ActionDensity.actionField p ρ (clockPhase p τ)) x ∂A.measure = 0) :
    operatorAction p A (ActionDensity.actionField p ρ (clockPhase p τ)) = (clockAction p A ρ τ : ℂ) := by
  simpa only [hz, smul_zero, add_zero] using clock_operator_action p A hA hρ hτ hp hfin hboundary

end FoliationQM.CurvedGlobalMaster
