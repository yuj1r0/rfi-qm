module

public import FoliationQM.CurvedAtlasDescent

/-!
# Complex and polar actions on the constructed metric atlas measure

Every coordinate Klein–Gordon density is computed from the actual field
derivative and scalar curvature. Its equality on chart overlaps defines a
global density. A regular positive global density and real action phase
give the same global integrand by the polar identity in each chart.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.CurvedAtlasAction

open Set MeasureTheory LorentzMatrixGroup CurvedMetricChartMeasure CurvedAtlasDescent
open scoped Matrix.Norms.Operator
set_option backward.isDefEq.respectTransparency false

variable {X : Type*} [TopologicalSpace X]

/-- The real quadratic density of the complex field is compatible across all charts in the metric atlas. -/
theorem kgDensity_compatible (p : MassiveParameters) (A : MetricAtlas X) (hA : SmoothLorentz A)
    {ψ : X → ℂ} (hψ : Regular A 2 ψ) :
    Compatible A (fun i => CurvedPolarAction.kgDensity p (A.metric i) (repr A i ψ)) := by
  intro i j x hi hj
  have hk := kinetic_compatible A hA hψ hψ i j x hi hj
  have hs := scalar_compatible A hA i j x hi hj
  simp only [CurvedPolarAction.kgDensity, CurvedKineticCovariance.actionDensity, CurvedPolarAction.massTerm,
    hk, hs, repr_chart A i ψ hi, repr_chart A j ψ hj]

/-- The global complex-field action density is selected from its compatible coordinate expressions. -/
def kgDensityField (p : MassiveParameters) (A : MetricAtlas X) (ψ : X → ℂ) : X → ℝ :=
  descend A (fun i => CurvedPolarAction.kgDensity p (A.metric i) (repr A i ψ))

/-- The global density-action-phase expression is selected from its coordinate polar expressions. -/
def hydroDensityField (p : MassiveParameters) (A : MetricAtlas X) (ρ S : X → ℝ) : X → ℝ :=
  descend A (fun i => CurvedPolarAction.hydroDensity p (A.metric i) (repr A i ρ) (repr A i S))

/-- A global Klein–Gordon density evaluates as its literal coordinate formula in every chart. -/
theorem kgDensityField_chart (p : MassiveParameters) (A : MetricAtlas X) (hA : SmoothLorentz A)
    {ψ : X → ℂ} (hψ : Regular A 2 ψ) (i : ℕ) {x : X} (hx : x ∈ (A.chart i).source) :
    kgDensityField p A ψ x = CurvedPolarAction.kgDensity p (A.metric i) (repr A i ψ) (A.chart i x) :=
  descend_chart A (kgDensity_compatible p A hA hψ) i hx

/-- The polar expression agrees in every chart, using actual global density and action fields. -/
theorem hydroDensity_compatible (p : MassiveParameters) (A : MetricAtlas X) (hA : SmoothLorentz A)
    {ρ S : X → ℝ} (hρ : Regular A 2 ρ) (hS : Regular A 2 S) (hp : ∀ x, 0 < ρ x) :
    Compatible A (fun i => CurvedPolarAction.hydroDensity p (A.metric i) (repr A i ρ) (repr A i S)) := by
  intro i j x hi hj
  have H := kgDensity_compatible p A hA (regular_actionField A p hρ hS hp) i j x hi hj
  dsimp only at H
  have he (k : ℕ) (hk : x ∈ (A.chart k).source) :
      CurvedPolarAction.kgDensity p (A.metric k) (repr A k (ActionDensity.actionField p ρ S)) (A.chart k x) =
        CurvedPolarAction.hydroDensity p (A.metric k) (repr A k ρ) (repr A k S) (A.chart k x) :=
    CurvedPolarAction.density_eq p (A.metric k)
      ((hρ k _ ((A.chart k).map_source hk)).differentiableAt (by decide))
      ((hS k _ ((A.chart k).map_source hk)).differentiableAt (by decide))
      (by simpa only [(A.chart k).left_inv hk] using hp x)
  rw [he i hi, he j hj] at H
  exact H

/-- The polar global density evaluates in any chart containing the point. -/
theorem hydroDensityField_chart (p : MassiveParameters) (A : MetricAtlas X) (hA : SmoothLorentz A)
    {ρ S : X → ℝ} (hρ : Regular A 2 ρ) (hS : Regular A 2 S) (hp : ∀ x, 0 < ρ x)
    (i : ℕ) {x : X} (hx : x ∈ (A.chart i).source) :
    hydroDensityField p A ρ S x =
      CurvedPolarAction.hydroDensity p (A.metric i) (repr A i ρ) (repr A i S) (A.chart i x) :=
  descend_chart A (hydroDensity_compatible p A hA hρ hS hp) i hx

/-- The compatible global complex and polar densities coincide pointwise on every positive-density field. -/
theorem density_eq (p : MassiveParameters) (A : MetricAtlas X) (hA : SmoothLorentz A)
    {ρ S : X → ℝ} (hρ : Regular A 2 ρ) (hS : Regular A 2 S) (hp : ∀ x, 0 < ρ x) :
    kgDensityField p A (ActionDensity.actionField p ρ S) = hydroDensityField p A ρ S := by
  funext x
  obtain ⟨i, hi⟩ := exists_chart A x
  rw [kgDensityField_chart p A hA (regular_actionField A p hρ hS hp) i hi,
    hydroDensityField_chart p A hA hρ hS hp i hi]
  exact CurvedPolarAction.density_eq p (A.metric i)
    ((hρ i _ ((A.chart i).map_source hi)).differentiableAt (by decide))
    ((hS i _ ((A.chart i).map_source hi)).differentiableAt (by decide))
    (by simpa only [(A.chart i).left_inv hi] using hp x)

variable [MeasurableSpace X]

/-- The global curved complex-field action integrates against the constructed atlas metric volume. -/
def kgAction (p : MassiveParameters) (A : MetricAtlas X) (ψ : X → ℂ) : ℝ :=
  ∫ x, kgDensityField p A ψ x ∂A.measure

/-- The global polar action uses the same constructed metric volume. -/
def hydroAction (p : MassiveParameters) (A : MetricAtlas X) (ρ S : X → ℝ) : ℝ :=
  ∫ x, hydroDensityField p A ρ S x ∂A.measure

/-- The global complex action and global polar action are equal for actual regular positive fields. -/
theorem action_eq (p : MassiveParameters) (A : MetricAtlas X) (hA : SmoothLorentz A)
    {ρ S : X → ℝ} (hρ : Regular A 2 ρ) (hS : Regular A 2 S) (hp : ∀ x, 0 < ρ x) :
    kgAction p A (ActionDensity.actionField p ρ S) = hydroAction p A ρ S := by
  rw [kgAction, hydroAction, density_eq p A hA hρ hS hp]

/-- Integrability of either global action density is equivalent to integrability of the other. -/
theorem integrable_iff (p : MassiveParameters) (A : MetricAtlas X) (hA : SmoothLorentz A)
    {ρ S : X → ℝ} (hρ : Regular A 2 ρ) (hS : Regular A 2 S) (hp : ∀ x, 0 < ρ x) :
    Integrable (kgDensityField p A (ActionDensity.actionField p ρ S)) A.measure ↔
      Integrable (hydroDensityField p A ρ S) A.measure := by
  rw [density_eq p A hA hρ hS hp]

/-- The actual finite global complex action is the sum of its disjoint chart contributions with each chart's own metric measure. -/
theorem hasSum_kg_chart_integrals [BorelSpace X] (p : MassiveParameters) (A : MetricAtlas X) (ψ : X → ℂ)
    (hi : Integrable (kgDensityField p A ψ) A.measure) :
    HasSum (fun i => ∫ x in disjointed (fun j => (A.chart j).source) i, kgDensityField p A ψ x
      ∂(chartMeasure (A.chart i) (A.metric i))) (kgAction p A ψ) :=
  A.hasSum_chart_integrals hi

end FoliationQM.CurvedAtlasAction
