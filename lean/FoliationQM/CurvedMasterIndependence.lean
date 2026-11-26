module

public import FoliationQM.CurvedGlobalMaster
public import FoliationQM.CurvedAtlasIndependence

/-!
# Atlas independence of the global master and boundary actions

Compatible C³ coordinate atlases compute the same wave, scalar curvature
and kinetic pairing. Consequently the normalized master operator,
its actual boundary scalar and their metric-volume integrals agree.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.CurvedMasterIndependence

open MeasureTheory CurvedMetricChartMeasure CurvedAtlasDescent CurvedAtlasIndependence
  CurvedGlobalMaster
variable {X : Type*} [TopologicalSpace X] {A B : MetricAtlas X}

/-- Compatible regular atlases compute exactly the same global normalized master operator. -/
theorem masterOp_eq (p : MassiveParameters) (h : CrossTransition A B) (hA : SmoothLorentz A)
    (hB : SmoothLorentz B) {ψ : X → ℂ} (hψA : Regular A 2 ψ) (hψB : Regular B 2 ψ) :
    masterOp p A ψ = masterOp p B ψ := by
  funext x
  rw [masterOp, masterOp, waveField_eq h hA hB hψA hψB, scalarField_eq h hA hB]

/-- The actual divergence per unit metric volume is independent of the compatible atlas. -/
theorem boundaryField_eq (h : CrossTransition A B) (hA : SmoothLorentz A)
    (hB : SmoothLorentz B) {ψ : X → ℂ} (hψA : Regular A 2 ψ) (hψB : Regular B 2 ψ) :
    boundaryField A ψ = boundaryField B ψ := by
  funext x
  rw [boundaryField, boundaryField, waveField_eq h hA hB hψA hψB,
    kineticField_eq h hA hB hψA hψA hψB hψB]

variable [MeasurableSpace X] [BorelSpace X]

/-- Compatible atlases give the same complex master operator action under the constructed metric measure. -/
theorem operatorAction_eq (p : MassiveParameters) (h : CrossTransition A B) (hA : SmoothLorentz A)
    (hB : SmoothLorentz B) {ψ : X → ℂ} (hψA : Regular A 2 ψ) (hψB : Regular B 2 ψ) :
    operatorAction p A ψ = operatorAction p B ψ := by
  rw [operatorAction, operatorAction, masterOp_eq p h hA hB hψA hψB, measure_eq h]

/-- The integrated global boundary correction agrees across compatible regular atlases. -/
theorem boundary_integral_eq (h : CrossTransition A B) (hA : SmoothLorentz A)
    (hB : SmoothLorentz B) {ψ : X → ℂ} (hψA : Regular A 2 ψ) (hψB : Regular B 2 ψ) :
    (∫ x, boundaryField A ψ x ∂A.measure) = ∫ x, boundaryField B ψ x ∂B.measure := by
  rw [boundaryField_eq h hA hB hψA hψB, measure_eq h]

/-- The global normalized clock action is unchanged by a compatible atlas with the same positive regular fields. -/
theorem clockAction_eq (p : MassiveParameters) (h : CrossTransition A B) (hA : SmoothLorentz A)
    (hB : SmoothLorentz B) {ρ τ : X → ℝ} (hρA : Regular A 2 ρ) (hτA : Regular A 2 τ)
    (hρB : Regular B 2 ρ) (hτB : Regular B 2 τ) (hp : ∀ x, 0 < ρ x) :
    clockAction p A ρ τ = clockAction p B ρ τ := by
  rw [← kg_action_normalized p A hA hρA hτA hp,
    ← kg_action_normalized p B hB hρB hτB hp,
    CurvedAtlasIndependence.kgAction_eq p h hA hB
      (regular_actionField A p hρA (regular_clockPhase p A hτA) hp)
      (regular_actionField B p hρB (regular_clockPhase p B hτB) hp)]

end FoliationQM.CurvedMasterIndependence
