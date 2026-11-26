module

public import FoliationQM.ObserverOscillatingBox
public import FoliationQM.ObserverPrescribedFactor
public import FoliationQM.ObserverShapeStability

/-!
# A fixed-box test using actual measured current densities

The phases realize the oscillating factors on the same initial slice.
Their separately normalized shapes converge in L¹, yet the raw traces
stay equal to 2π. The construction specifies smooth polar fields and
their currents on this slice.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.ObserverCurrentFisherLimitTest

open MeasureTheory Filter LorentzCoordinates FisherNormalization ObserverNormalizedShape
open ObserverOscillatingBox ObserverOscillatingFactor ObserverGaussianFisher
open scoped ContDiff Topology

/-- Initial measured flux for the prescribed phase realizing the kth oscillating multiplier. -/
def flux (p : MassiveParameters) (k : ℕ) : Spatial → ℝ :=
  ObserverSliceFisher.measured p (fun _ => 1) (ObserverPrescribedFactor.action p (factor k)) 0

/-- The measured current density agrees with the oscillating factor at every spatial point. -/
theorem flux_eq (p : MassiveParameters) (k : ℕ) : flux p k = factor k := by
  funext y
  exact ObserverPrescribedFactor.measured_eq p (factor k) y
    ((factor_smooth k).differentiable (by simp) y)

/-- The normalized measured shapes converge in L¹ on the fixed box of volume π. -/
theorem shapes_converge (p : MassiveParameters) :
    let μ := (volume : Measure Spatial).restrict box
    Tendsto (fun k => ∫ y, |shape μ (flux p k) y - shape μ (fun _ => 1) y| ∂μ) atTop (𝓝 0) := by
  dsimp only
  simp_rw [flux_eq]
  let μ := (volume : Measure Spatial).restrict box
  let _ : IsFiniteMeasure μ := by
    constructor
    simp [μ, box_volume]
  have hm : 0 < mass μ (fun _ => (1:ℝ)) := by
    simp [mass, μ, integral_const, measureReal_def, box_volume, Real.pi_pos.le, Real.pi_pos]
  have h := ObserverShapeStability.shape_l1_tendsto (μ := μ) atTop factor
    (fun k => 4*(frequency k)⁻¹ + 4*((frequency k)⁻¹)^2) (ρ := fun _ => 1)
    (integrable_const 1) (Eventually.of_forall fun _ => zero_le_one) hm envelope_tendsto
  have hf (k : ℕ) : AEMeasurable (factor k) μ ∧
      0 ≤ 4*(frequency k)⁻¹ + 4*((frequency k)⁻¹)^2 ∧
      ∀ᵐ y ∂μ, |factor k y - 1| ≤ 4*(frequency k)⁻¹ + 4*((frequency k)⁻¹)^2 := by
    have hk := frequency_pos k
    exact ⟨(factor_smooth k).continuous.aemeasurable, by positivity,
      Eventually.of_forall (factor_error k)⟩
  simpa only [mul_one] using h (Eventually.of_forall hf)

/-- Uniform convergence of the actual current densities and L¹ convergence of their
separately normalized shapes coexist with an exact nonzero Fisher gap on the same region. -/
theorem measured_counterexample (p : MassiveParameters) :
    let μ := (volume : Measure Spatial).restrict box
    TendstoUniformly (flux p) (fun _ => 1) atTop ∧
      Tendsto (fun k => ∫ y, |shape μ (flux p k) y - shape μ (fun _ => 1) y| ∂μ) atTop (𝓝 0) ∧
      (∀ k, fisherTrace (flux p k) axes μ = 2*Real.pi) ∧ fisherTrace (fun _ => 1) axes μ = 0 := by
  refine ⟨?_, shapes_converge p, fun k => (congrArg (fun f => fisherTrace f axes (volume.restrict box)) (flux_eq p k)).trans (trace_value k), unit_trace⟩
  simpa only [show flux p = factor from funext (flux_eq p)] using uniform_to_one

end FoliationQM.ObserverCurrentFisherLimitTest
