module

public import FoliationQM.CurvedAtlasGlobalGreen
public import FoliationQM.CurvedAtlasFullVariation
public import FoliationQM.CurvedNormalizedOperator

/-!
# Global independent variation of the conjugated field

The two slots of the complex polarized action can vary independently.
Varying the conjugated slot by a compact global test gives an integrable
action difference without any finiteness premise on the background.
Its actual derivative is the complex tested Euler–Lagrange residual.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.CurvedAtlasIndependentVariation

open Set MeasureTheory CurvedMetricChartMeasure CurvedAtlasDescent CurvedAtlasCross
  CurvedAtlasResidualPair CurvedAtlasCompactIntegrability CurvedAtlasGlobalGreen
open scoped Topology Manifold ContDiff
set_option backward.isDefEq.respectTransparency false

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X]

/-- The actual relative complex action obtained by varying only the conjugated field slot. -/
def leftRelative (p : MassiveParameters) (A : MetricAtlas X) (χ ψ η : X → ℂ) (t : ℝ) : ℂ :=
  ∫ x, crossField p A (CurvedAtlasVariation.perturb χ η t) ψ x - crossField p A χ ψ x ∂A.measure

/-- The independent conjugate-slot action difference is exactly linear in its real parameter. -/
theorem leftRelative_eq (p : MassiveParameters) (A : MetricAtlas X) (hA : SmoothLorentz A)
    {χ ψ η : X → ℂ} (hχ : Regular A 2 χ) (hψ : Regular A 2 ψ) (hη : Regular A 2 η) (t : ℝ) :
    leftRelative p A χ ψ η t = t • ∫ x, crossField p A η ψ x ∂A.measure := by
  unfold leftRelative
  rw [crossField_perturb_left p A hA hχ hη hψ t]
  simp only [Pi.add_apply, Pi.smul_apply, add_sub_cancel_left, integral_smul]

/-- The derivative of the relative polarized functional is its complex cross integral. -/
theorem hasDerivAt_left_cross (p : MassiveParameters) (A : MetricAtlas X) (hA : SmoothLorentz A)
    {χ ψ η : X → ℂ} (hχ : Regular A 2 χ) (hψ : Regular A 2 ψ) (hη : Regular A 2 η) (t : ℝ) :
    HasDerivAt (leftRelative p A χ ψ η) (∫ x, crossField p A η ψ x ∂A.measure) t := by
  have he := funext (leftRelative_eq p A hA hχ hψ hη)
  rw [he]
  simpa only [one_smul, id_eq] using!
    (hasDerivAt_id t).smul_const (∫ x, crossField p A η ψ x ∂A.measure)

/-- The actual complex polarized action integrated against the constructed metric measure. -/
def polarizedAction (p : MassiveParameters) (A : MetricAtlas X) (χ ψ : X → ℂ) : ℂ :=
  ∫ x, crossField p A χ ψ x ∂A.measure

omit [MeasurableSpace X] in
/-- The diagonal of the independent two-field density is exactly the real physical action density. -/
theorem crossField_self_complex (p : MassiveParameters) (A : MetricAtlas X) (hA : SmoothLorentz A)
    {ψ : X → ℂ} (hψ : Regular A 2 ψ) (x : X) :
    crossField p A ψ ψ x = (CurvedAtlasAction.kgDensityField p A ψ x : ℂ) := by
  obtain ⟨i, hi⟩ := exists_chart A x
  rw [crossField_chart p A hA hψ hψ i hi, CurvedAtlasAction.kgDensityField_chart p A hA hψ i hi]
  exact (CurvedNormalizedOperator.cross_self_complex p
    (hA.symmetric i _ ((A.chart i).map_source hi)) _).symm

/-- Restricting the polarized action to equal field slots recovers the actual physical action. -/
theorem polarizedAction_self (p : MassiveParameters) (A : MetricAtlas X) (hA : SmoothLorentz A)
    {ψ : X → ℂ} (hψ : Regular A 2 ψ) :
    polarizedAction p A ψ ψ = (CurvedAtlasAction.kgAction p A ψ : ℂ) := by
  simp only [polarizedAction, crossField_self_complex p A hA hψ,
    CurvedAtlasAction.kgAction, integral_complex_ofReal]

variable [BorelSpace X] [T2Space X] [ChartedSpace Covector X] [IsManifold 𝓘(ℝ, Covector) ∞ X]
  [SecondCountableTopology X]

/-- Compact C² variations give an integrable action difference even without an integrable background. -/
theorem integrable_difference (p : MassiveParameters) (A : MetricAtlas X) (hA : SmoothLorentz A)
    (hcharts : ∀ i, A.chart i ∈ IsManifold.maximalAtlas 𝓘(ℝ, Covector) 2 X)
    {χ ψ η : X → ℂ} (hχ : Regular A 2 χ) (hψ : Regular A 2 ψ) (hη : Regular A 2 η)
    (hc : HasCompactSupport η) (t : ℝ) :
    Integrable (fun x => crossField p A (CurvedAtlasVariation.perturb χ η t) ψ x -
      crossField p A χ ψ x) A.measure := by
  rw [crossField_perturb_left p A hA hχ hη hψ t]
  simpa only [Pi.add_apply, Pi.smul_apply, add_sub_cancel_left] using
    Integrable.fun_smul t (integrable_cross p A hA hcharts hη hψ hc)

/-- Independent compact conjugate-field variation has the actual negative complex residual pairing as derivative. -/
theorem left_derivative (p : MassiveParameters) (A : MetricAtlas X) (hA : SmoothLorentz A)
    (hcharts : ∀ i, A.chart i ∈ IsManifold.maximalAtlas 𝓘(ℝ, Covector) 2 X)
    {χ ψ η : X → ℂ} (hχ : Regular A 2 χ) (hψ : Regular A 2 ψ) (hη : Regular A 2 η)
    (hc : HasCompactSupport η) :
    HasDerivAt (leftRelative p A χ ψ η) (-(∫ x, pairField p A η ψ x ∂A.measure)) 0 := by
  rw [← integral_green p A hA hcharts hη hψ hc]
  exact hasDerivAt_left_cross p A hA hχ hψ hη 0

/-- A finite background polarized action remains integrable under a compact independent variation. -/
theorem integrable_perturbed (p : MassiveParameters) (A : MetricAtlas X) (hA : SmoothLorentz A)
    (hcharts : ∀ i, A.chart i ∈ IsManifold.maximalAtlas 𝓘(ℝ, Covector) 2 X)
    {χ ψ η : X → ℂ} (hχ : Regular A 2 χ) (hψ : Regular A 2 ψ) (hη : Regular A 2 η)
    (hc : HasCompactSupport η) (hfin : Integrable (crossField p A χ ψ) A.measure) (t : ℝ) :
    Integrable (crossField p A (CurvedAtlasVariation.perturb χ η t) ψ) A.measure := by
  rw [crossField_perturb_left p A hA hχ hη hψ t]
  exact hfin.add ((integrable_cross p A hA hcharts hη hψ hc).smul t)

/-- A finite absolute polarized action equals its background plus the actual relative action. -/
theorem polarizedAction_eq (p : MassiveParameters) (A : MetricAtlas X) (hA : SmoothLorentz A)
    (hcharts : ∀ i, A.chart i ∈ IsManifold.maximalAtlas 𝓘(ℝ, Covector) 2 X)
    {χ ψ η : X → ℂ} (hχ : Regular A 2 χ) (hψ : Regular A 2 ψ) (hη : Regular A 2 η)
    (hc : HasCompactSupport η) (hfin : Integrable (crossField p A χ ψ) A.measure) (t : ℝ) :
    polarizedAction p A (CurvedAtlasVariation.perturb χ η t) ψ =
      polarizedAction p A χ ψ + leftRelative p A χ ψ η t := by
  rw [leftRelative_eq p A hA hχ hψ hη t]
  unfold polarizedAction
  rw [crossField_perturb_left p A hA hχ hη hψ t]
  simp only [Pi.add_apply, Pi.smul_apply]
  have ht := Integrable.fun_smul t (integrable_cross p A hA hcharts hη hψ hc)
  rw [integral_add hfin ht, integral_smul]

/-- Finite absolute polarized action has the same independent conjugate-slot derivative as the relative action. -/
theorem hasDerivAt_polarizedAction (p : MassiveParameters) (A : MetricAtlas X) (hA : SmoothLorentz A)
    (hcharts : ∀ i, A.chart i ∈ IsManifold.maximalAtlas 𝓘(ℝ, Covector) 2 X)
    {χ ψ η : X → ℂ} (hχ : Regular A 2 χ) (hψ : Regular A 2 ψ) (hη : Regular A 2 η)
    (hc : HasCompactSupport η) (hfin : Integrable (crossField p A χ ψ) A.measure) :
    HasDerivAt (fun t => polarizedAction p A (CurvedAtlasVariation.perturb χ η t) ψ)
      (-(∫ x, pairField p A η ψ x ∂A.measure)) 0 := by
  simp_rw [polarizedAction_eq p A hA hcharts hχ hψ hη hc hfin]
  exact (left_derivative p A hA hcharts hχ hψ hη hc).const_add _

/-- Stationarity under all compact C² independent variations of the conjugated field slot. -/
def LeftStationary (p : MassiveParameters) (A : MetricAtlas X) (χ ψ : X → ℂ) : Prop :=
  ∀ η : X → ℂ, Regular A 2 η → HasCompactSupport η →
    HasDerivAt (leftRelative p A χ ψ η) 0 0

/-- Independent conjugate-slot stationarity is equivalent to the pointwise global Klein–Gordon equation. -/
theorem left_stationary_iff (p : MassiveParameters) (A : MetricAtlas X) (hA : SmoothLorentz A)
    (hcharts : ∀ i, A.chart i ∈ IsManifold.maximalAtlas 𝓘(ℝ, Covector) 2 X)
    {χ ψ : X → ℂ} (hχ : Regular A 2 χ) (hψ : Regular A 2 ψ) :
    LeftStationary p A χ ψ ↔ ∀ x, kgOperatorField p A ψ x = 0 := by
  constructor
  · intro hs
    apply (CurvedAtlasFullVariation.relative_stationary_iff p A hA hcharts hψ).mp
    intro η hη hc
    have hz : (∫ x, pairField p A η ψ x ∂A.measure) = 0 :=
      neg_eq_zero.mp ((left_derivative p A hA hcharts hχ hψ hη hc).unique (hs η hη hc))
    have hr : (∫ x, (pairField p A η ψ x).re ∂A.measure) = 0 := by
      calc
        _ = (∫ x, pairField p A η ψ x ∂A.measure).re := by
          simpa only [RCLike.re_eq_complex_re] using
            integral_re (integrable_pair p A hA hcharts hη hψ hc)
        _ = 0 := by rw [hz, Complex.zero_re]
    simpa only [hr, mul_zero, neg_zero] using
      CurvedAtlasFullVariation.hasDerivAt_relative_residual p A hA hcharts hψ hη hc
  · intro hz η hη hc
    simpa only [pairField, residualField, hz, smul_zero, mul_zero, integral_zero, neg_zero] using
      left_derivative p A hA hcharts hχ hψ hη hc

end FoliationQM.CurvedAtlasIndependentVariation
