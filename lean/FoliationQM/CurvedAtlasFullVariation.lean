module

public import FoliationQM.CurvedAtlasGlobalGreen

/-!
# Arbitrary compact variations of the global curved action

The exact quadratic density increment has integrable coefficients for every
compact C² global test. Its metric-volume integral is therefore an actual
quadratic polynomial in the variation parameter. Differentiation and the
global Green identity identify stationarity with the global Klein–Gordon
equation. The finite absolute action is treated under explicit background
integrability. These results complete the remaining variational bridge in
v13 `thm:conformal_coupling`.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.CurvedAtlasFullVariation

open Set MeasureTheory CurvedMetricChartMeasure CurvedAtlasDescent CurvedAtlasAction
  CurvedAtlasCross CurvedAtlasCompactIntegrability CurvedAtlasResidualPair CurvedAtlasGlobalGreen
open scoped Topology Matrix.Norms.Operator Manifold ContDiff
set_option backward.isDefEq.respectTransparency false
variable {X : Type*} [TopologicalSpace X]

private theorem increment_eq (p : MassiveParameters) (A : MetricAtlas X) (hA : SmoothLorentz A)
    {ψ η : X → ℂ} (hψ : Regular A 2 ψ) (hη : Regular A 2 η) (t : ℝ) :
    (fun x => kgDensityField p A (CurvedAtlasVariation.perturb ψ η t) x - kgDensityField p A ψ x) =
      fun x => (2 * t) * (crossField p A η ψ x).re + t ^ 2 * kgDensityField p A η x := by
  funext x
  rw [density_perturb p A hA hψ hη]
  ring

variable [MeasurableSpace X] [BorelSpace X] [T2Space X]
  [ChartedSpace Covector X] [IsManifold 𝓘(ℝ, Covector) ∞ X] [SecondCountableTopology X]

/-- Both coefficients of the global compact variation polynomial are absolutely integrable. -/
theorem integrable_coefficients (p : MassiveParameters) (A : MetricAtlas X) (hA : SmoothLorentz A)
    (hcharts : ∀ i, A.chart i ∈ IsManifold.maximalAtlas 𝓘(ℝ, Covector) 2 X)
    {ψ η : X → ℂ} (hψ : Regular A 2 ψ) (hη : Regular A 2 η) (hc : HasCompactSupport η) :
    Integrable (fun x => (crossField p A η ψ x).re) A.measure ∧
      Integrable (kgDensityField p A η) A.measure := by
  refine ⟨?_, integrable_self_density p A hA hcharts hη hc⟩
  simpa only [Function.comp_apply, RCLike.re_eq_complex_re] using
    (integrable_cross p A hA hcharts hη hψ hc).re

/-- Every finite-parameter density increment is integrable for an arbitrary compact C² variation. -/
theorem integrable_difference (p : MassiveParameters) (A : MetricAtlas X) (hA : SmoothLorentz A)
    (hcharts : ∀ i, A.chart i ∈ IsManifold.maximalAtlas 𝓘(ℝ, Covector) 2 X)
    {ψ η : X → ℂ} (hψ : Regular A 2 ψ) (hη : Regular A 2 η) (hc : HasCompactSupport η) (t : ℝ) :
    Integrable (fun x => kgDensityField p A (CurvedAtlasVariation.perturb ψ η t) x -
      kgDensityField p A ψ x) A.measure := by
  obtain ⟨h₁, h₂⟩ := integrable_coefficients p A hA hcharts hψ hη hc
  rw [increment_eq p A hA hψ hη t]
  exact (h₁.const_mul (2 * t)).add (h₂.const_mul (t ^ 2))

/-- Integrating the actual global density increment gives the exact quadratic variation polynomial. -/
theorem relativeAction_eq (p : MassiveParameters) (A : MetricAtlas X) (hA : SmoothLorentz A)
    (hcharts : ∀ i, A.chart i ∈ IsManifold.maximalAtlas 𝓘(ℝ, Covector) 2 X)
    {ψ η : X → ℂ} (hψ : Regular A 2 ψ) (hη : Regular A 2 η) (hc : HasCompactSupport η) (t : ℝ) :
    CurvedAtlasVariation.relativeAction p A ψ η t =
      2 * t * (∫ x, (crossField p A η ψ x).re ∂A.measure) + t ^ 2 * kgAction p A η := by
  obtain ⟨h₁, h₂⟩ := integrable_coefficients p A hA hcharts hψ hη hc
  unfold CurvedAtlasVariation.relativeAction kgAction
  rw [increment_eq p A hA hψ hη t, integral_add (h₁.const_mul (2 * t)) (h₂.const_mul (t ^ 2)),
    integral_const_mul, integral_const_mul]

/-- The actual global relative action has the integrated real cross density as its first derivative. -/
theorem hasDerivAt_relative (p : MassiveParameters) (A : MetricAtlas X) (hA : SmoothLorentz A)
    (hcharts : ∀ i, A.chart i ∈ IsManifold.maximalAtlas 𝓘(ℝ, Covector) 2 X)
    {ψ η : X → ℂ} (hψ : Regular A 2 ψ) (hη : Regular A 2 η) (hc : HasCompactSupport η) :
    HasDerivAt (CurvedAtlasVariation.relativeAction p A ψ η)
      (2 * ∫ x, (crossField p A η ψ x).re ∂A.measure) 0 := by
  rw [show CurvedAtlasVariation.relativeAction p A ψ η = _ from
    funext (relativeAction_eq p A hA hcharts hψ hη hc)]
  convert! (((hasDerivAt_id (0 : ℝ)).const_mul 2).mul_const
    (∫ x, (crossField p A η ψ x).re ∂A.measure)).add
    (((hasDerivAt_id (0 : ℝ)).pow 2).mul_const (kgAction p A η)) using 1
  simp

/-- Global integration by parts identifies the first variation with minus twice the real residual test pairing. -/
theorem hasDerivAt_relative_residual (p : MassiveParameters) (A : MetricAtlas X) (hA : SmoothLorentz A)
    (hcharts : ∀ i, A.chart i ∈ IsManifold.maximalAtlas 𝓘(ℝ, Covector) 2 X)
    {ψ η : X → ℂ} (hψ : Regular A 2 ψ) (hη : Regular A 2 η) (hc : HasCompactSupport η) :
    HasDerivAt (CurvedAtlasVariation.relativeAction p A ψ η)
      (-(2 * ∫ x, (pairField p A η ψ x).re ∂A.measure)) 0 := by
  have H := hasDerivAt_relative p A hA hcharts hψ hη hc
  rw [integral_green_re p A hA hcharts hη hψ hc, mul_neg] at H
  exact H

/-- A finite background action remains finite under every compact C² affine perturbation. -/
theorem integrable_perturbed (p : MassiveParameters) (A : MetricAtlas X) (hA : SmoothLorentz A)
    (hcharts : ∀ i, A.chart i ∈ IsManifold.maximalAtlas 𝓘(ℝ, Covector) 2 X)
    {ψ η : X → ℂ} (hψ : Regular A 2 ψ) (hη : Regular A 2 η) (hc : HasCompactSupport η)
    (hfin : Integrable (kgDensityField p A ψ) A.measure) (t : ℝ) :
    Integrable (kgDensityField p A (CurvedAtlasVariation.perturb ψ η t)) A.measure := by
  have H := (integrable_difference p A hA hcharts hψ hη hc t).add hfin
  convert H using 1
  funext x
  dsimp only [Pi.add_apply]
  ring

/-- The finite absolute action equals its background action plus the actual relative compact change. -/
theorem absolute_eq (p : MassiveParameters) (A : MetricAtlas X) (hA : SmoothLorentz A)
    (hcharts : ∀ i, A.chart i ∈ IsManifold.maximalAtlas 𝓘(ℝ, Covector) 2 X)
    {ψ η : X → ℂ} (hψ : Regular A 2 ψ) (hη : Regular A 2 η) (hc : HasCompactSupport η)
    (hfin : Integrable (kgDensityField p A ψ) A.measure) (t : ℝ) :
    kgAction p A (CurvedAtlasVariation.perturb ψ η t) =
      CurvedAtlasVariation.relativeAction p A ψ η t + kgAction p A ψ := by
  unfold kgAction CurvedAtlasVariation.relativeAction
  rw [← integral_add (integrable_difference p A hA hcharts hψ hη hc t) hfin]
  congr 1
  funext x
  ring

/-- The finite global absolute action has the same residual first derivative for every compact C² variation. -/
theorem hasDerivAt_absolute (p : MassiveParameters) (A : MetricAtlas X) (hA : SmoothLorentz A)
    (hcharts : ∀ i, A.chart i ∈ IsManifold.maximalAtlas 𝓘(ℝ, Covector) 2 X)
    {ψ η : X → ℂ} (hψ : Regular A 2 ψ) (hη : Regular A 2 η) (hc : HasCompactSupport η)
    (hfin : Integrable (kgDensityField p A ψ) A.measure) :
    HasDerivAt (fun t => kgAction p A (CurvedAtlasVariation.perturb ψ η t))
      (-(2 * ∫ x, (pairField p A η ψ x).re ∂A.measure)) 0 := by
  simp_rw [absolute_eq p A hA hcharts hψ hη hc hfin]
  exact (hasDerivAt_relative_residual p A hA hcharts hψ hη hc).add_const _

/-- Global relative stationarity quantifies every compact C² variation, regardless of how many charts meet its support. -/
def RelativeStationary (p : MassiveParameters) (A : MetricAtlas X) (ψ : X → ℂ) : Prop :=
  ∀ η : X → ℂ, Regular A 2 η → HasCompactSupport η →
    HasDerivAt (CurvedAtlasVariation.relativeAction p A ψ η) 0 0

/-- Stationarity under arbitrary compact C² global variations is exactly the pointwise global KG equation. -/
theorem relative_stationary_iff (p : MassiveParameters) (A : MetricAtlas X) (hA : SmoothLorentz A)
    (hcharts : ∀ i, A.chart i ∈ IsManifold.maximalAtlas 𝓘(ℝ, Covector) 2 X)
    {ψ : X → ℂ} (hψ : Regular A 2 ψ) :
    RelativeStationary p A ψ ↔ ∀ x, kgOperatorField p A ψ x = 0 := by
  constructor
  · intro hstat
    apply (CurvedAtlasVariation.chart_stationary_iff p A hA hψ).mp
    intro i ζ hζ hc hs
    exact hstat (CurvedAtlasTests.extend A i ζ)
      (CurvedAtlasTests.regular_extend A hA i (hζ.of_le (by simp)) hc hs)
      (CurvedAtlasTests.extend_compact A i hc hs)
  · intro hzero η hη hc
    have H := hasDerivAt_relative_residual p A hA hcharts hψ hη hc
    simpa only [pairField, residualField, hzero, smul_zero, mul_zero, Complex.zero_re,
      integral_zero, neg_zero] using H

/-- Finite global absolute-action stationarity under every compact C² variation. -/
def AbsoluteStationary (p : MassiveParameters) (A : MetricAtlas X) (ψ : X → ℂ) : Prop :=
  Integrable (kgDensityField p A ψ) A.measure ∧
    ∀ η : X → ℂ, Regular A 2 η → HasCompactSupport η →
      HasDerivAt (fun t => kgAction p A (CurvedAtlasVariation.perturb ψ η t)) 0 0

/-- Finite absolute stationarity and relative stationarity are equivalent for the full compact test class. -/
theorem absolute_iff_relative (p : MassiveParameters) (A : MetricAtlas X) (hA : SmoothLorentz A)
    (hcharts : ∀ i, A.chart i ∈ IsManifold.maximalAtlas 𝓘(ℝ, Covector) 2 X)
    {ψ : X → ℂ} (hψ : Regular A 2 ψ) :
    AbsoluteStationary p A ψ ↔ Integrable (kgDensityField p A ψ) A.measure ∧ RelativeStationary p A ψ := by
  unfold AbsoluteStationary
  apply and_congr_right
  intro hfin
  unfold RelativeStationary
  apply forall_congr'
  intro η
  apply forall_congr'
  intro hη
  apply forall_congr'
  intro hc
  simp_rw [absolute_eq p A hA hcharts hψ hη hc hfin]
  exact hasDerivAt_add_const_iff _

/-- The finite global action is stationary under all compact C² variations exactly at the global KG solutions. -/
theorem absolute_stationary_iff (p : MassiveParameters) (A : MetricAtlas X) (hA : SmoothLorentz A)
    (hcharts : ∀ i, A.chart i ∈ IsManifold.maximalAtlas 𝓘(ℝ, Covector) 2 X)
    {ψ : X → ℂ} (hψ : Regular A 2 ψ) :
    AbsoluteStationary p A ψ ↔ Integrable (kgDensityField p A ψ) A.measure ∧
      ∀ x, kgOperatorField p A ψ x = 0 := by
  rw [absolute_iff_relative p A hA hcharts hψ, relative_stationary_iff p A hA hcharts hψ]

end FoliationQM.CurvedAtlasFullVariation
