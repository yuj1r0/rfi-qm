module

public import FoliationQM.CurvedAtlasCross
public import FoliationQM.CurvedAtlasCompactPartition

/-!
# Integrability of compact global variation densities

Chart tests give genuinely integrable polarized action densities under the
constructed metric measure. A finite smooth partition then proves this
for arbitrary compact C² global tests, even when their support crosses
several coordinate charts.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.CurvedAtlasCompactIntegrability

open Set Filter MeasureTheory CurvedMetricChartMeasure CurvedAtlasDescent
  CurvedAtlasAction CurvedAtlasCross CurvedAtlasTests
open scoped Topology Manifold ContDiff Matrix.Norms.Operator
set_option backward.isDefEq.respectTransparency false

variable {X : Type*} [TopologicalSpace X]

/-- A coordinate germ of the test identifies the literal local polarized density. -/
theorem cross_chart_germ (p : MassiveParameters) (A : MetricAtlas X) (hA : SmoothLorentz A)
    {η ψ : X → ℂ} (hη : Regular A 2 η) (hψ : Regular A 2 ψ) (i : ℕ)
    {ζ : Covector → ℂ} {y : Covector} (hy : y ∈ (A.chart i).target)
    (hrepr : repr A i η =ᶠ[𝓝 y] ζ) :
    crossField p A η ψ ((A.chart i).symm y) =
      CurvedKGFirstVariation.cross p (A.metric i) ζ (repr A i ψ) y := by
  rw [crossField_chart p A hA hη hψ i ((A.chart i).map_target hy), (A.chart i).right_inv hy]
  simp only [CurvedKGFirstVariation.cross, CurvedFluxGreen.kinetic,
    hrepr.fderiv_eq (𝕜 := ℝ), hrepr.self_of_nhds]

variable [MeasurableSpace X] [BorelSpace X]

/-- A chart-local test gives the actual volume-weighted coordinate cross integral. -/
theorem integral_cross_chart (p : MassiveParameters) (A : MetricAtlas X) (hA : SmoothLorentz A)
    {η ψ : X → ℂ} (hη : Regular A 2 η) (hψ : Regular A 2 ψ) (i : ℕ)
    {ζ : Covector → ℂ} (hrepr : ∀ y ∈ (A.chart i).target, repr A i η =ᶠ[𝓝 y] ζ)
    (hzero : ∀ x ∉ (A.chart i).source, η =ᶠ[𝓝 x] (fun _ => 0)) :
    (∫ x, crossField p A η ψ x ∂A.measure) =
      ∫ y in (A.chart i).target, RNCVolumeDensity.volumeFactor (A.metric i y) •
        CurvedKGFirstVariation.cross p (A.metric i) ζ (repr A i ψ) y := by
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := (A.chart i).source)
    (fun x hx => crossField_zero_germ p A hA hη hψ (hzero x hx))]
  rw [CurvedChartIntegration.integral_chart A i _
    (fun y hy => (hA.metric_smooth i y hy).continuousAt.continuousWithinAt)]
  apply setIntegral_congr_fun (A.chart i).open_target.measurableSet
  intro y hy
  dsimp only
  rw [cross_chart_germ p A hA hη hψ i hy (hrepr y hy)]

/-- A compact coordinate test yields a genuinely integrable global cross density. -/
theorem integrable_cross_chart (p : MassiveParameters) (A : MetricAtlas X) (hA : SmoothLorentz A)
    {η ψ : X → ℂ} (hη : Regular A 2 η) (hψ : Regular A 2 ψ) (i : ℕ)
    {ζ : Covector → ℂ} (hrepr : ∀ y ∈ (A.chart i).target, repr A i η =ᶠ[𝓝 y] ζ)
    (hzero : ∀ x ∉ (A.chart i).source, η =ᶠ[𝓝 x] (fun _ => 0))
    (hζ : ContDiff ℝ 2 ζ) (hc : HasCompactSupport ζ) (hs : tsupport ζ ⊆ (A.chart i).target) :
    Integrable (crossField p A η ψ) A.measure := by
  have hsupp : Function.support (crossField p A η ψ) ⊆ (A.chart i).source := by
    intro x hx
    by_contra hn
    exact hx (crossField_zero_germ p A hA hη hψ (hzero x hn))
  apply (integrableOn_iff_integrable_of_support_subset hsupp).mp
  apply (CurvedChartIntegration.integrable_chart A i _
    (fun y hy => (hA.metric_smooth i y hy).continuousAt.continuousWithinAt)).mpr
  have hi := CurvedKGTestResidual.integrable_cross p (hζ.of_le (by decide)) hc hs
    (hA.metric_smooth i) (hA.negative i) (hψ i)
  apply hi.congr
  filter_upwards [ae_restrict_mem (A.chart i).open_target.measurableSet] with y hy
  rw [cross_chart_germ p A hA hη hψ i hy (hrepr y hy)]

variable [T2Space X]

/-- A compact test extended from one chart has exactly its coordinate cross integral. -/
theorem integral_cross_extended (p : MassiveParameters) (A : MetricAtlas X) (hA : SmoothLorentz A)
    {ψ : X → ℂ} (hψ : Regular A 2 ψ) (i : ℕ) {ζ : Covector → ℂ}
    (hζ : ContDiff ℝ 2 ζ) (hc : HasCompactSupport ζ) (hs : tsupport ζ ⊆ (A.chart i).target) :
    (∫ x, crossField p A (extend A i ζ) ψ x ∂A.measure) =
      ∫ y in (A.chart i).target, RNCVolumeDensity.volumeFactor (A.metric i y) •
        CurvedKGFirstVariation.cross p (A.metric i) ζ (repr A i ψ) y :=
  integral_cross_chart p A hA (regular_extend A hA i hζ hc hs) hψ i
    (fun _ hy => repr_extend_germ A i ζ hy) (fun _ hx => extend_zero_germ A i hc hs hx)

/-- Extending a compact coordinate test gives an integrable global cross density. -/
theorem integrable_cross_extended (p : MassiveParameters) (A : MetricAtlas X) (hA : SmoothLorentz A)
    {ψ : X → ℂ} (hψ : Regular A 2 ψ) (i : ℕ) {ζ : Covector → ℂ}
    (hζ : ContDiff ℝ 2 ζ) (hc : HasCompactSupport ζ) (hs : tsupport ζ ⊆ (A.chart i).target) :
    Integrable (crossField p A (extend A i ζ) ψ) A.measure :=
  integrable_cross_chart p A hA (regular_extend A hA i hζ hc hs) hψ i
    (fun _ hy => repr_extend_germ A i ζ hy) (fun _ hx => extend_zero_germ A i hc hs hx) hζ hc hs

variable [ChartedSpace Covector X] [IsManifold 𝓘(ℝ, Covector) ∞ X] [SecondCountableTopology X]

/-- Every compact C² global test has an integrable polarized density against a regular field. -/
theorem integrable_cross (p : MassiveParameters) (A : MetricAtlas X) (hA : SmoothLorentz A)
    (hcharts : ∀ i, A.chart i ∈ IsManifold.maximalAtlas 𝓘(ℝ, Covector) 2 X)
    {η ψ : X → ℂ} (hη : Regular A 2 η) (hψ : Regular A 2 ψ) (hc : HasCompactSupport η) :
    Integrable (crossField p A η ψ) A.measure := by
  obtain ⟨s, θ, hθ, he⟩ := CurvedAtlasCompactPartition.exists_coordinate_decomposition A hcharts hη hc
  rw [he, crossField_sum_left p A hA s (fun i _ => (hθ i).2.2.2.1) hψ]
  convert integrable_finsetSum s (fun i _ =>
    integrable_cross_extended p A hA hψ i (hθ i).1 (hθ i).2.1 (hθ i).2.2.1) using 1
  funext x
  exact Finset.sum_apply x s (fun i => crossField p A (extend A i (θ i)) ψ)

/-- The actual quadratic action density of a compact regular global field is integrable. -/
theorem integrable_self_density (p : MassiveParameters) (A : MetricAtlas X) (hA : SmoothLorentz A)
    (hcharts : ∀ i, A.chart i ∈ IsManifold.maximalAtlas 𝓘(ℝ, Covector) 2 X)
    {η : X → ℂ} (hη : Regular A 2 η) (hc : HasCompactSupport η) :
    Integrable (kgDensityField p A η) A.measure := by
  have hi := (integrable_cross p A hA hcharts hη hη hc).re
  simpa only [Function.comp_apply, RCLike.re_eq_complex_re, crossField_self_re p A hA hη] using hi

end FoliationQM.CurvedAtlasCompactIntegrability
