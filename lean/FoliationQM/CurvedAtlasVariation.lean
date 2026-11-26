module

public import FoliationQM.CurvedAtlasAction
public import FoliationQM.CurvedChartIntegration
public import FoliationQM.CurvedAtlasTests
public import FoliationQM.CurvedKGEulerLagrange

/-!
# Differentiation of the global action along chart-supported variations

The action difference is integrated with the constructed atlas metric
measure. For a variation supported inside a chart it equals the actual
coordinate relative action, so its derivative and stationarity follow
from the compact-support coordinate Euler–Lagrange theorem.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.CurvedAtlasVariation

open Set Filter MeasureTheory LorentzMatrixGroup CurvedMetricChartMeasure CurvedAtlasDescent CurvedAtlasAction
open scoped Topology Matrix.Norms.Operator ContDiff

variable {X : Type*} [TopologicalSpace X]

/-- Affine variation of a global complex field by a real parameter. -/
def perturb (ψ η : X → ℂ) (t : ℝ) (x : X) : ℂ := ψ x + t • η x

/-- Global coordinate regularity is preserved by affine field variation. -/
theorem regular_perturb (A : MetricAtlas X) {ψ η : X → ℂ}
    (hψ : Regular A 2 ψ) (hη : Regular A 2 η) (t : ℝ) : Regular A 2 (perturb ψ η t) :=
  fun i y hy => (hψ i y hy).add ((contDiffAt_const (c := t)).smul (hη i y hy))

/-- Fields with the same germ have the same descended Klein–Gordon density. -/
theorem density_germ (p : MassiveParameters) (A : MetricAtlas X) (hA : SmoothLorentz A)
    {ψ χ : X → ℂ} (hψ : Regular A 2 ψ) (hχ : Regular A 2 χ) {x : X} (he : ψ =ᶠ[𝓝 x] χ) :
    kgDensityField p A ψ x = kgDensityField p A χ x := by
  obtain ⟨i, hi⟩ := exists_chart A x
  rw [kgDensityField_chart p A hA hψ i hi, kgDensityField_chart p A hA hχ i hi]
  apply CurvedPolarAction.kgDensity_congr
  have hc := (A.chart i).continuousAt_symm ((A.chart i).map_source hi)
  have he' : ∀ᶠ z in 𝓝 ((A.chart i).symm (A.chart i x)), ψ z = χ z := by
    simpa only [(A.chart i).left_inv hi] using (show ∀ᶠ z in 𝓝 x, ψ z = χ z from he)
  exact hc.eventually he'


variable [MeasurableSpace X] [BorelSpace X]

/-- The relative global action uses the actual constructed atlas volume measure. -/
def relativeAction (p : MassiveParameters) (A : MetricAtlas X) (ψ η : X → ℂ) (t : ℝ) : ℝ :=
  ∫ x, kgDensityField p A (perturb ψ η t) x - kgDensityField p A ψ x ∂A.measure

omit [MeasurableSpace X] [BorelSpace X] in
/-- At every point in the test chart, the global density difference is the coordinate perturbation difference. -/
theorem density_difference_chart (p : MassiveParameters) (A : MetricAtlas X) (hA : SmoothLorentz A)
    {ψ η : X → ℂ} (hψ : Regular A 2 ψ) (hη : Regular A 2 η) (i : ℕ)
    {ζ : Covector → ℂ} (hrepr : ∀ y ∈ (A.chart i).target, repr A i η =ᶠ[𝓝 y] ζ)
    (t : ℝ) {y : Covector} (hy : y ∈ (A.chart i).target) :
    kgDensityField p A (perturb ψ η t) ((A.chart i).symm y) -
        kgDensityField p A ψ ((A.chart i).symm y) =
      CurvedPolarAction.kgDensity p (A.metric i) (CurvedKGFirstVariation.perturb (repr A i ψ) ζ t) y -
        CurvedPolarAction.kgDensity p (A.metric i) (repr A i ψ) y := by
  rw [kgDensityField_chart p A hA (regular_perturb A hψ hη t) i ((A.chart i).map_target hy),
    kgDensityField_chart p A hA hψ i ((A.chart i).map_target hy), (A.chart i).right_inv hy]
  have he : repr A i (perturb ψ η t) =ᶠ[𝓝 y] CurvedKGFirstVariation.perturb (repr A i ψ) ζ t := by
    filter_upwards [hrepr y hy] with z hz
    change ψ ((A.chart i).symm z) + t • η ((A.chart i).symm z) = _
    rw [show η ((A.chart i).symm z) = ζ z from hz]
    rfl
  rw [CurvedPolarAction.kgDensity_congr p (A.metric i) he]

/-- A variation that vanishes as a germ outside a chart changes the global action by the coordinate relative action. -/
theorem relativeAction_eq_chart (p : MassiveParameters) (A : MetricAtlas X) (hA : SmoothLorentz A)
    {ψ η : X → ℂ} (hψ : Regular A 2 ψ) (hη : Regular A 2 η) (i : ℕ)
    {ζ : Covector → ℂ} (hrepr : ∀ y ∈ (A.chart i).target, repr A i η =ᶠ[𝓝 y] ζ)
    (hzero : ∀ x ∉ (A.chart i).source, η =ᶠ[𝓝 x] (fun _ => 0)) (t : ℝ) :
    relativeAction p A ψ η t =
      CurvedKGRelativeVariation.relativeAction p (A.metric i) (repr A i ψ) ζ (A.chart i).target t := by
  unfold relativeAction
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := (A.chart i).source) (fun x hx => ?_)]
  · rw [CurvedChartIntegration.integral_chart A i _
      (fun y hy => (hA.metric_smooth i y hy).continuousAt.continuousWithinAt)]
    apply setIntegral_congr_fun (A.chart i).open_target.measurableSet
    intro y hy
    dsimp only
    rw [density_difference_chart p A hA hψ hη i hrepr t hy]
    rfl
  · apply sub_eq_zero.mpr
    apply density_germ p A hA (regular_perturb A hψ hη t) hψ
    filter_upwards [hzero x hx] with y hy
    simp only [perturb, hy, smul_zero, add_zero]

/-- The actual globally integrated relative action has the coordinate compact-support first derivative. -/
theorem hasDerivAt_relative (p : MassiveParameters) (A : MetricAtlas X) (hA : SmoothLorentz A)
    {ψ η : X → ℂ} (hψ : Regular A 2 ψ) (hη : Regular A 2 η) (i : ℕ)
    {ζ : Covector → ℂ} (hrepr : ∀ y ∈ (A.chart i).target, repr A i η =ᶠ[𝓝 y] ζ)
    (hzero : ∀ x ∉ (A.chart i).source, η =ᶠ[𝓝 x] (fun _ => 0))
    (hζ : ContDiff ℝ 2 ζ) (hc : HasCompactSupport ζ) (hs : tsupport ζ ⊆ (A.chart i).target) :
    HasDerivAt (relativeAction p A ψ η)
      (2 * ∫ y in (A.chart i).target, RNCVolumeDensity.volumeFactor (A.metric i y) *
        (CurvedKGFirstVariation.cross p (A.metric i) ζ (repr A i ψ) y).re) 0 := by
  have he := funext (relativeAction_eq_chart p A hA hψ hη i hrepr hzero)
  rw [he]
  exact CurvedKGRelativeVariation.hasDerivAt_relative p (A.chart i).open_target
    (hA.metric_smooth i) (hA.symmetric i) (hA.negative i) (hψ i) hζ hc hs

/-- The globally integrated density difference is genuinely integrable for a compact chart-supported variation. -/
theorem integrable_difference (p : MassiveParameters) (A : MetricAtlas X) (hA : SmoothLorentz A)
    {ψ η : X → ℂ} (hψ : Regular A 2 ψ) (hη : Regular A 2 η) (i : ℕ)
    {ζ : Covector → ℂ} (hrepr : ∀ y ∈ (A.chart i).target, repr A i η =ᶠ[𝓝 y] ζ)
    (hzero : ∀ x ∉ (A.chart i).source, η =ᶠ[𝓝 x] (fun _ => 0))
    (hζ : ContDiff ℝ 2 ζ) (hc : HasCompactSupport ζ) (hs : tsupport ζ ⊆ (A.chart i).target) (t : ℝ) :
    Integrable (fun x => kgDensityField p A (perturb ψ η t) x - kgDensityField p A ψ x) A.measure := by
  have hsupp : Function.support (fun x => kgDensityField p A (perturb ψ η t) x -
      kgDensityField p A ψ x) ⊆ (A.chart i).source := by
    intro x hx
    by_contra hn
    apply hx
    apply sub_eq_zero.mpr
    apply density_germ p A hA (regular_perturb A hψ hη t) hψ
    filter_upwards [hzero x hn] with z hz
    simp only [perturb, hz, smul_zero, add_zero]
  apply (integrableOn_iff_integrable_of_support_subset hsupp).mp
  apply (CurvedChartIntegration.integrable_chart A i _
    (fun y hy => (hA.metric_smooth i y hy).continuousAt.continuousWithinAt)).mpr
  have hi := CurvedKGRelativeVariation.integrable_difference p (A.chart i).open_target
    (hA.metric_smooth i) (hA.symmetric i) (hA.negative i) (hψ i) hζ hc hs t
  apply hi.congr
  filter_upwards [ae_restrict_mem (A.chart i).open_target.measurableSet] with y hy
  rw [density_difference_chart p A hA hψ hη i hrepr t hy]
  rfl

/-- An integrable background action plus the relative variation equals the finite perturbed global action. -/
theorem absolute_eq (p : MassiveParameters) (A : MetricAtlas X) (hA : SmoothLorentz A)
    {ψ η : X → ℂ} (hψ : Regular A 2 ψ) (hη : Regular A 2 η) (i : ℕ)
    {ζ : Covector → ℂ} (hrepr : ∀ y ∈ (A.chart i).target, repr A i η =ᶠ[𝓝 y] ζ)
    (hzero : ∀ x ∉ (A.chart i).source, η =ᶠ[𝓝 x] (fun _ => 0))
    (hζ : ContDiff ℝ 2 ζ) (hc : HasCompactSupport ζ) (hs : tsupport ζ ⊆ (A.chart i).target)
    (hfin : Integrable (kgDensityField p A ψ) A.measure) (t : ℝ) :
    kgAction p A (perturb ψ η t) = relativeAction p A ψ η t + kgAction p A ψ := by
  have hi := integrable_difference p A hA hψ hη i hrepr hzero hζ hc hs t
  unfold kgAction relativeAction
  rw [← integral_add hi hfin]
  congr 1
  funext x
  ring

/-- The finite absolute global action has the same first derivative as its relative action. -/
theorem hasDerivAt_absolute (p : MassiveParameters) (A : MetricAtlas X) (hA : SmoothLorentz A)
    {ψ η : X → ℂ} (hψ : Regular A 2 ψ) (hη : Regular A 2 η) (i : ℕ)
    {ζ : Covector → ℂ} (hrepr : ∀ y ∈ (A.chart i).target, repr A i η =ᶠ[𝓝 y] ζ)
    (hzero : ∀ x ∉ (A.chart i).source, η =ᶠ[𝓝 x] (fun _ => 0))
    (hζ : ContDiff ℝ 2 ζ) (hc : HasCompactSupport ζ) (hs : tsupport ζ ⊆ (A.chart i).target)
    (hfin : Integrable (kgDensityField p A ψ) A.measure) :
    HasDerivAt (fun t => kgAction p A (perturb ψ η t))
      (2 * ∫ y in (A.chart i).target, RNCVolumeDensity.volumeFactor (A.metric i y) *
        (CurvedKGFirstVariation.cross p (A.metric i) ζ (repr A i ψ) y).re) 0 := by
  simp_rw [absolute_eq p A hA hψ hη i hrepr hzero hζ hc hs hfin]
  exact (hasDerivAt_relative p A hA hψ hη i hrepr hzero hζ hc hs).add_const _

variable [T2Space X]

/-- A zero-extended compact chart test gives precisely the coordinate relative action for every parameter. -/
theorem relativeAction_eq_extended (p : MassiveParameters) (A : MetricAtlas X) (hA : SmoothLorentz A)
    {ψ : X → ℂ} (hψ : Regular A 2 ψ) (i : ℕ) {ζ : Covector → ℂ}
    (hζ : ContDiff ℝ 2 ζ) (hc : HasCompactSupport ζ) (hs : tsupport ζ ⊆ (A.chart i).target) :
    relativeAction p A ψ (CurvedAtlasTests.extend A i ζ) =
      CurvedKGRelativeVariation.relativeAction p (A.metric i) (repr A i ψ) ζ (A.chart i).target := by
  funext t
  exact relativeAction_eq_chart p A hA hψ (CurvedAtlasTests.regular_extend A hA i hζ hc hs) i
    (fun _ hy => CurvedAtlasTests.repr_extend_germ A i ζ hy)
    (fun _ hx => CurvedAtlasTests.extend_zero_germ A i hc hs hx) t

/-- Stationarity of the global relative action under every compactly supported smooth test in each chart. -/
def ChartStationary (p : MassiveParameters) (A : MetricAtlas X) (ψ : X → ℂ) : Prop :=
  ∀ (i : ℕ) (ζ : Covector → ℂ), ContDiff ℝ ∞ ζ → HasCompactSupport ζ →
    tsupport ζ ⊆ (A.chart i).target →
      HasDerivAt (relativeAction p A ψ (CurvedAtlasTests.extend A i ζ)) 0 0

/-- Stationarity of the globally integrated action against all chart-supported tests
is equivalent to the descended pointwise Klein–Gordon equation everywhere. -/
theorem chart_stationary_iff (p : MassiveParameters) (A : MetricAtlas X) (hA : SmoothLorentz A)
    {ψ : X → ℂ} (hψ : Regular A 2 ψ) :
    ChartStationary p A ψ ↔ ∀ x, kgOperatorField p A ψ x = 0 := by
  have hlocal (i : ℕ) := CurvedKGEulerLagrange.relative_stationary_iff p (A.chart i).open_target
    (hA.metric_smooth i) (hA.symmetric i) (hA.negative i) (hψ i)
  constructor
  · intro hstat x
    obtain ⟨i, hi⟩ := exists_chart A x
    rw [kgOperatorField_chart p A hA hψ i hi]
    apply (hlocal i).mp _ _ ((A.chart i).map_source hi)
    intro ζ hζ hc hs
    have he := hstat i ζ hζ hc hs
    rwa [relativeAction_eq_extended p A hA hψ i (hζ.of_le (by simp)) hc hs] at he
  · intro hzero i ζ hζ hc hs
    rw [relativeAction_eq_extended p A hA hψ i (hζ.of_le (by simp)) hc hs]
    apply (hlocal i).mpr _ ζ hζ hc hs
    intro y hy
    have he := hzero ((A.chart i).symm y)
    rw [kgOperatorField_chart p A hA hψ i ((A.chart i).map_target hy), (A.chart i).right_inv hy] at he
    exact he

/-- Finite absolute global action stationary against all compactly supported smooth chart tests. -/
def AbsoluteChartStationary (p : MassiveParameters) (A : MetricAtlas X) (ψ : X → ℂ) : Prop :=
  Integrable (kgDensityField p A ψ) A.measure ∧
  ∀ (i : ℕ) (ζ : Covector → ℂ), ContDiff ℝ ∞ ζ → HasCompactSupport ζ →
    tsupport ζ ⊆ (A.chart i).target →
      HasDerivAt (fun t => kgAction p A (perturb ψ (CurvedAtlasTests.extend A i ζ) t)) 0 0

/-- The finite absolute global action is chart-test stationary exactly at the globally defined KG solutions. -/
theorem absolute_chart_stationary_iff (p : MassiveParameters) (A : MetricAtlas X) (hA : SmoothLorentz A)
    {ψ : X → ℂ} (hψ : Regular A 2 ψ) :
    AbsoluteChartStationary p A ψ ↔ Integrable (kgDensityField p A ψ) A.measure ∧
      ∀ x, kgOperatorField p A ψ x = 0 := by
  unfold AbsoluteChartStationary
  apply and_congr_right
  intro hfin
  rw [← chart_stationary_iff p A hA hψ]
  unfold ChartStationary
  apply forall_congr'
  intro i
  apply forall_congr'
  intro ζ
  apply forall_congr'
  intro hζ
  apply forall_congr'
  intro hc
  apply forall_congr'
  intro hs
  have hζ₂ : ContDiff ℝ 2 ζ := hζ.of_le (by simp)
  have hr := CurvedAtlasTests.regular_extend A hA i hζ₂ hc hs
  have he (t : ℝ) := absolute_eq p A hA hψ hr i
    (fun _ hy => CurvedAtlasTests.repr_extend_germ A i ζ hy)
    (fun _ hx => CurvedAtlasTests.extend_zero_germ A i hc hs hx) hζ₂ hc hs hfin t
  simp_rw [he]
  exact hasDerivAt_add_const_iff _

end FoliationQM.CurvedAtlasVariation
