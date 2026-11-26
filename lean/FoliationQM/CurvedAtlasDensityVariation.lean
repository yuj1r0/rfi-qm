module

public import FoliationQM.CurvedDensityVariation
public import FoliationQM.CurvedAtlasVariation
public import FoliationQM.CurvedGlobalMaster

/-!
# Variation of the density alone on a curved metric atlas

Source: v13 `sec:master_equation`, statement (III) with
`eq:master_dressed_mass`: "Stationary variation of
`eq:master_variational_equivalence` with respect to `ρ(x)`" gives the dressed
mass relation, component kinds B and C. On a regular Lorentzian metric atlas
let `ρ > 0` and `S` be twice continuously differentiable. For a smooth
compactly supported `ζ` in one chart image, extended by zero, the globally
integrated density–phase action of `ρ + t ζ` minus that of `ρ`, at the same
`S`, is differentiable in `t` at zero, and its derivative is the chart
integral of `√(-g) ζ` times the Hamilton–Jacobi residual. Hence the global
action is stationary under all such variations of the density alone exactly
when, in every chart, `g(∂S,∂S)/m² = c² (1 + q)` with
`q = ℓ_C² (□_g √ρ/√ρ − 𝓡/6)`. With `S = −mc² τ` this is statement (III) for a
density and a real clock.

For small `t` the perturbed density is positive everywhere, so the global
integrand is the coordinate one in the chart and vanishes off it; the
coordinate theorem then applies. Only differences of actions are integrated.
The clock is a real function on the whole space; circle-valued clocks around
nodes are outside this statement.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.CurvedAtlasDensityVariation

open MeasureTheory Set Filter LorentzMatrixGroup RNCVolumeDensity CurvedMetricChartMeasure
open CurvedAtlasDescent CurvedAtlasAction CurvedAtlasTests CurvedPolarKG CurvedGradientCovariance
open CurvedClockNormalization
open scoped ContDiff Topology Matrix.Norms.Operator

variable {X : Type*} [TopologicalSpace X] {ρ S : X → ℝ} {ζ : Covector → ℝ}

/-- For small parameters the density perturbed by a chart-supported test is
positive everywhere. -/
theorem eventually_pos (A : MetricAtlas X) (hρ : Regular A 2 ρ) (hp : ∀ x, 0 < ρ x) (i : ℕ)
    (hζ : Continuous ζ) (hc : HasCompactSupport ζ) (hs : tsupport ζ ⊆ (A.chart i).target) :
    ∀ᶠ t in 𝓝 (0 : ℝ), ∀ x, 0 < ρ x + t * extend A i ζ x := by
  have hK : IsCompact (tsupport ζ) := hc
  have hcont : ContinuousOn (repr A i ρ) (tsupport ζ) := fun y hy =>
    (hρ i y (hs hy)).continuousAt.continuousWithinAt
  obtain ⟨m, hm, hmK⟩ := hK.exists_forall_le' (f := repr A i ρ) hcont (a := 0)
    (fun y _ => hp _)
  obtain ⟨C, hC⟩ := hc.exists_bound_of_continuous hζ
  have hC1 : 0 < |C| + 1 := by positivity
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ) (div_pos hm hC1)] with t ht x
  rw [mem_ball_zero_iff, Real.norm_eq_abs, lt_div_iff₀ hC1] at ht
  by_cases hx : x ∈ (A.chart i).source
  · rw [extend_apply A i ζ hx]
    by_cases hy : A.chart i x ∈ tsupport ζ
    · have h1 := hmK _ hy
      rw [repr_chart A i ρ hx] at h1
      have h2 : |ζ (A.chart i x)| ≤ |C| + 1 := by
        have := hC (A.chart i x)
        rw [Real.norm_eq_abs] at this
        exact this.trans ((le_abs_self C).trans (by linarith))
      have h3 : |t * ζ (A.chart i x)| ≤ |t| * (|C| + 1) := by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
      have h4 := neg_abs_le (t * ζ (A.chart i x))
      linarith
    · rw [image_eq_zero_of_notMem_tsupport hy, mul_zero, add_zero]
      exact hp x
  · rw [extend_zero A i ζ hx, mul_zero, add_zero]
    exact hp x

variable [T2Space X] [MeasurableSpace X] [BorelSpace X]

/-- The globally integrated action of the density `ρ + t a` minus that of
`ρ`, at the same phase. -/
def densityRelativeAction (p : MassiveParameters) (A : MetricAtlas X) (ρ S a : X → ℝ)
    (t : ℝ) : ℝ :=
  ∫ x, hydroDensityField p A (fun y => ρ y + t * a y) S x - hydroDensityField p A ρ S x
    ∂A.measure

/-- Stationarity of the global density–phase action under every smooth
compactly supported variation of the density alone in each chart. -/
def DensityStationary (p : MassiveParameters) (A : MetricAtlas X) (ρ S : X → ℝ) : Prop :=
  ∀ (i : ℕ) (ζ : Covector → ℝ), ContDiff ℝ ∞ ζ → HasCompactSupport ζ →
    tsupport ζ ⊆ (A.chart i).target →
      HasDerivAt (densityRelativeAction p A ρ S (extend A i ζ)) 0 0

/-- While the perturbed density is positive, the global action difference is
the coordinate one in the chart of the test. -/
theorem densityRelativeAction_eq_chart (p : MassiveParameters) (A : MetricAtlas X)
    (hA : SmoothLorentz A) (hρ : Regular A 2 ρ) (hS : Regular A 2 S) (hp : ∀ x, 0 < ρ x)
    (i : ℕ) (hζ : ContDiff ℝ 2 ζ) (hc : HasCompactSupport ζ)
    (hs : tsupport ζ ⊆ (A.chart i).target) {t : ℝ}
    (ht : ∀ x, 0 < ρ x + t * extend A i ζ x) :
    densityRelativeAction p A ρ S (extend A i ζ) t =
      CurvedDensityVariation.densityRelativeAction p (A.metric i) (repr A i ρ) (repr A i S) ζ
        (A.chart i).target t := by
  have hρt : Regular A 2 (fun y => ρ y + t * extend A i ζ y) := fun j y hy =>
    (hρ j y hy).add (contDiffAt_const.mul (regular_extend A hA i hζ hc hs j y hy))
  unfold densityRelativeAction CurvedDensityVariation.densityRelativeAction
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := (A.chart i).source) (fun x hx => ?_)]
  · rw [CurvedChartIntegration.integral_chart A i _
      (fun y hy => (hA.metric_smooth i y hy).continuousAt.continuousWithinAt)]
    apply setIntegral_congr_fun (A.chart i).open_target.measurableSet
    intro y hy
    dsimp only
    have hx := (A.chart i).map_target hy
    rw [hydroDensityField_chart p A hA hρt hS ht i hx, hydroDensityField_chart p A hA hρ hS hp i hx,
      (A.chart i).right_inv hy, smul_eq_mul]
    congr 2
    apply CurvedDensityVariation.hydroDensity_congr
    filter_upwards [repr_extend_germ A i ζ hy] with z hz
    change ρ ((A.chart i).symm z) + t * extend A i ζ ((A.chart i).symm z) = repr A i ρ z + t * ζ z
    rw [show extend A i ζ ((A.chart i).symm z) = ζ z from hz]
    rfl
  · obtain ⟨j, hj⟩ := exists_chart A x
    rw [hydroDensityField_chart p A hA hρt hS ht j hj, hydroDensityField_chart p A hA hρ hS hp j hj]
    apply sub_eq_zero.mpr
    apply CurvedDensityVariation.hydroDensity_congr
    have hz := extend_zero_germ A i hc hs hx
    have hcont := (A.chart j).continuousAt_symm ((A.chart j).map_source hj)
    have hz' : ∀ᶠ z in 𝓝 ((A.chart j).symm (A.chart j x)), extend A i ζ z = 0 := by
      simpa only [(A.chart j).left_inv hj] using
        (show ∀ᶠ z in 𝓝 x, extend A i ζ z = 0 from hz)
    filter_upwards [hcont.eventually hz'] with z hz
    simp only [CurvedAtlasDescent.repr, Function.comp_apply, hz, mul_zero, add_zero]

/-- The first variation of the global density–phase action under a
chart-supported change of the density alone. -/
theorem hasDerivAt_densityRelative (p : MassiveParameters) (A : MetricAtlas X)
    (hA : SmoothLorentz A) (hρ : Regular A 2 ρ) (hS : Regular A 2 S) (hp : ∀ x, 0 < ρ x)
    (i : ℕ) (hζ : ContDiff ℝ ∞ ζ) (hc : HasCompactSupport ζ)
    (hs : tsupport ζ ⊆ (A.chart i).target) :
    HasDerivAt (densityRelativeAction p A ρ S (extend A i ζ))
      (∫ y in (A.chart i).target, volumeFactor (A.metric i y) *
        (ζ y * hjResidual p (A.metric i) (fun z => √(repr A i ρ z)) (repr A i S) y)) 0 := by
  have h := CurvedDensityVariation.hasDerivAt_densityRelative p (A.chart i).open_target
    (hA.metric_smooth i) (hA.symmetric i) (hA.negative i) (hρ i) (hS i) (fun _ _ => hp _)
    hζ hc hs
  refine h.congr_of_eventuallyEq ?_
  filter_upwards [eventually_pos A hρ hp i hζ.continuous hc hs] with t ht
  exact densityRelativeAction_eq_chart p A hA hρ hS hp i (hζ.of_le (by simp)) hc hs ht

/-- The global density–phase action is stationary under variations of the
density alone exactly when the dressed mass relation holds in every chart. -/
theorem density_stationary_iff (p : MassiveParameters) (A : MetricAtlas X)
    (hA : SmoothLorentz A) (hρ : Regular A 2 ρ) (hS : Regular A 2 S) (hp : ∀ x, 0 < ρ x) :
    DensityStationary p A ρ S ↔ ∀ i y, y ∈ (A.chart i).target →
      pairing (A.metric i) (repr A i S) (repr A i S) y / p.m ^ 2 =
        p.c ^ 2 * (1 + defect p (A.metric i) (fun z => √(repr A i ρ z)) y) := by
  have hloc (i : ℕ) := CurvedDensityVariation.density_stationary_iff_dressed_mass p
    (A.chart i).open_target (hA.metric_smooth i) (hA.symmetric i) (hA.negative i) (hρ i) (hS i)
    (fun _ _ => hp _)
  have heq (i : ℕ) (ζ : Covector → ℝ) (hζ : ContDiff ℝ ∞ ζ) (hc : HasCompactSupport ζ)
      (hs : tsupport ζ ⊆ (A.chart i).target) :
      densityRelativeAction p A ρ S (extend A i ζ) =ᶠ[𝓝 0]
        CurvedDensityVariation.densityRelativeAction p (A.metric i) (repr A i ρ) (repr A i S) ζ
          (A.chart i).target := by
    filter_upwards [eventually_pos A hρ hp i hζ.continuous hc hs] with t ht
    exact densityRelativeAction_eq_chart p A hA hρ hS hp i (hζ.of_le (by simp)) hc hs ht
  constructor
  · intro h i y hy
    exact (hloc i).mp (fun ζ hζ hc hs =>
      (h i ζ hζ hc hs).congr_of_eventuallyEq (heq i ζ hζ hc hs).symm) y hy
  · intro h i ζ hζ hc hs
    exact ((hloc i).mpr (fun y hy => h i y hy) ζ hζ hc hs).congr_of_eventuallyEq
      (heq i ζ hζ hc hs)

/-- Statement (III) for a density and a real clock: the density–clock action
is stationary under variations of the density alone exactly when
`g(∂S,∂S)/m² = c² (1 + q)` in every chart, with `S = −mc² τ`. -/
theorem clock_density_stationary_iff (p : MassiveParameters) (A : MetricAtlas X)
    (hA : SmoothLorentz A) {τ : X → ℝ} (hρ : Regular A 2 ρ) (hτ : Regular A 2 τ)
    (hp : ∀ x, 0 < ρ x) :
    DensityStationary p A ρ (clockPhase p τ) ↔ ∀ i y, y ∈ (A.chart i).target →
      pairing (A.metric i) (repr A i (clockPhase p τ)) (repr A i (clockPhase p τ)) y / p.m ^ 2 =
        p.c ^ 2 * (1 + defect p (A.metric i) (fun z => √(repr A i ρ z)) y) :=
  density_stationary_iff p A hA hρ (CurvedGlobalMaster.regular_clockPhase p A hτ) hp

end FoliationQM.CurvedAtlasDensityVariation
