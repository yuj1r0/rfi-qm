module

public import FoliationQM.CompactActionVariation
public import FoliationQM.PolarSmoothCurve
public import FoliationQM.PolarChartAction
public import FoliationQM.PolarRegularity

/-!
# Stationarity under independent affine density and phase variations

Source: v13 `thm:kahler`. The real action is tested along the conventional
curves `(ρ+t*a, S+t*b)`, with independent smooth compact real tests. A compact
positive parameter interval, joint smoothness, mixed derivative symmetry and
proved integrable domination justify the actual integrated derivative. The
domain here is whole flat R4, with a supplied smooth positive-density real
phase chart and integrable full real action density.
-/
@[expose] public section

namespace FoliationQM.PolarStationaryAction

open MeasureTheory ActionDensity ActionVariation PolarTestVariations
open PolarChartAction PolarSmoothCurve CompactActionVariation SmoothActionDensity
open StationaryAction FlatIntegrationByParts
open scoped Topology ContDiff ComplexConjugate

/-- The actual complex action along the nonlinear polar image of independent
affine real variations has the derivative determined by its polar tangent. -/
theorem hasDerivAt_action_affine_polar (p : MassiveParameters)
    {ρ S a b : Covector → ℝ}
    (hρ : ContDiff ℝ ∞ ρ) (hS : ContDiff ℝ ∞ S)
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b) (hpos : ∀ x, 0 < ρ x)
    (hca : HasCompactSupport a) (hcb : HasCompactSupport b) (e : Fin 4 → Covector)
    (hfinite : Integrable (hydroIntegrand p ρ S e)) :
    HasDerivAt (fun t : ℝ => action p
      (actionField p (fun x => ρ x + t * a x) (fun x => S x + t * b x)) e volume)
      (-2 * ∫ x, (conj (testTangent p ρ S a b x) *
        kgOperator p (actionField p ρ S) e x).re) 0 := by
  obtain ⟨ε, hε, hreg⟩ := exists_pos_contDiffAt_curve p hρ hS ha hb hpos hca
  let s := Metric.ball (0 : ℝ) ε
  have hs : IsOpen s := Metric.isOpen_ball
  have hzero : (0 : ℝ) ∈ s := Metric.mem_ball_self hε
  have hcurve : ∀ t ∈ s, ∀ x, ContDiffAt ℝ ∞ (curve p ρ S a b) (t, x) := by
    intro t ht x
    exact (hreg t (by simpa only [s, Metric.mem_ball, dist_zero_right,
      Real.norm_eq_abs] using ht) x).2
  have heq : ∀ t ∈ s, ∀ x ∉ tsupport a ∪ tsupport b,
      curve p ρ S a b (t, x) = curve p ρ S a b (0, x) := by
    intro t _ x hx
    rw [curve_eq_base_of_not_mem p ρ S a b hx t, curve_zero]
  have hslice : slice (curve p ρ S a b) 0 = actionField p ρ S :=
    funext (curve_zero p ρ S a b)
  have hvel : velocity (curve p ρ S a b) 0 = testTangent p ρ S a b :=
    funext (fun x => fderiv_curve_time_zero p hρ hS ha hb x (hpos x))
  have hf := (integrable_hydroIntegrand_iff p (hρ.differentiable (by simp))
    (hS.differentiable (by simp)) hpos e).mp hfinite
  have hf' : Integrable (fun x => (fieldPairing p
      (slice (curve p ρ S a b) 0) (slice (curve p ρ S a b) 0) e x).re) := by
    simpa only [hslice] using hf
  have hd := hasDerivAt_action_curve_eq_kg p hs hzero hcurve
    (isCompact_variation_support hca hcb) heq e hf'
  rw [hslice, hvel] at hd
  exact hd

/-- The conventional affine real variations have genuinely integrable
source densities on a neighborhood of parameter zero. -/
theorem eventually_integrable_hydro_affine (p : MassiveParameters)
    {ρ S a b : Covector → ℝ}
    (hρ : ContDiff ℝ ∞ ρ) (hS : ContDiff ℝ ∞ S)
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b) (hpos : ∀ x, 0 < ρ x)
    (hca : HasCompactSupport a) (hcb : HasCompactSupport b) (e : Fin 4 → Covector)
    (hfinite : Integrable (hydroIntegrand p ρ S e)) :
    ∀ᶠ t in 𝓝 (0 : ℝ), Integrable
      (hydroIntegrand p (fun x => ρ x + t * a x) (fun x => S x + t * b x) e) := by
  obtain ⟨ε, hε, hreg⟩ := exists_pos_contDiffAt_curve p hρ hS ha hb hpos hca
  let s := Metric.ball (0 : ℝ) ε
  have hzero : (0 : ℝ) ∈ s := Metric.mem_ball_self hε
  have hcurve : ∀ t ∈ s, ∀ x, ContDiffAt ℝ ∞ (curve p ρ S a b) (t, x) := by
    intro t ht x
    exact (hreg t (by simpa only [s, Metric.mem_ball, dist_zero_right,
      Real.norm_eq_abs] using ht) x).2
  have heq : ∀ t ∈ s, ∀ x ∉ tsupport a ∪ tsupport b,
      curve p ρ S a b (t, x) = curve p ρ S a b (0, x) := by
    intro t _ x hx
    rw [curve_eq_base_of_not_mem p ρ S a b hx t, curve_zero]
  have hslice : slice (curve p ρ S a b) 0 = actionField p ρ S :=
    funext (curve_zero p ρ S a b)
  have hf := (integrable_hydroIntegrand_iff p (hρ.differentiable (by simp))
    (hS.differentiable (by simp)) hpos e).mp hfinite
  have hf' : Integrable (fun x => (fieldPairing p
      (slice (curve p ρ S a b) 0) (slice (curve p ρ S a b) 0) e x).re) := by
    simpa only [hslice] using hf
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hε] with t ht
  have ht' : |t| < ε := by
    simpa only [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] using ht
  have hrt : Differentiable ℝ (fun x => ρ x + t * a x) :=
    (hρ.add (contDiff_const.mul ha)).differentiable (by simp)
  have hSt : Differentiable ℝ (fun x => S x + t * b x) :=
    (hS.add (contDiff_const.mul hb)).differentiable (by simp)
  apply (integrable_hydroIntegrand_iff p hrt hSt (fun x => (hreg t ht' x).1) e).mpr
  exact integrable_density_curve p hzero hcurve
    (isCompact_variation_support hca hcb) heq e hf' ht

/-- The genuine source real action differentiated along independent affine
density and phase tests. All limit/integral and derivative commutations have
been justified by the compact smooth curve theorems. -/
theorem hasDerivAt_hydroAction_affine (p : MassiveParameters)
    {ρ S a b : Covector → ℝ}
    (hρ : ContDiff ℝ ∞ ρ) (hS : ContDiff ℝ ∞ S)
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b) (hpos : ∀ x, 0 < ρ x)
    (hca : HasCompactSupport a) (hcb : HasCompactSupport b) (e : Fin 4 → Covector)
    (hfinite : Integrable (hydroIntegrand p ρ S e)) :
    HasDerivAt (fun t : ℝ =>
      hydroAction p (fun x => ρ x + t * a x) (fun x => S x + t * b x) e)
      (-2 * ∫ x, (conj (testTangent p ρ S a b x) *
        kgOperator p (actionField p ρ S) e x).re) 0 := by
  have hd := hasDerivAt_action_affine_polar p hρ hS ha hb hpos hca hcb e hfinite
  apply hd.congr_of_eventuallyEq
  obtain ⟨ε, hε, hp⟩ := CompactPerturbation.exists_pos_affine
    hρ.continuous hpos ha.continuous hca
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hε] with t ht
  have ht' : |t| < ε := by
    simpa only [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] using ht
  exact hydroAction_eq p
    ((hρ.add (contDiff_const.mul ha)).differentiable (by simp))
    ((hS.add (contDiff_const.mul hb)).differentiable (by simp)) (hp t ht') e

/-- Conventional real-variable stationarity: finite source action density
and zero actual derivative for every pair of independent smooth compact
affine density and action-phase variations. -/
def PolarStationary (p : MassiveParameters) (ρ S : Covector → ℝ)
    (e : Fin 4 → Covector) : Prop :=
  Integrable (hydroIntegrand p ρ S e) ∧
    ∀ a b : Covector → ℝ, ContDiff ℝ ∞ a → ContDiff ℝ ∞ b →
      HasCompactSupport a → HasCompactSupport b →
      HasDerivAt (fun t : ℝ =>
        hydroAction p (fun x => ρ x + t * a x) (fun x => S x + t * b x) e) 0 0

/-- The conventional real density/phase and complex affine test classes
give equivalent stationary actions on a smooth positive finite-action chart. -/
theorem polarStationary_iff_stationary (p : MassiveParameters) {ρ S : Covector → ℝ}
    (hρ : ContDiff ℝ ∞ ρ) (hS : ContDiff ℝ ∞ S) (hpos : ∀ x, 0 < ρ x)
    (e : Fin 4 → Covector) :
    PolarStationary p ρ S e ↔ Stationary p (actionField p ρ S) e := by
  have hi := integrable_hydroIntegrand_iff p (hρ.differentiable (by simp))
    (hS.differentiable (by simp)) hpos e
  have hψ := contDiff_actionField p hρ hS hpos
  constructor
  · intro hs
    have hf := hi.mp hs.1
    apply (stationary_iff_polar_tangent_tests p hρ hS hpos e hf).mpr
    intro a b ha hb hca hcb
    have hd := hasDerivAt_hydroAction_affine p hρ hS ha hb hpos hca hcb e hs.1
    have hz := (hs.2 a b ha hb hca hcb).unique hd
    have hlinear := hasDerivAt_action_eq_kg_pairing p e (hψ.of_le (by norm_num))
      (contDiff_testTangent p hρ hS ha hb hpos)
      (hasCompactSupport_testTangent p ρ S hca hcb) hf
    rwa [← hz] at hlinear
  · intro hs
    refine ⟨hi.mpr hs.1, ?_⟩
    intro a b ha hb hca hcb
    have hlinear := hasDerivAt_action_eq_kg_pairing p e (hψ.of_le (by norm_num))
      (contDiff_testTangent p hρ hS ha hb hpos)
      (hasCompactSupport_testTangent p ρ S hca hcb) hs.1
    have hz := (hs.2 _ (contDiff_testTangent p hρ hS ha hb hpos)
      (hasCompactSupport_testTangent p ρ S hca hcb)).unique hlinear
    have hd := hasDerivAt_hydroAction_affine p hρ hS ha hb hpos hca hcb e (hi.mpr hs.1)
    rwa [← hz] at hd

/-- Conventional affine real stationarity agrees with the previously
constructed inverse-chart variation class; neither is silently identified. -/
theorem polarStationary_iff_chartStationary (p : MassiveParameters) {ρ S : Covector → ℝ}
    (hρ : ContDiff ℝ ∞ ρ) (hS : ContDiff ℝ ∞ S) (hpos : ∀ x, 0 < ρ x)
    (e : Fin 4 → Covector) :
    PolarStationary p ρ S e ↔ ChartStationary p ρ S e := by
  rw [polarStationary_iff_stationary p hρ hS hpos e,
    chartStationary_iff_stationary p hρ hS hpos e]

/-- The source's ordinary real-variable stationary action is equivalent to
the normalized actual KG equation under the stated whole-flat-space scope. -/
theorem polarStationary_iff_kleinGordon (p : MassiveParameters) {ρ S : Covector → ℝ}
    (hρ : ContDiff ℝ ∞ ρ) (hS : ContDiff ℝ ∞ S) (hpos : ∀ x, 0 < ρ x)
    (hfinite : Integrable (hydroIntegrand p ρ S Madelung.coordinateVector)) :
    PolarStationary p ρ S Madelung.coordinateVector ↔ ∀ x,
      PolarSecondDifferential.box (actionField p ρ S) Madelung.coordinateVector x +
        (((p.m ^ 2 * p.c ^ 2 / p.hbar ^ 2 : ℝ) : ℂ) * actionField p ρ S x) = 0 := by
  rw [polarStationary_iff_chartStationary p hρ hS hpos Madelung.coordinateVector]
  exact chartStationary_iff_kleinGordon p hρ hS hpos hfinite

/-- The independent real-variable stationary action has exactly the coupled
Hamilton-Jacobi and density-current-continuity equations on the regular chart.
These real equations are conclusions here, not imposed field hypotheses. -/
theorem polarStationary_iff_madelung (p : MassiveParameters) {ρ S : Covector → ℝ}
    (hρ : ContDiff ℝ ∞ ρ) (hS : ContDiff ℝ ∞ S) (hpos : ∀ x, 0 < ρ x)
    (hfinite : Integrable (hydroIntegrand p ρ S Madelung.coordinateVector)) :
    PolarStationary p ρ S Madelung.coordinateVector ↔ ∀ x,
      minkowski
        (fun i => PolarSecondDifferential.directionalDerivative S (Madelung.coordinateVector i) x)
        (fun i => PolarSecondDifferential.directionalDerivative S (Madelung.coordinateVector i) x) =
        p.m ^ 2 * p.c ^ 2 + p.hbar ^ 2 *
          PolarSecondDifferential.box (fun y => Real.sqrt (ρ y))
            Madelung.coordinateVector x / Real.sqrt (ρ x) ∧
      PolarRegularity.densityCurrentDivergence ρ S Madelung.coordinateVector x = 0 := by
  rw [polarStationary_iff_kleinGordon p hρ hS hpos hfinite]
  exact forall_congr' (fun x => PolarRegularity.kg_eq_zero_iff_madelung_density_coordinates p
    (hρ.contDiffAt.of_le (by norm_num)) (hS.contDiffAt.of_le (by norm_num)) (hpos x))

/-- Unit density and the explicit nonzero rest phase are stationary under
the conventional independent compact real density and phase variations. -/
theorem rest_polarStationary (p : MassiveParameters) :
    PolarStationary p (fun _ => 1) (RestPlaneWave.restAction p)
      Madelung.coordinateVector := by
  apply (polarStationary_iff_chartStationary p contDiff_const
    (RestPlaneWave.contDiff_restAction p ∞) (fun _ => by norm_num)
    Madelung.coordinateVector).mpr
  exact rest_chartStationary p

end FoliationQM.PolarStationaryAction
