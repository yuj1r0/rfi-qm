module

public import FoliationQM.OpenActionVariation
public import FoliationQM.OpenStationaryAction
public import FoliationQM.PolarStationaryAction

/-!
# Real stationary action on an arbitrary open positive-density region

Source: v13 `thm:kahler`. The action is the actual restricted Lebesgue integral
on U. Background density and real phase need only be smooth on U, with positive
density there. Independent smooth real tests have compact topological support
inside U. No background extension regularity, boundary smoothness, or global
positive lower bound is assumed.
-/
@[expose] public section

namespace FoliationQM.OpenPolarStationaryAction

open MeasureTheory ActionDensity ActionVariation PolarTestVariations
open PolarChartAction PolarSmoothCurve SmoothActionDensity FlatIntegrationByParts
open scoped Topology ContDiff ComplexConjugate

/-- The literal real source action restricted to the supplied region. -/
noncomputable def hydroActionOn (p : MassiveParameters) (ρ S : Covector → ℝ)
    (e : Fin 4 → Covector) (U : Set Covector) : ℝ := ∫ x in U, hydroIntegrand p ρ S e x

/-- Local differentiability and positivity identify the real and complex
integrability conditions on the open region. -/
theorem integrableOn_hydroIntegrand_iff (p : MassiveParameters) {ρ S : Covector → ℝ}
    {U : Set Covector} (hU : IsOpen U)
    (hρ : ∀ x ∈ U, DifferentiableAt ℝ ρ x) (hS : ∀ x ∈ U, DifferentiableAt ℝ S x)
    (hpos : ∀ x ∈ U, 0 < ρ x) (e : Fin 4 → Covector) :
    IntegrableOn (hydroIntegrand p ρ S e) U ↔
      IntegrableOn (fun x => (fieldPairing p (actionField p ρ S)
        (actionField p ρ S) e x).re) U := by
  apply integrable_congr
  filter_upwards [ae_restrict_mem hU.measurableSet] with x hx
  exact hydroIntegrand_eq p (hρ x hx) (hS x hx) (hpos x hx) e

/-- The actual restricted real action equals the restricted complex action
on a differentiable positive chart. Integrability is tracked separately. -/
theorem hydroActionOn_eq (p : MassiveParameters) {ρ S : Covector → ℝ}
    {U : Set Covector} (hU : IsOpen U)
    (hρ : ∀ x ∈ U, DifferentiableAt ℝ ρ x) (hS : ∀ x ∈ U, DifferentiableAt ℝ S x)
    (hpos : ∀ x ∈ U, 0 < ρ x) (e : Fin 4 → Covector) :
    hydroActionOn p ρ S e U = action p (actionField p ρ S) e (volume.restrict U) := by
  apply setIntegral_congr_fun hU.measurableSet
  intro x hx
  exact hydroIntegrand_eq p (hρ x hx) (hS x hx) (hpos x hx) e

/-- The nonlinear polar image of independent interior real tests has an
actual integrated first derivative on U, with no regularity needed outside U. -/
theorem hasDerivAt_action_affine_polar (p : MassiveParameters)
    {ρ S a b : Covector → ℝ} {U : Set Covector} (hU : IsOpen U)
    (hρ : ∀ x ∈ U, ContDiffAt ℝ ∞ ρ x) (hS : ∀ x ∈ U, ContDiffAt ℝ ∞ S x)
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b) (hpos : ∀ x ∈ U, 0 < ρ x)
    (hca : HasCompactSupport a) (hcb : HasCompactSupport b)
    (hsa : tsupport a ⊆ U) (hsb : tsupport b ⊆ U) (e : Fin 4 → Covector)
    (hfinite : IntegrableOn (hydroIntegrand p ρ S e) U) :
    HasDerivAt (fun t : ℝ => action p
      (actionField p (fun x => ρ x + t * a x) (fun x => S x + t * b x)) e (volume.restrict U))
      (-2 * ∫ x in U, (conj (testTangent p ρ S a b x) *
        kgOperator p (actionField p ρ S) e x).re) 0 := by
  obtain ⟨ε, hε, hreg⟩ := OpenPolarVariations.exists_pos_contDiffAt_curve p
    hρ hS ha hb hpos hca hsa
  let s := Metric.ball (0 : ℝ) ε
  have hs : IsOpen s := Metric.isOpen_ball
  have hzero : (0 : ℝ) ∈ s := Metric.mem_ball_self hε
  have hcurve : ∀ t ∈ s, ∀ x ∈ U, ContDiffAt ℝ ∞ (curve p ρ S a b) (t, x) := by
    intro t ht x hx
    exact (hreg t (by simpa only [s, Metric.mem_ball, dist_zero_right,
      Real.norm_eq_abs] using ht) x hx).2
  have heq : ∀ t ∈ s, ∀ x ∉ tsupport a ∪ tsupport b,
      curve p ρ S a b (t, x) = curve p ρ S a b (0, x) := by
    intro t _ x hx
    rw [curve_eq_base_of_not_mem p ρ S a b hx t, curve_zero]
  have hslice : slice (curve p ρ S a b) 0 = actionField p ρ S :=
    funext (curve_zero p ρ S a b)
  have hf := (integrableOn_hydroIntegrand_iff p hU
    (fun x hx => (hρ x hx).differentiableAt (by simp))
    (fun x hx => (hS x hx).differentiableAt (by simp)) hpos e).mp hfinite
  have hf' : IntegrableOn (fun x => (fieldPairing p
      (slice (curve p ρ S a b) 0) (slice (curve p ρ S a b) 0) e x).re) U := by
    simpa only [hslice] using hf
  have hd := OpenActionVariation.hasDerivAt_action_curve_eq_kg p hU hs hzero hcurve
    (isCompact_variation_support hca hcb) (Set.union_subset hsa hsb) heq e hf'
  rw [hslice] at hd
  have hvel : (∫ x in U, (conj (velocity (curve p ρ S a b) 0 x) *
      kgOperator p (actionField p ρ S) e x).re) =
      ∫ x in U, (conj (testTangent p ρ S a b x) * kgOperator p (actionField p ρ S) e x).re := by
    apply setIntegral_congr_fun hU.measurableSet
    intro x hx
    dsimp only
    rw [SmoothActionDensity.velocity, OpenPolarVariations.fderiv_curve_time_zero p (hρ x hx) (hS x hx) ha hb (hpos x hx)]
  rwa [hvel] at hd

/-- The affine real test family has genuinely integrable source densities on
one neighborhood of parameter zero, using only local chart assumptions. -/
theorem eventually_integrableOn_hydro_affine (p : MassiveParameters)
    {ρ S a b : Covector → ℝ} {U : Set Covector} (hU : IsOpen U)
    (hρ : ∀ x ∈ U, ContDiffAt ℝ ∞ ρ x) (hS : ∀ x ∈ U, ContDiffAt ℝ ∞ S x)
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b) (hpos : ∀ x ∈ U, 0 < ρ x)
    (hca : HasCompactSupport a) (hcb : HasCompactSupport b)
    (hsa : tsupport a ⊆ U) (hsb : tsupport b ⊆ U) (e : Fin 4 → Covector)
    (hfinite : IntegrableOn (hydroIntegrand p ρ S e) U) :
    ∀ᶠ t in 𝓝 (0 : ℝ), IntegrableOn
      (hydroIntegrand p (fun x => ρ x + t * a x) (fun x => S x + t * b x) e) U := by
  obtain ⟨ε, hε, hreg⟩ := OpenPolarVariations.exists_pos_contDiffAt_curve p
    hρ hS ha hb hpos hca hsa
  let s := Metric.ball (0 : ℝ) ε
  have hzero : (0 : ℝ) ∈ s := Metric.mem_ball_self hε
  have hcurve : ∀ t ∈ s, ∀ x ∈ U, ContDiffAt ℝ ∞ (curve p ρ S a b) (t, x) := by
    intro t ht x hx
    exact (hreg t (by simpa only [s, Metric.mem_ball, dist_zero_right,
      Real.norm_eq_abs] using ht) x hx).2
  have heq : ∀ t ∈ s, ∀ x ∉ tsupport a ∪ tsupport b,
      curve p ρ S a b (t, x) = curve p ρ S a b (0, x) := by
    intro t _ x hx
    rw [curve_eq_base_of_not_mem p ρ S a b hx t, curve_zero]
  have hslice : slice (curve p ρ S a b) 0 = actionField p ρ S :=
    funext (curve_zero p ρ S a b)
  have hf := (integrableOn_hydroIntegrand_iff p hU
    (fun x hx => (hρ x hx).differentiableAt (by simp))
    (fun x hx => (hS x hx).differentiableAt (by simp)) hpos e).mp hfinite
  have hf' : IntegrableOn (fun x => (fieldPairing p
      (slice (curve p ρ S a b) 0) (slice (curve p ρ S a b) 0) e x).re) U := by
    simpa only [hslice] using hf
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hε] with t ht
  have ht' : |t| < ε := by
    simpa only [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] using ht
  apply (integrableOn_hydroIntegrand_iff p hU
    (fun x hx => ((hρ x hx).add (contDiffAt_const.mul ha.contDiffAt)).differentiableAt (by simp))
    (fun x hx => ((hS x hx).add (contDiffAt_const.mul hb.contDiffAt)).differentiableAt (by simp))
    (fun x hx => (hreg t ht' x hx).1) e).mpr
  exact OpenActionVariation.integrable_density_curve p hU hzero hcurve
    (isCompact_variation_support hca hcb) (Set.union_subset hsa hsb) heq e hf' ht

/-- The actual restricted real action has the KG-pairing derivative along
independent affine real density and phase tests supported inside U. -/
theorem hasDerivAt_hydroActionOn_affine (p : MassiveParameters)
    {ρ S a b : Covector → ℝ} {U : Set Covector} (hU : IsOpen U)
    (hρ : ∀ x ∈ U, ContDiffAt ℝ ∞ ρ x) (hS : ∀ x ∈ U, ContDiffAt ℝ ∞ S x)
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b) (hpos : ∀ x ∈ U, 0 < ρ x)
    (hca : HasCompactSupport a) (hcb : HasCompactSupport b)
    (hsa : tsupport a ⊆ U) (hsb : tsupport b ⊆ U) (e : Fin 4 → Covector)
    (hfinite : IntegrableOn (hydroIntegrand p ρ S e) U) :
    HasDerivAt (fun t : ℝ =>
      hydroActionOn p (fun x => ρ x + t * a x) (fun x => S x + t * b x) e U)
      (-2 * ∫ x in U, (conj (testTangent p ρ S a b x) *
        kgOperator p (actionField p ρ S) e x).re) 0 := by
  have hd := hasDerivAt_action_affine_polar p hU hρ hS ha hb hpos hca hcb hsa hsb e hfinite
  apply hd.congr_of_eventuallyEq
  obtain ⟨ε, hε, hp⟩ := OpenPolarVariations.exists_pos_contDiffAt_curve p
    hρ hS ha hb hpos hca hsa
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hε] with t ht
  have ht' : |t| < ε := by
    simpa only [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] using ht
  exact hydroActionOn_eq p hU
    (fun x hx => ((hρ x hx).add (contDiffAt_const.mul ha.contDiffAt)).differentiableAt (by simp))
    (fun x hx => ((hS x hx).add (contDiffAt_const.mul hb.contDiffAt)).differentiableAt (by simp))
    (fun x hx => (hp t ht' x hx).1) e

/-- Stationarity of the restricted real source action under independent
smooth compact real tests supported inside U, with genuine integrability. -/
def PolarStationaryOn (p : MassiveParameters) (ρ S : Covector → ℝ)
    (e : Fin 4 → Covector) (U : Set Covector) : Prop :=
  IntegrableOn (hydroIntegrand p ρ S e) U ∧
    ∀ a b : Covector → ℝ, ContDiff ℝ ∞ a → ContDiff ℝ ∞ b →
      HasCompactSupport a → HasCompactSupport b → tsupport a ⊆ U → tsupport b ⊆ U →
      HasDerivAt (fun t : ℝ =>
        hydroActionOn p (fun x => ρ x + t * a x) (fun x => S x + t * b x) e U) 0 0


/-- Independent compact interior real tests and complex tests give exactly
the same stationary condition on a smooth positive chart over U. -/
theorem polarStationaryOn_iff_stationaryOn (p : MassiveParameters)
    {ρ S : Covector → ℝ} {U : Set Covector} (hU : IsOpen U)
    (hρ : ∀ x ∈ U, ContDiffAt ℝ ∞ ρ x) (hS : ∀ x ∈ U, ContDiffAt ℝ ∞ S x)
    (hpos : ∀ x ∈ U, 0 < ρ x) (e : Fin 4 → Covector) :
    PolarStationaryOn p ρ S e U ↔
      OpenStationaryAction.StationaryOn p (actionField p ρ S) e U := by
  have hi := integrableOn_hydroIntegrand_iff p hU
    (fun x hx => (hρ x hx).differentiableAt (by simp))
    (fun x hx => (hS x hx).differentiableAt (by simp)) hpos e
  have hψ : ∀ x ∈ U, ContDiffAt ℝ 2 (actionField p ρ S) x :=
    fun x hx => (OpenPolarVariations.contDiffAt_actionField p
      (hρ x hx) (hS x hx) (hpos x hx)).of_le (by simp)
  constructor
  · intro hs
    refine ⟨hi.mp hs.1, ?_⟩
    intro η hη hc hηU
    obtain ⟨a, b, ha, hb, hca, hcb, hsa, hsb, heq⟩ :=
      OpenPolarVariations.exists_testTangent p hρ hS hpos hη hc hηU
    have hd := hasDerivAt_hydroActionOn_affine p hU hρ hS ha hb hpos hca hcb hsa hsb e hs.1
    have hz := (hs.2 a b ha hb hca hcb hsa hsb).unique hd
    have heqint : (∫ x in U, (conj (testTangent p ρ S a b x) *
        kgOperator p (actionField p ρ S) e x).re) =
        ∫ x in U, (conj (η x) * kgOperator p (actionField p ρ S) e x).re := by
      apply setIntegral_congr_fun hU.measurableSet
      intro x hx
      dsimp only
      rw [heq x hx]
    rw [heqint] at hz
    have hlinear := OpenStationaryAction.hasDerivAt_action_eq_kg_pairing p hU e
      hψ hη hc hηU (hi.mp hs.1)
    rwa [← hz] at hlinear
  · intro hs
    refine ⟨hi.mpr hs.1, ?_⟩
    intro a b ha hb hca hcb hsa hsb
    have ht := OpenPolarVariations.contDiff_testTangent p hρ hS ha hb hpos hsa hsb
    have htc := hasCompactSupport_testTangent p ρ S hca hcb
    have hts := (OpenPolarVariations.tsupport_testTangent_subset p ρ S a b).trans
      (Set.union_subset hsa hsb)
    have hlinear := OpenStationaryAction.hasDerivAt_action_eq_kg_pairing p hU e
      hψ ht htc hts hs.1
    have hz := (hs.2 _ ht htc hts).unique hlinear
    have hd := hasDerivAt_hydroActionOn_affine p hU hρ hS ha hb hpos hca hcb hsa hsb e
      (hi.mpr hs.1)
    rwa [← hz] at hd

/-- The actual real stationary action on an arbitrary open positive-density
region is equivalent to the source normalized KG equation throughout it. -/
theorem polarStationaryOn_iff_kleinGordon (p : MassiveParameters)
    {ρ S : Covector → ℝ} {U : Set Covector} (hU : IsOpen U)
    (hρ : ∀ x ∈ U, ContDiffAt ℝ ∞ ρ x) (hS : ∀ x ∈ U, ContDiffAt ℝ ∞ S x)
    (hpos : ∀ x ∈ U, 0 < ρ x)
    (hfinite : IntegrableOn (hydroIntegrand p ρ S Madelung.coordinateVector) U) :
    PolarStationaryOn p ρ S Madelung.coordinateVector U ↔ ∀ x ∈ U,
      PolarSecondDifferential.box (actionField p ρ S) Madelung.coordinateVector x +
        (((p.m ^ 2 * p.c ^ 2 / p.hbar ^ 2 : ℝ) : ℂ) * actionField p ρ S x) = 0 := by
  rw [polarStationaryOn_iff_stationaryOn p hU hρ hS hpos Madelung.coordinateVector]
  apply OpenStationaryAction.stationaryOn_iff_kleinGordon p hU
    (fun x hx => (OpenPolarVariations.contDiffAt_actionField p
      (hρ x hx) (hS x hx) (hpos x hx)).of_le (by simp))
  exact (integrableOn_hydroIntegrand_iff p hU
    (fun x hx => (hρ x hx).differentiableAt (by simp))
    (fun x hx => (hS x hx).differentiableAt (by simp)) hpos Madelung.coordinateVector).mp hfinite

/-- On the open regular chart the real variational equations are exactly
Hamilton-Jacobi with the canonical quantum correction and current continuity.
Both real PDEs are conclusions, not additional hypotheses. -/
theorem polarStationaryOn_iff_madelung (p : MassiveParameters)
    {ρ S : Covector → ℝ} {U : Set Covector} (hU : IsOpen U)
    (hρ : ∀ x ∈ U, ContDiffAt ℝ ∞ ρ x) (hS : ∀ x ∈ U, ContDiffAt ℝ ∞ S x)
    (hpos : ∀ x ∈ U, 0 < ρ x)
    (hfinite : IntegrableOn (hydroIntegrand p ρ S Madelung.coordinateVector) U) :
    PolarStationaryOn p ρ S Madelung.coordinateVector U ↔ ∀ x ∈ U,
      minkowski
        (fun i => PolarSecondDifferential.directionalDerivative S (Madelung.coordinateVector i) x)
        (fun i => PolarSecondDifferential.directionalDerivative S (Madelung.coordinateVector i) x) =
        p.m ^ 2 * p.c ^ 2 + p.hbar ^ 2 *
          PolarSecondDifferential.box (fun y => Real.sqrt (ρ y))
            Madelung.coordinateVector x / Real.sqrt (ρ x) ∧
      PolarRegularity.densityCurrentDivergence ρ S Madelung.coordinateVector x = 0 := by
  rw [polarStationaryOn_iff_kleinGordon p hU hρ hS hpos hfinite]
  exact forall_congr' (fun x => forall_congr' (fun hx =>
    PolarRegularity.kg_eq_zero_iff_madelung_density_coordinates p
      ((hρ x hx).of_le (by simp)) ((hS x hx).of_le (by simp)) (hpos x hx)))

/-- Taking U to be the whole spacetime recovers the previous conventional
real stationarity definition exactly. -/
theorem polarStationaryOn_univ_iff (p : MassiveParameters) (ρ S : Covector → ℝ)
    (e : Fin 4 → Covector) :
    PolarStationaryOn p ρ S e Set.univ ↔ PolarStationaryAction.PolarStationary p ρ S e := by
  simp [PolarStationaryOn, PolarStationaryAction.PolarStationary, IntegrableOn,
    hydroActionOn, hydroAction]

/-- Unit density and the explicit rest phase give a nonzero stationary example
on every open region, including unbounded regions and irregular boundaries. -/
theorem rest_polarStationaryOn (p : MassiveParameters) {U : Set Covector} (hU : IsOpen U) :
    PolarStationaryOn p (fun _ => 1) (RestPlaneWave.restAction p)
      Madelung.coordinateVector U := by
  apply (polarStationaryOn_iff_stationaryOn p hU (fun _ _ => contDiffAt_const)
    (fun _ _ => (RestPlaneWave.contDiff_restAction p ∞).contDiffAt)
    (fun _ _ => by norm_num) Madelung.coordinateVector).mpr
  exact OpenStationaryAction.restWave_stationaryOn p hU

end FoliationQM.OpenPolarStationaryAction
