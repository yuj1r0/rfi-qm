module

public import FoliationQM.RelativeActionVariation
public import FoliationQM.RelativeStationaryAction
public import FoliationQM.OpenPolarStationaryAction

/-!
# Relative real stationary action without finite background action

Source: v13 `thm:kahler`. The relative action integrates the pointwise change
of the literal real source density under compact interior variations. It is
not defined by subtracting two possibly nonintegrable action integrals.
Local smoothness and positive density on the open chart suffice. The actual
integrability of the density change and the first variation are proved.
-/
@[expose] public section

namespace FoliationQM.RelativePolarStationaryAction

open MeasureTheory ActionDensity ActionVariation PolarTestVariations
open PolarChartAction PolarSmoothCurve SmoothActionDensity FlatIntegrationByParts
open RelativeAction RelativeActionVariation RelativeStationaryAction
open scoped Topology ContDiff ComplexConjugate

/-- The pointwise change in the real source density; background arguments first. -/
noncomputable def relativeHydroDensity (p : MassiveParameters)
    (ρ S ρ' S' : Covector → ℝ) (e : Fin 4 → Covector) (x : Covector) : ℝ :=
  hydroIntegrand p ρ' S' e x - hydroIntegrand p ρ S e x

/-- Relative real action is the integral of the density change itself. -/
noncomputable def relativeHydroAction (p : MassiveParameters)
    (ρ S ρ' S' : Covector → ℝ) (e : Fin 4 → Covector) (U : Set Covector) : ℝ :=
  ∫ x in U, relativeHydroDensity p ρ S ρ' S' e x

/-- Positive differentiable polar charts identify the real and complex
pointwise density changes before any integration is performed. -/
theorem relativeHydroDensity_eq (p : MassiveParameters)
    {ρ S ρ' S' : Covector → ℝ} {x : Covector}
    (hρ : DifferentiableAt ℝ ρ x) (hS : DifferentiableAt ℝ S x)
    (hρ' : DifferentiableAt ℝ ρ' x) (hS' : DifferentiableAt ℝ S' x)
    (hpos : 0 < ρ x) (hpos' : 0 < ρ' x) (e : Fin 4 → Covector) :
    relativeHydroDensity p ρ S ρ' S' e x =
      relativeDensity p (actionField p ρ S) (actionField p ρ' S') e x := by
  simp only [relativeHydroDensity, relativeDensity,
    hydroIntegrand_eq p hρ hS hpos e, hydroIntegrand_eq p hρ' hS' hpos' e]

/-- Equality of the actual relative real and complex integrals follows from
local pointwise equality. No finiteness of either background action is needed. -/
theorem relativeHydroAction_eq (p : MassiveParameters)
    {ρ S ρ' S' : Covector → ℝ} {U : Set Covector} (hU : IsOpen U)
    (hρ : ∀ x ∈ U, DifferentiableAt ℝ ρ x) (hS : ∀ x ∈ U, DifferentiableAt ℝ S x)
    (hρ' : ∀ x ∈ U, DifferentiableAt ℝ ρ' x) (hS' : ∀ x ∈ U, DifferentiableAt ℝ S' x)
    (hpos : ∀ x ∈ U, 0 < ρ x) (hpos' : ∀ x ∈ U, 0 < ρ' x)
    (e : Fin 4 → Covector) :
    relativeHydroAction p ρ S ρ' S' e U =
      relativeAction p (actionField p ρ S) (actionField p ρ' S') e U := by
  apply setIntegral_congr_fun hU.measurableSet
  intro x hx
  exact relativeHydroDensity_eq p (hρ x hx) (hS x hx) (hρ' x hx) (hS' x hx)
    (hpos x hx) (hpos' x hx) e

/-- When both full densities really are integrable, relative real action
agrees with the difference of their ordinary restricted actions. -/
theorem relativeHydroAction_eq_sub (p : MassiveParameters)
    (ρ S ρ' S' : Covector → ℝ) (e : Fin 4 → Covector) (U : Set Covector)
    (hbase : IntegrableOn (hydroIntegrand p ρ S e) U)
    (hnew : IntegrableOn (hydroIntegrand p ρ' S' e) U) :
    relativeHydroAction p ρ S ρ' S' e U =
      OpenPolarStationaryAction.hydroActionOn p ρ' S' e U -
        OpenPolarStationaryAction.hydroActionOn p ρ S e U :=
  integral_sub hnew hbase

/-- Actual relative first variation of the nonlinear polar image of independent
interior real tests, without an integrable background-action hypothesis. -/
theorem hasDerivAt_relativeAction_affine_polar (p : MassiveParameters)
    {ρ S a b : Covector → ℝ} {U : Set Covector} (hU : IsOpen U)
    (hρ : ∀ x ∈ U, ContDiffAt ℝ ∞ ρ x) (hS : ∀ x ∈ U, ContDiffAt ℝ ∞ S x)
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b) (hpos : ∀ x ∈ U, 0 < ρ x)
    (hca : HasCompactSupport a) (hcb : HasCompactSupport b)
    (hsa : tsupport a ⊆ U) (hsb : tsupport b ⊆ U) (e : Fin 4 → Covector) :
    HasDerivAt (fun t : ℝ => relativeAction p (actionField p ρ S)
      (actionField p (fun x => ρ x + t * a x) (fun x => S x + t * b x)) e U)
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
  have hd := hasDerivAt_relativeAction_curve_eq_kg p hU hs hzero hcurve
    (isCompact_variation_support hca hcb) (Set.union_subset hsa hsb) heq e
  rw [hslice] at hd
  have hvel : (∫ x in U, (conj (velocity (curve p ρ S a b) 0 x) *
      kgOperator p (actionField p ρ S) e x).re) =
      ∫ x in U, (conj (testTangent p ρ S a b x) * kgOperator p (actionField p ρ S) e x).re := by
    apply setIntegral_congr_fun hU.measurableSet
    intro x hx
    dsimp only
    rw [SmoothActionDensity.velocity, OpenPolarVariations.fderiv_curve_time_zero p
      (hρ x hx) (hS x hx) ha hb (hpos x hx)]
  rwa [hvel] at hd

/-- The literal real density change is genuinely integrable near parameter
zero even when neither individual background nor perturbed density is. -/
theorem eventually_integrableOn_relativeHydroDensity_affine (p : MassiveParameters)
    {ρ S a b : Covector → ℝ} {U : Set Covector} (hU : IsOpen U)
    (hρ : ∀ x ∈ U, ContDiffAt ℝ ∞ ρ x) (hS : ∀ x ∈ U, ContDiffAt ℝ ∞ S x)
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b) (hpos : ∀ x ∈ U, 0 < ρ x)
    (hca : HasCompactSupport a) (hcb : HasCompactSupport b)
    (hsa : tsupport a ⊆ U) (hsb : tsupport b ⊆ U) (e : Fin 4 → Covector) :
    ∀ᶠ t in 𝓝 (0 : ℝ), IntegrableOn
      (relativeHydroDensity p ρ S (fun x => ρ x + t * a x) (fun x => S x + t * b x) e) U := by
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
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hε] with t ht
  have ht' : |t| < ε := by
    simpa only [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] using ht
  have hi := integrableOn_relativeDensity_curve p hU hzero hcurve
    (isCompact_variation_support hca hcb) (Set.union_subset hsa hsb) heq e ht
  rw [hslice] at hi
  apply hi.congr
  filter_upwards [ae_restrict_mem hU.measurableSet] with x hx
  exact (relativeHydroDensity_eq p
    ((hρ x hx).differentiableAt (by simp)) ((hS x hx).differentiableAt (by simp))
    (((hρ x hx).add (contDiffAt_const.mul ha.contDiffAt)).differentiableAt (by simp))
    (((hS x hx).add (contDiffAt_const.mul hb.contDiffAt)).differentiableAt (by simp))
    (hpos x hx) (hreg t ht' x hx).1 e).symm

/-- Independent real variations have the actual relative first variation
of the source action, without assuming finite total background action. -/
theorem hasDerivAt_relativeHydroAction_affine (p : MassiveParameters)
    {ρ S a b : Covector → ℝ} {U : Set Covector} (hU : IsOpen U)
    (hρ : ∀ x ∈ U, ContDiffAt ℝ ∞ ρ x) (hS : ∀ x ∈ U, ContDiffAt ℝ ∞ S x)
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b) (hpos : ∀ x ∈ U, 0 < ρ x)
    (hca : HasCompactSupport a) (hcb : HasCompactSupport b)
    (hsa : tsupport a ⊆ U) (hsb : tsupport b ⊆ U) (e : Fin 4 → Covector) :
    HasDerivAt (fun t : ℝ => relativeHydroAction p ρ S
      (fun x => ρ x + t * a x) (fun x => S x + t * b x) e U)
      (-2 * ∫ x in U, (conj (testTangent p ρ S a b x) *
        kgOperator p (actionField p ρ S) e x).re) 0 := by
  have hd := hasDerivAt_relativeAction_affine_polar p hU hρ hS ha hb hpos hca hcb hsa hsb e
  apply hd.congr_of_eventuallyEq
  obtain ⟨ε, hε, hp⟩ := OpenPolarVariations.exists_pos_contDiffAt_curve p
    hρ hS ha hb hpos hca hsa
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hε] with t ht
  have ht' : |t| < ε := by
    simpa only [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] using ht
  exact relativeHydroAction_eq p hU
    (fun x hx => (hρ x hx).differentiableAt (by simp))
    (fun x hx => (hS x hx).differentiableAt (by simp))
    (fun x hx => ((hρ x hx).add (contDiffAt_const.mul ha.contDiffAt)).differentiableAt (by simp))
    (fun x hx => ((hS x hx).add (contDiffAt_const.mul hb.contDiffAt)).differentiableAt (by simp))
    hpos (fun x hx => (hp t ht' x hx).1) e

/-- Relative real stationarity tests the actual compact density changes.
Finiteness of the unperturbed full density is deliberately absent. -/
def RelativePolarStationaryOn (p : MassiveParameters) (ρ S : Covector → ℝ)
    (e : Fin 4 → Covector) (U : Set Covector) : Prop :=
  ∀ a b : Covector → ℝ, ContDiff ℝ ∞ a → ContDiff ℝ ∞ b →
    HasCompactSupport a → HasCompactSupport b → tsupport a ⊆ U → tsupport b ⊆ U →
    HasDerivAt (fun t : ℝ => relativeHydroAction p ρ S
      (fun x => ρ x + t * a x) (fun x => S x + t * b x) e U) 0 0

/-- Relative stationarity in independent real polar variables is equivalent
to relative complex stationarity with the full interior test correspondence. -/
theorem relativePolarStationaryOn_iff_relativeStationaryOn (p : MassiveParameters)
    {ρ S : Covector → ℝ} {U : Set Covector} (hU : IsOpen U)
    (hρ : ∀ x ∈ U, ContDiffAt ℝ ∞ ρ x) (hS : ∀ x ∈ U, ContDiffAt ℝ ∞ S x)
    (hpos : ∀ x ∈ U, 0 < ρ x) (e : Fin 4 → Covector) :
    RelativePolarStationaryOn p ρ S e U ↔
      RelativeStationaryOn p (actionField p ρ S) e U := by
  have hψ : ∀ x ∈ U, ContDiffAt ℝ 2 (actionField p ρ S) x :=
    fun x hx => (OpenPolarVariations.contDiffAt_actionField p
      (hρ x hx) (hS x hx) (hpos x hx)).of_le (by simp)
  constructor
  · intro hs η hη hc hηU
    obtain ⟨a, b, ha, hb, hca, hcb, hsa, hsb, heq⟩ :=
      OpenPolarVariations.exists_testTangent p hρ hS hpos hη hc hηU
    have hd := hasDerivAt_relativeHydroAction_affine p hU hρ hS ha hb hpos hca hcb hsa hsb e
    have hz := (hs a b ha hb hca hcb hsa hsb).unique hd
    have heqint : (∫ x in U, (conj (testTangent p ρ S a b x) *
        kgOperator p (actionField p ρ S) e x).re) =
        ∫ x in U, (conj (η x) * kgOperator p (actionField p ρ S) e x).re := by
      apply setIntegral_congr_fun hU.measurableSet
      intro x hx
      dsimp only
      rw [heq x hx]
    rw [heqint] at hz
    have hlinear := hasDerivAt_relativeAction_affine_eq_kg_pairing p hU e hψ hη hc hηU
    rwa [← hz] at hlinear
  · intro hs a b ha hb hca hcb hsa hsb
    have ht := OpenPolarVariations.contDiff_testTangent p hρ hS ha hb hpos hsa hsb
    have htc := hasCompactSupport_testTangent p ρ S hca hcb
    have hts := (OpenPolarVariations.tsupport_testTangent_subset p ρ S a b).trans
      (Set.union_subset hsa hsb)
    have hlinear := hasDerivAt_relativeAction_affine_eq_kg_pairing p hU e hψ ht htc hts
    have hz := (hs _ ht htc hts).unique hlinear
    have hd := hasDerivAt_relativeHydroAction_affine p hU hρ hS ha hb hpos hca hcb hsa hsb e
    rwa [← hz] at hd

/-- Relative real stationarity is equivalent to the actual dimensional KG
operator vanishing on U, without full-density integrability. -/
theorem relativePolarStationaryOn_iff_kgOperator (p : MassiveParameters)
    {ρ S : Covector → ℝ} {U : Set Covector} (hU : IsOpen U)
    (hρ : ∀ x ∈ U, ContDiffAt ℝ ∞ ρ x) (hS : ∀ x ∈ U, ContDiffAt ℝ ∞ S x)
    (hpos : ∀ x ∈ U, 0 < ρ x) (e : Fin 4 → Covector) :
    RelativePolarStationaryOn p ρ S e U ↔ ∀ x ∈ U, kgOperator p (actionField p ρ S) e x = 0 := by
  rw [relativePolarStationaryOn_iff_relativeStationaryOn p hU hρ hS hpos e]
  exact relativeStationaryOn_iff_kgOperator p hU e (fun x hx =>
    (OpenPolarVariations.contDiffAt_actionField p (hρ x hx) (hS x hx) (hpos x hx)).of_le (by simp))

/-- The relative source action yields exactly the normalized KG equation on
the regular chart, with no global action-integrability assumption. -/
theorem relativePolarStationaryOn_iff_kleinGordon (p : MassiveParameters)
    {ρ S : Covector → ℝ} {U : Set Covector} (hU : IsOpen U)
    (hρ : ∀ x ∈ U, ContDiffAt ℝ ∞ ρ x) (hS : ∀ x ∈ U, ContDiffAt ℝ ∞ S x)
    (hpos : ∀ x ∈ U, 0 < ρ x) :
    RelativePolarStationaryOn p ρ S Madelung.coordinateVector U ↔ ∀ x ∈ U,
      PolarSecondDifferential.box (actionField p ρ S) Madelung.coordinateVector x +
        (((p.m ^ 2 * p.c ^ 2 / p.hbar ^ 2 : ℝ) : ℂ) * actionField p ρ S x) = 0 := by
  rw [relativePolarStationaryOn_iff_kgOperator p hU hρ hS hpos Madelung.coordinateVector]
  exact forall_congr' (fun x => forall_congr' (fun _ =>
    StationaryAction.kgOperator_eq_zero_iff p (actionField p ρ S) Madelung.coordinateVector x))

/-- The actual Hamilton-Jacobi and density-current equations characterize
relative real stationarity; they are conclusions and require no total action. -/
theorem relativePolarStationaryOn_iff_madelung (p : MassiveParameters)
    {ρ S : Covector → ℝ} {U : Set Covector} (hU : IsOpen U)
    (hρ : ∀ x ∈ U, ContDiffAt ℝ ∞ ρ x) (hS : ∀ x ∈ U, ContDiffAt ℝ ∞ S x)
    (hpos : ∀ x ∈ U, 0 < ρ x) :
    RelativePolarStationaryOn p ρ S Madelung.coordinateVector U ↔ ∀ x ∈ U,
      minkowski
        (fun i => PolarSecondDifferential.directionalDerivative S (Madelung.coordinateVector i) x)
        (fun i => PolarSecondDifferential.directionalDerivative S (Madelung.coordinateVector i) x) =
        p.m ^ 2 * p.c ^ 2 + p.hbar ^ 2 *
          PolarSecondDifferential.box (fun y => Real.sqrt (ρ y))
            Madelung.coordinateVector x / Real.sqrt (ρ x) ∧
      PolarRegularity.densityCurrentDivergence ρ S Madelung.coordinateVector x = 0 := by
  rw [relativePolarStationaryOn_iff_kleinGordon p hU hρ hS hpos]
  exact forall_congr' (fun x => forall_congr' (fun hx =>
    PolarRegularity.kg_eq_zero_iff_madelung_density_coordinates p
      ((hρ x hx).of_le (by simp)) ((hS x hx).of_le (by simp)) (hpos x hx)))

/-- Under genuine full-density integrability, relative real stationarity and
the previous finite-action definition agree. -/
theorem relativePolarStationaryOn_iff_polarStationaryOn (p : MassiveParameters)
    {ρ S : Covector → ℝ} {U : Set Covector} (hU : IsOpen U)
    (hρ : ∀ x ∈ U, ContDiffAt ℝ ∞ ρ x) (hS : ∀ x ∈ U, ContDiffAt ℝ ∞ S x)
    (hpos : ∀ x ∈ U, 0 < ρ x) (e : Fin 4 → Covector)
    (hfinite : IntegrableOn (hydroIntegrand p ρ S e) U) :
    RelativePolarStationaryOn p ρ S e U ↔ OpenPolarStationaryAction.PolarStationaryOn p ρ S e U := by
  rw [relativePolarStationaryOn_iff_kgOperator p hU hρ hS hpos e,
    OpenPolarStationaryAction.polarStationaryOn_iff_stationaryOn p hU hρ hS hpos e,
    OpenStationaryAction.stationaryOn_iff_kgOperator p hU e
      (fun x hx => (OpenPolarVariations.contDiffAt_actionField p
        (hρ x hx) (hS x hx) (hpos x hx)).of_le (by simp))]
  exact (OpenPolarStationaryAction.integrableOn_hydroIntegrand_iff p hU
    (fun x hx => (hρ x hx).differentiableAt (by simp))
    (fun x hx => (hS x hx).differentiableAt (by simp)) hpos e).mp hfinite

/-- Finite real stationarity is exactly relative real stationarity together
with genuine integrability of the full background density. -/
theorem polarStationaryOn_iff_integrable_and_relative (p : MassiveParameters)
    {ρ S : Covector → ℝ} {U : Set Covector} (hU : IsOpen U)
    (hρ : ∀ x ∈ U, ContDiffAt ℝ ∞ ρ x) (hS : ∀ x ∈ U, ContDiffAt ℝ ∞ S x)
    (hpos : ∀ x ∈ U, 0 < ρ x) (e : Fin 4 → Covector) :
    OpenPolarStationaryAction.PolarStationaryOn p ρ S e U ↔
      IntegrableOn (hydroIntegrand p ρ S e) U ∧ RelativePolarStationaryOn p ρ S e U := by
  constructor
  · intro h
    exact ⟨h.1, (relativePolarStationaryOn_iff_polarStationaryOn p hU hρ hS hpos e h.1).2 h⟩
  · rintro ⟨hfinite, hrelative⟩
    exact (relativePolarStationaryOn_iff_polarStationaryOn p hU hρ hS hpos e hfinite).1 hrelative

/-- The nonzero rest-phase field is relatively stationary on every open chart. -/
theorem rest_relativePolarStationaryOn (p : MassiveParameters)
    {U : Set Covector} (hU : IsOpen U) :
    RelativePolarStationaryOn p (fun _ => 1) (RestPlaneWave.restAction p)
      Madelung.coordinateVector U := by
  apply (relativePolarStationaryOn_iff_relativeStationaryOn p hU (fun _ _ => contDiffAt_const)
    (fun _ _ => (RestPlaneWave.contDiff_restAction p ∞).contDiffAt)
    (fun _ _ => by norm_num) Madelung.coordinateVector).mpr
  exact restWave_relativeStationaryOn p hU

end FoliationQM.RelativePolarStationaryAction
