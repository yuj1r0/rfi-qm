module

public import FoliationQM.ScalarSectorDensity
public import FoliationQM.RelativePolarStationaryAction

/-!
# Variational dynamics on the scalar plane-rotor sector

For v13 `thm:dirac_lift` and `eq:coupled_action`, the mass-completed
spinor kinetic density restricted to the plane-rotor field has the scalar
action. Independent compact variations of its amplitude density and phase
give the flat Klein–Gordon, Hamilton–Jacobi and continuity equations.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.ScalarSectorAction

open MeasureTheory DiracFieldDensity ScalarSectorDensity PolarChartAction
open RelativePolarStationaryAction PolarTestVariations FlatIntegrationByParts
open scoped Topology ContDiff ComplexConjugate

/-- The mass-completed neutralized spinor density of the actual plane rotor, at chiral angle zero. -/
def integrand (p : MassiveParameters) (ρ S : Covector → ℝ) (x : Covector) : ℝ :=
  MassiveSpinKinetic.density p 0 (field p ρ S) x

/-- The ordinary Lebesgue action of the plane-rotor field on the region. -/
def action (p : MassiveParameters) (ρ S : Covector → ℝ) (U : Set Covector) : ℝ :=
  ∫ x in U, integrand p ρ S x

/-- The pointwise change of the spinor density, with the background first. -/
def increment (p : MassiveParameters) (ρ S ρ' S' : Covector → ℝ) (x : Covector) : ℝ :=
  integrand p ρ' S' x - integrand p ρ S x

/-- The relative spinor action integrates the change before integration of either density. -/
def relativeAction (p : MassiveParameters) (ρ S ρ' S' : Covector → ℝ) (U : Set Covector) : ℝ :=
  ∫ x in U, increment p ρ S ρ' S' x

/-- The ordinary sector density is integrable precisely when the scalar action density is. -/
theorem integrableOn_iff (p : MassiveParameters) {ρ S : Covector → ℝ} {U : Set Covector}
    (hU : IsOpen U) (hρ : ∀ x ∈ U, DifferentiableAt ℝ ρ x)
    (hS : ∀ x ∈ U, DifferentiableAt ℝ S x) (hp : ∀ x ∈ U, 0 < ρ x) :
    IntegrableOn (integrand p ρ S) U ↔ IntegrableOn (hydroIntegrand p ρ S coordinateDirections) U := by
  apply integrable_congr
  filter_upwards [ae_restrict_mem hU.measurableSet] with x hx
  exact density_eq_hydroIntegrand p (hρ x hx) (hS x hx) (hp x hx)

/-- Equality of ordinary plane-rotor and scalar actions on the positive differentiable region. -/
theorem action_eq_hydro (p : MassiveParameters) {ρ S : Covector → ℝ} {U : Set Covector}
    (hU : IsOpen U) (hρ : ∀ x ∈ U, DifferentiableAt ℝ ρ x)
    (hS : ∀ x ∈ U, DifferentiableAt ℝ S x) (hp : ∀ x ∈ U, 0 < ρ x) :
    action p ρ S U = OpenPolarStationaryAction.hydroActionOn p ρ S coordinateDirections U := by
  apply setIntegral_congr_fun hU.measurableSet
  exact fun x hx => density_eq_hydroIntegrand p (hρ x hx) (hS x hx) (hp x hx)

/-- Pointwise changes agree for any two positive, differentiable polar fields. -/
theorem increment_eq_hydro (p : MassiveParameters) {ρ S ρ' S' : Covector → ℝ} {x : Covector}
    (hρ : DifferentiableAt ℝ ρ x) (hS : DifferentiableAt ℝ S x)
    (hρ' : DifferentiableAt ℝ ρ' x) (hS' : DifferentiableAt ℝ S' x)
    (hp : 0 < ρ x) (hp' : 0 < ρ' x) :
    increment p ρ S ρ' S' x = relativeHydroDensity p ρ S ρ' S' coordinateDirections x := by
  simp only [increment, integrand, relativeHydroDensity,
    density_eq_hydroIntegrand p hρ' hS' hp', density_eq_hydroIntegrand p hρ hS hp]

/-- The relative scalar action equals the integral of the spinor increment on the open region. -/
theorem relativeAction_eq_hydro (p : MassiveParameters) {ρ S ρ' S' : Covector → ℝ} {U : Set Covector}
    (hU : IsOpen U) (hρ : ∀ x ∈ U, DifferentiableAt ℝ ρ x) (hS : ∀ x ∈ U, DifferentiableAt ℝ S x)
    (hρ' : ∀ x ∈ U, DifferentiableAt ℝ ρ' x) (hS' : ∀ x ∈ U, DifferentiableAt ℝ S' x)
    (hp : ∀ x ∈ U, 0 < ρ x) (hp' : ∀ x ∈ U, 0 < ρ' x) :
    relativeAction p ρ S ρ' S' U = relativeHydroAction p ρ S ρ' S' coordinateDirections U := by
  apply setIntegral_congr_fun hU.measurableSet
  exact fun x hx => increment_eq_hydro p (hρ x hx) (hS x hx) (hρ' x hx) (hS' x hx) (hp x hx) (hp' x hx)

/-- With integrable ordinary densities the relative action is their action difference. -/
theorem relativeAction_eq_sub (p : MassiveParameters) {ρ S ρ' S' : Covector → ℝ} {U : Set Covector}
    (hbase : IntegrableOn (integrand p ρ S) U) (hpert : IntegrableOn (integrand p ρ' S') U) :
    relativeAction p ρ S ρ' S' U = action p ρ' S' U - action p ρ S U :=
  integral_sub hpert hbase

/-- Stationarity tests compact, independent changes of the density and phase in the actual spinor action. -/
def StationaryOn (p : MassiveParameters) (ρ S : Covector → ℝ) (U : Set Covector) : Prop :=
  ∀ a b : Covector → ℝ, ContDiff ℝ ∞ a → ContDiff ℝ ∞ b →
    HasCompactSupport a → HasCompactSupport b → tsupport a ⊆ U → tsupport b ⊆ U →
    HasDerivAt (fun t : ℝ => relativeAction p ρ S
      (fun x => ρ x + t * a x) (fun x => S x + t * b x) U) 0 0

section Smooth
variable (p : MassiveParameters) {ρ S : Covector → ℝ} {U : Set Covector} (hU : IsOpen U)
    (hρ : ∀ x ∈ U, ContDiffAt ℝ ∞ ρ x) (hS : ∀ x ∈ U, ContDiffAt ℝ ∞ S x)
    (hp : ∀ x ∈ U, 0 < ρ x)

include p hρ hS hp in
/-- Compact support of the density test gives one parameter neighborhood of positivity throughout U. -/
theorem eventually_pos_affine {a b : Covector → ℝ} (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (hca : HasCompactSupport a) (hsa : tsupport a ⊆ U) :
    ∀ᶠ t in 𝓝 (0 : ℝ), ∀ x ∈ U, 0 < ρ x + t * a x := by
  obtain ⟨ε, hε, h⟩ := OpenPolarVariations.exists_pos_contDiffAt_curve p hρ hS ha hb hp hca hsa
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hε] with t ht x hx
  exact (h t (by simpa only [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] using ht) x hx).1

include hρ hS hp in
private theorem eventually_increment_eq_hydro {a b : Covector → ℝ}
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b) (hca : HasCompactSupport a) (hsa : tsupport a ⊆ U) :
    ∀ᶠ t in 𝓝 (0 : ℝ), ∀ x ∈ U, increment p ρ S (fun y => ρ y + t*a y) (fun y => S y + t*b y) x =
      relativeHydroDensity p ρ S (fun y => ρ y + t*a y) (fun y => S y + t*b y) coordinateDirections x := by
  filter_upwards [eventually_pos_affine p hρ hS hp ha hb hca hsa] with t hpos x hx
  exact increment_eq_hydro p ((hρ x hx).differentiableAt (by simp)) ((hS x hx).differentiableAt (by simp))
    (((hρ x hx).add (contDiffAt_const.mul ha.contDiffAt)).differentiableAt (by simp))
    (((hS x hx).add (contDiffAt_const.mul hb.contDiffAt)).differentiableAt (by simp)) (hp x hx) (hpos x hx)

include hU hρ hS hp in
/-- Each small compact interior affine perturbation has an integrable spinor density increment. -/
theorem eventually_integrableOn_increment {a b : Covector → ℝ} (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (hca : HasCompactSupport a) (hcb : HasCompactSupport b) (hsa : tsupport a ⊆ U) (hsb : tsupport b ⊆ U) :
    ∀ᶠ t in 𝓝 (0 : ℝ), IntegrableOn (increment p ρ S (fun y => ρ y + t*a y) (fun y => S y + t*b y)) U := by
  filter_upwards [eventually_integrableOn_relativeHydroDensity_affine p hU hρ hS ha hb hp hca hcb hsa hsb
    coordinateDirections, eventually_increment_eq_hydro p hρ hS hp ha hb hca hsa] with t hi he
  apply hi.congr
  filter_upwards [ae_restrict_mem hU.measurableSet] with x hx
  exact (he x hx).symm

include hU hρ hS hp in
/-- Sector and scalar relative actions have equal germs along the independent affine variations. -/
theorem eventuallyEq_relativeAction_affine {a b : Covector → ℝ} (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (hca : HasCompactSupport a) (hsa : tsupport a ⊆ U) :
    (fun t : ℝ => relativeAction p ρ S (fun y => ρ y + t*a y) (fun y => S y + t*b y) U)
      =ᶠ[𝓝 0] (fun t : ℝ => relativeHydroAction p ρ S (fun y => ρ y + t*a y) (fun y => S y + t*b y)
        coordinateDirections U) := by
  filter_upwards [eventually_increment_eq_hydro p hρ hS hp ha hb hca hsa] with t he
  exact setIntegral_congr_fun hU.measurableSet he

include hU hρ hS hp in
/-- The actual relative spinor action has the Klein–Gordon residual pairing as its derivative. -/
theorem hasDerivAt_relativeAction_affine {a b : Covector → ℝ} (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (hca : HasCompactSupport a) (hcb : HasCompactSupport b) (hsa : tsupport a ⊆ U) (hsb : tsupport b ⊆ U) :
    HasDerivAt (fun t : ℝ => relativeAction p ρ S (fun y => ρ y + t*a y) (fun y => S y + t*b y) U)
      (-2 * ∫ x in U, (conj (testTangent p ρ S a b x) *
         kgOperator p (ActionDensity.actionField p ρ S) coordinateDirections x).re) 0 :=
  (hasDerivAt_relativeHydroAction_affine p hU hρ hS ha hb hp hca hcb hsa hsb coordinateDirections)
    |>.congr_of_eventuallyEq (eventuallyEq_relativeAction_affine p hU hρ hS hp ha hb hca hsa)

include hU hρ hS hp in
/-- Restricted spinor stationarity is precisely the existing real relative scalar stationarity. -/
theorem stationaryOn_iff_relativePolar :
    StationaryOn p ρ S U ↔ RelativePolarStationaryOn p ρ S coordinateDirections U := by
  constructor
  · intro h a b ha hb hca hcb hsa hsb
    exact (h a b ha hb hca hcb hsa hsb).congr_of_eventuallyEq
      (eventuallyEq_relativeAction_affine p hU hρ hS hp ha hb hca hsa).symm
  · intro h a b ha hb hca hcb hsa hsb
    exact (h a b ha hb hca hcb hsa hsb).congr_of_eventuallyEq
      (eventuallyEq_relativeAction_affine p hU hρ hS hp ha hb hca hsa)

include hU hρ hS hp in
/-- Restricted stationarity is equivalent to the normalized scalar Klein–Gordon equation on U. -/
theorem stationaryOn_iff_kleinGordon : StationaryOn p ρ S U ↔ ∀ x ∈ U,
    PolarSecondDifferential.box (ActionDensity.actionField p ρ S) coordinateDirections x +
      (((p.m^2 * p.c^2 / p.hbar^2 : ℝ) : ℂ) * ActionDensity.actionField p ρ S x) = 0 :=
  (stationaryOn_iff_relativePolar p hU hρ hS hp).trans
    (relativePolarStationaryOn_iff_kleinGordon p hU hρ hS hp)

include hU hρ hS hp in
/-- Restricted stationarity gives both the true Hamilton–Jacobi equation and density-current conservation. -/
theorem stationaryOn_iff_madelung : StationaryOn p ρ S U ↔ ∀ x ∈ U,
    minkowski (ScalarSpinDefect.gradient S x) (ScalarSpinDefect.gradient S x) = p.m^2 * p.c^2 +
      p.hbar^2 * PolarSecondDifferential.box (fun y => Real.sqrt (ρ y)) coordinateDirections x /
        Real.sqrt (ρ x) ∧ PolarRegularity.densityCurrentDivergence ρ S coordinateDirections x = 0 :=
  (stationaryOn_iff_relativePolar p hU hρ hS hp).trans
    (relativePolarStationaryOn_iff_madelung p hU hρ hS hp)

end Smooth
end FoliationQM.ScalarSectorAction
