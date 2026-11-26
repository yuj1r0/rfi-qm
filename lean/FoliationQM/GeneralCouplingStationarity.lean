module

public import FoliationQM.GeneralCouplingAction
public import FoliationQM.NonlinearDefectEquivalence

/-!
# General Fisher coupling: actual stationarity and the fixed-clock defect

Sources: v13 `eq:general_lambda_action`, `eq:nonlinear_defect`, and
`lem:uniqueness` (ii). The stationarity predicate uses the literal real
relative action and independent compact interior density/phase variations.
For positive λ, an auxiliary parameter record transports the established
variational proof. The final wave equation uses the original physical ℏ
and the original phase S/ℏ; neither is rescaled in that conclusion.
-/
@[expose] public section

namespace FoliationQM.GeneralCouplingStationarity

open MeasureTheory GeneralCouplingAction PolarSecondDifferential
open scoped ContDiff

/-- Stationarity of the literal general-coupling density-change integral
under all independent smooth compact interior real variations. -/
def RelativeStationaryOn (p : MassiveParameters) (lam : ℝ) (ρ S : Covector → ℝ)
    (e : Fin 4 → Covector) (U : Set Covector) : Prop :=
  ∀ a b : Covector → ℝ, ContDiff ℝ ∞ a → ContDiff ℝ ∞ b →
    HasCompactSupport a → HasCompactSupport b → tsupport a ⊆ U → tsupport b ⊆ U →
    HasDerivAt (fun t : ℝ => relativeHydroAction p lam ρ S
      (fun x => ρ x + t * a x) (fun x => S x + t * b x) e U) 0 0

/-- Literal functional equality transports the entire independent real test
class; no PDE or regularity is assumed in this identification. -/
theorem relativeStationaryOn_iff_effective (p : MassiveParameters) (lam : ℝ)
    (hlam : 0 < lam) (ρ S : Covector → ℝ) (e : Fin 4 → Covector) (U : Set Covector) :
    RelativeStationaryOn p lam ρ S e U ↔
      RelativePolarStationaryAction.RelativePolarStationaryOn
        (effectiveParameters p lam hlam) ρ S e U := by
  simp only [RelativeStationaryOn, RelativePolarStationaryAction.RelativePolarStationaryOn,
    relativeHydroAction_eq_effective p hlam]

/-- The physical canonical coefficient recovers exactly the existing predicate. -/
theorem relativeStationaryOn_canonical (p : MassiveParameters)
    (ρ S : Covector → ℝ) (e : Fin 4 → Covector) (U : Set Covector) :
    RelativeStationaryOn p (p.hbar ^ 2 / 4) ρ S e U ↔
      RelativePolarStationaryAction.RelativePolarStationaryOn p ρ S e U := by
  rfl

/-- Generalized Hamilton--Jacobi and actual current continuity are equivalent
to actual relative stationarity. They are derived conclusions, not premises.
Background smoothness and positivity are needed only on the open region. -/
theorem relativeStationaryOn_iff_madelung (p : MassiveParameters) (lam : ℝ)
    (hlam : 0 < lam) {ρ S : Covector → ℝ} {U : Set Covector} (hU : IsOpen U)
    (hρ : ∀ x ∈ U, ContDiffAt ℝ ∞ ρ x) (hS : ∀ x ∈ U, ContDiffAt ℝ ∞ S x)
    (hpos : ∀ x ∈ U, 0 < ρ x) (e : Fin 4 → Covector) :
    RelativeStationaryOn p lam ρ S e U ↔ ∀ x ∈ U,
      minkowski (fun μ => directionalDerivative S (e μ) x)
          (fun μ => directionalDerivative S (e μ) x) - p.m ^ 2 * p.c ^ 2 =
        4 * lam * box (fun y => Real.sqrt (ρ y)) e x / Real.sqrt (ρ x) ∧
      PolarRegularity.densityCurrentDivergence ρ S e x = 0 := by
  rw [relativeStationaryOn_iff_effective p lam hlam,
    RelativePolarStationaryAction.relativePolarStationaryOn_iff_kgOperator
      (effectiveParameters p lam hlam) hU hρ hS hpos e]
  refine forall_congr' fun x => forall_congr' fun hx => ?_
  rw [StationaryAction.kgOperator_eq_zero_iff]
  have h := PolarRegularity.kg_eq_zero_iff_madelung_density
    (effectiveParameters p lam hlam) ((hρ x hx).of_le (by simp))
    ((hS x hx).of_le (by simp)) (hpos x hx) e
  rw [effectiveParameters_hbar_sq p hlam] at h ⊢
  refine h.trans ?_
  change (_ = p.m ^ 2 * p.c ^ 2 + _ ∧ _) ↔ _
  constructor
  · rintro ⟨hHJ, hc⟩
    exact ⟨by linarith, hc⟩
  · rintro ⟨hHJ, hc⟩
    exact ⟨by linarith, hc⟩

/-- The fixed-physical-clock nonlinear modulus equation characterizes the
stationary fields of the positive general-coupling action, in both directions. -/
theorem relativeStationaryOn_iff_nonlinearModulusDefect (p : MassiveParameters)
    (lam : ℝ) (hlam : 0 < lam) {ρ S : Covector → ℝ} {U : Set Covector} (hU : IsOpen U)
    (hρ : ∀ x ∈ U, ContDiffAt ℝ ∞ ρ x) (hS : ∀ x ∈ U, ContDiffAt ℝ ∞ S x)
    (hpos : ∀ x ∈ U, 0 < ρ x) (e : Fin 4 → Covector) :
    RelativeStationaryOn p lam ρ S e U ↔ ∀ x ∈ U,
      box (ActionDensity.actionField p ρ S) e x +
        (((p.m ^ 2 * p.c ^ 2 / p.hbar ^ 2 : ℝ) : ℂ) * ActionDensity.actionField p ρ S x) =
        (((1 - 4 * lam / p.hbar ^ 2) *
          box (fun y => ‖ActionDensity.actionField p ρ S y‖) e x /
            ‖ActionDensity.actionField p ρ S x‖ : ℝ) : ℂ) *
          ActionDensity.actionField p ρ S x := by
  rw [relativeStationaryOn_iff_madelung p lam hlam hU hρ hS hpos e]
  exact forall_congr' fun x => forall_congr' fun hx =>
    (NonlinearDefectEquivalence.kg_eq_nonlinearModulusDefect_density_iff p lam
      ((hρ x hx).of_le (by simp)) ((hS x hx).of_le (by simp)) (hpos x hx) e).symm

/-- At the selected physical coefficient, general-coupling stationarity
recovers the linear physical KG equation. -/
theorem relativeStationaryOn_canonical_iff_kleinGordon (p : MassiveParameters)
    {ρ S : Covector → ℝ} {U : Set Covector} (hU : IsOpen U)
    (hρ : ∀ x ∈ U, ContDiffAt ℝ ∞ ρ x) (hS : ∀ x ∈ U, ContDiffAt ℝ ∞ S x)
    (hpos : ∀ x ∈ U, 0 < ρ x) :
    RelativeStationaryOn p (p.hbar ^ 2 / 4) ρ S Madelung.coordinateVector U ↔ ∀ x ∈ U,
      box (ActionDensity.actionField p ρ S) Madelung.coordinateVector x +
        (((p.m ^ 2 * p.c ^ 2 / p.hbar ^ 2 : ℝ) : ℂ) * ActionDensity.actionField p ρ S x) = 0 := by
  rw [relativeStationaryOn_canonical]
  exact RelativePolarStationaryAction.relativePolarStationaryOn_iff_kleinGordon p hU hρ hS hpos

/-- The same physical rest phase is stationary for every positive coupling.
A single field with zero nonlinear defect therefore cannot select λ. -/
theorem rest_relativeStationaryOn (p : MassiveParameters) (lam : ℝ) (hlam : 0 < lam)
    {U : Set Covector} (hU : IsOpen U) :
    RelativeStationaryOn p lam (fun _ => 1) (RestPlaneWave.restAction p)
      Madelung.coordinateVector U := by
  rw [relativeStationaryOn_iff_effective p lam hlam]
  exact RelativePolarStationaryAction.rest_relativePolarStationaryOn
    (effectiveParameters p lam hlam) hU

/-- Ordinary stationary action, with a genuinely integrable full background
source density and actual zero derivatives under the same real tests. -/
def StationaryOn (p : MassiveParameters) (lam : ℝ) (ρ S : Covector → ℝ)
    (e : Fin 4 → Covector) (U : Set Covector) : Prop :=
  IntegrableOn (hydroIntegrand p lam ρ S e) U ∧
    ∀ a b : Covector → ℝ, ContDiff ℝ ∞ a → ContDiff ℝ ∞ b →
      HasCompactSupport a → HasCompactSupport b → tsupport a ⊆ U → tsupport b ⊆ U →
      HasDerivAt (fun t : ℝ => hydroActionOn p lam
        (fun x => ρ x + t * a x) (fun x => S x + t * b x) e U) 0 0

/-- The ordinary finite-action predicate has the same exact auxiliary
identification, including its explicit integrability requirement. -/
theorem stationaryOn_iff_effective (p : MassiveParameters) (lam : ℝ) (hlam : 0 < lam)
    (ρ S : Covector → ℝ) (e : Fin 4 → Covector) (U : Set Covector) :
    StationaryOn p lam ρ S e U ↔
      OpenPolarStationaryAction.PolarStationaryOn (effectiveParameters p lam hlam) ρ S e U := by
  simp only [StationaryOn, OpenPolarStationaryAction.PolarStationaryOn,
    funext (hydroIntegrand_eq_effective p hlam ρ S e), hydroActionOn_eq_effective p hlam]

/-- Ordinary stationarity is exactly relative stationarity plus full-density
integrability. Compact changes do not silently supply finite background action. -/
theorem stationaryOn_iff_integrable_and_relative (p : MassiveParameters) (lam : ℝ)
    (hlam : 0 < lam) {ρ S : Covector → ℝ} {U : Set Covector} (hU : IsOpen U)
    (hρ : ∀ x ∈ U, ContDiffAt ℝ ∞ ρ x) (hS : ∀ x ∈ U, ContDiffAt ℝ ∞ S x)
    (hpos : ∀ x ∈ U, 0 < ρ x) (e : Fin 4 → Covector) :
    StationaryOn p lam ρ S e U ↔
      IntegrableOn (hydroIntegrand p lam ρ S e) U ∧ RelativeStationaryOn p lam ρ S e U := by
  rw [stationaryOn_iff_effective p lam hlam,
    RelativePolarStationaryAction.polarStationaryOn_iff_integrable_and_relative
      (effectiveParameters p lam hlam) hU hρ hS hpos e,
    relativeStationaryOn_iff_effective p lam hlam,
    funext (hydroIntegrand_eq_effective p hlam ρ S e)]

/-- The literal ordinary source action also yields exactly the fixed-clock
nonlinear modulus equation when its full density is genuinely integrable. -/
theorem stationaryOn_iff_nonlinearModulusDefect (p : MassiveParameters) (lam : ℝ)
    (hlam : 0 < lam) {ρ S : Covector → ℝ} {U : Set Covector} (hU : IsOpen U)
    (hρ : ∀ x ∈ U, ContDiffAt ℝ ∞ ρ x) (hS : ∀ x ∈ U, ContDiffAt ℝ ∞ S x)
    (hpos : ∀ x ∈ U, 0 < ρ x) (e : Fin 4 → Covector)
    (hfinite : IntegrableOn (hydroIntegrand p lam ρ S e) U) :
    StationaryOn p lam ρ S e U ↔ ∀ x ∈ U,
      box (ActionDensity.actionField p ρ S) e x +
        (((p.m ^ 2 * p.c ^ 2 / p.hbar ^ 2 : ℝ) : ℂ) * ActionDensity.actionField p ρ S x) =
        (((1 - 4 * lam / p.hbar ^ 2) *
          box (fun y => ‖ActionDensity.actionField p ρ S y‖) e x /
            ‖ActionDensity.actionField p ρ S x‖ : ℝ) : ℂ) *
          ActionDensity.actionField p ρ S x := by
  rw [stationaryOn_iff_integrable_and_relative p lam hlam hU hρ hS hpos e,
    and_iff_right hfinite]
  exact relativeStationaryOn_iff_nonlinearModulusDefect p lam hlam hU hρ hS hpos e

end FoliationQM.GeneralCouplingStationarity
