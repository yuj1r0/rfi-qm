module

public import FoliationQM.RelativeAction
public import FoliationQM.OpenStationaryAction

/-!
# Relative stationary action without finite background action

Source: v13 `thm:kahler` and `eq:master_variational_equivalence`.
The action integrates the difference of the two densities over an arbitrary
open region of flat spacetime. Smooth compact interior perturbations make
this difference integrable even when the unperturbed action density is not.
Stationarity therefore imposes no finiteness condition on the background.
The local C² assumption and the actual first variation give the pointwise KG
equation on the region, without any boundary regularity assumption.
-/
@[expose] public section

namespace FoliationQM.RelativeStationaryAction

open MeasureTheory ActionVariation FlatIntegrationByParts PolarSecondDifferential
open scoped ComplexConjugate ContDiff

/-- Zero actual derivative of the relative action along every smooth compact
interior complex perturbation. No integral of the background density occurs
in this definition. -/
def RelativeStationaryOn (p : MassiveParameters) (ψ : Covector → ℂ)
    (e : Fin 4 → Covector) (U : Set Covector) : Prop :=
  ∀ η : Covector → ℂ, ContDiff ℝ ∞ η → HasCompactSupport η → tsupport η ⊆ U →
    HasDerivAt (fun t : ℝ =>
      RelativeAction.relativeAction p ψ (fun x => ψ x + t * η x) e U) 0 0

/-- Relative stationarity detects the pointwise dimensional KG equation using
only C² regularity inside the open region. Integrability of each density
difference is established by the relative-action first-variation theorem. -/
theorem relativeStationaryOn_iff_kgOperator (p : MassiveParameters) {U : Set Covector}
    (hU : IsOpen U) {ψ : Covector → ℂ} (e : Fin 4 → Covector)
    (hψ : ∀ x ∈ U, ContDiffAt ℝ 2 ψ x) :
    RelativeStationaryOn p ψ e U ↔ ∀ x ∈ U, kgOperator p ψ e x = 0 := by
  constructor
  · intro hstationary
    apply OpenFundamentalLemma.continuousOn_eq_zero_of_test_pairings hU
      (kgOperator p ψ e) (OpenIntegrationByParts.continuousOn_kgOperator p hψ e)
    intro η hη hc hs
    have hd := RelativeAction.hasDerivAt_relativeAction_affine_eq_kg_pairing
      p hU e hψ hη hc hs
    have hz := (hstationary η hη hc hs).unique hd
    linarith
  · intro hkg η hη hc hs
    have hd := RelativeAction.hasDerivAt_relativeAction_affine_eq_kg_pairing
      p hU e hψ hη hc hs
    have hz : (∫ x in U, (conj (η x) * kgOperator p ψ e x).re) = 0 := by
      apply integral_eq_zero_of_ae
      filter_upwards [ae_restrict_mem hU.measurableSet] with x hx
      simp only [hkg x hx, mul_zero, Complex.zero_re, Pi.zero_apply]
    simpa only [hz, mul_zero] using hd

/-- In source coordinates, relative stationary action is exactly the
normalized Klein--Gordon equation on the open region. -/
theorem relativeStationaryOn_iff_kleinGordon (p : MassiveParameters) {U : Set Covector}
    (hU : IsOpen U) {ψ : Covector → ℂ}
    (hψ : ∀ x ∈ U, ContDiffAt ℝ 2 ψ x) :
    RelativeStationaryOn p ψ Madelung.coordinateVector U ↔ ∀ x ∈ U,
      box ψ Madelung.coordinateVector x +
        (((p.m ^ 2 * p.c ^ 2 / p.hbar ^ 2 : ℝ) : ℂ) * ψ x) = 0 := by
  rw [relativeStationaryOn_iff_kgOperator p hU Madelung.coordinateVector hψ]
  exact forall_congr' fun x => forall_congr' fun _ =>
    StationaryAction.kgOperator_eq_zero_iff p ψ Madelung.coordinateVector x

/-- When the full background action density is integrable, the relative and
existing finite-action stationary formulations agree. -/
theorem relativeStationaryOn_iff_stationaryOn (p : MassiveParameters) {U : Set Covector}
    (hU : IsOpen U) {ψ : Covector → ℂ} (e : Fin 4 → Covector)
    (hψ : ∀ x ∈ U, ContDiffAt ℝ 2 ψ x)
    (hfinite : IntegrableOn (fun x => (fieldPairing p ψ ψ e x).re) U) :
    RelativeStationaryOn p ψ e U ↔ OpenStationaryAction.StationaryOn p ψ e U := by
  rw [relativeStationaryOn_iff_kgOperator p hU e hψ,
    OpenStationaryAction.stationaryOn_iff_kgOperator p hU e hψ hfinite]

/-- The earlier stationary predicate is exactly relative stationarity together
with integrability of the full background density. -/
theorem stationaryOn_iff_integrable_and_relative (p : MassiveParameters) {U : Set Covector}
    (hU : IsOpen U) {ψ : Covector → ℂ} (e : Fin 4 → Covector)
    (hψ : ∀ x ∈ U, ContDiffAt ℝ 2 ψ x) :
    OpenStationaryAction.StationaryOn p ψ e U ↔
      IntegrableOn (fun x => (fieldPairing p ψ ψ e x).re) U ∧
        RelativeStationaryOn p ψ e U := by
  constructor
  · intro h
    exact ⟨h.1, (relativeStationaryOn_iff_stationaryOn p hU e hψ h.1).2 h⟩
  · rintro ⟨hfinite, hrelative⟩
    exact (relativeStationaryOn_iff_stationaryOn p hU e hψ hfinite).1 hrelative

/-- On the full flat space, relative stationarity agrees with the original
stationary predicate whenever the full action density is integrable. -/
theorem relativeStationaryOn_univ_iff_stationary (p : MassiveParameters)
    {ψ : Covector → ℂ} (e : Fin 4 → Covector) (hψ : ContDiff ℝ 2 ψ)
    (hfinite : Integrable (fun x => (fieldPairing p ψ ψ e x).re)) :
    RelativeStationaryOn p ψ e Set.univ ↔ StationaryAction.Stationary p ψ e := by
  rw [relativeStationaryOn_iff_stationaryOn p isOpen_univ e (fun x _ => hψ.contDiffAt)
    (by simpa only [integrableOn_univ] using hfinite)]
  exact OpenStationaryAction.stationaryOn_univ_iff p ψ e

/-- The unit rest wave is relatively stationary on every open region. The
proof uses its pointwise KG equation, without a finite-action premise. -/
theorem restWave_relativeStationaryOn (p : MassiveParameters) {U : Set Covector}
    (hU : IsOpen U) :
    RelativeStationaryOn p (RestPlaneWave.restWave p) Madelung.coordinateVector U := by
  apply (relativeStationaryOn_iff_kleinGordon p hU
    (fun x _ => (RestPlaneWave.contDiff_restWave p 2).contDiffAt)).2
  exact fun x _ => RestPlaneWave.restWave_kg p x

/-- The constant unit field has a nonzero massive KG operator in any constant
coordinate directions. This supplies an explicit nonstationary background. -/
theorem unitField_kgOperator (p : MassiveParameters) (e : Fin 4 → Covector)
    (x : Covector) :
    kgOperator p (fun _ => (1 : ℂ)) e x = (p.m : ℂ) ^ 2 * (p.c : ℂ) ^ 2 := by
  have hd (v : Covector) : directionalDerivative (fun _ : Covector => (1 : ℂ)) v = 0 := by
    ext y
    simp [directionalDerivative]
  simp [kgOperator, box, secondDirectionalDerivative, hd, directionalDerivative]

/-- The real full action density of the unit field is a nonzero constant. -/
theorem unitField_density (p : MassiveParameters) (e : Fin 4 → Covector)
    (x : Covector) :
    (fieldPairing p (fun _ => (1 : ℂ)) (fun _ => (1 : ℂ)) e x).re =
      -(p.m ^ 2 * p.c ^ 2) := by
  simp [fieldPairing, pairing, kineticPairing, directionalDerivative,
    ← Complex.ofReal_pow, ← Complex.ofReal_mul]

/-- The unit background is smooth but its full action density is not
integrable over the infinite-volume flat spacetime. -/
theorem not_integrable_unitField_density (p : MassiveParameters) (e : Fin 4 → Covector) :
    ¬ Integrable (fun x =>
      (fieldPairing p (fun _ => (1 : ℂ)) (fun _ => (1 : ℂ)) e x).re) := by
  simp_rw [unitField_density]
  rw [integrable_const_iff]
  have hn : -(p.m ^ 2 * p.c ^ 2) ≠ 0 :=
    neg_ne_zero.mpr (mul_ne_zero (pow_ne_zero _ (ne_of_gt p.m_pos))
      (pow_ne_zero _ (ne_of_gt p.c_pos)))
  have hv : (volume : Measure Covector) Set.univ = ⊤ := by
    simp [Covector, volume_pi]
  simp [hn, isFiniteMeasure_iff, hv]

/-- Despite the infinite full background action, every smooth compact affine
perturbation of the unit field has an integrable relative density. -/
theorem integrable_relativeDensity_unitField_affine (p : MassiveParameters)
    {η : Covector → ℂ} (e : Fin 4 → Covector) (hη : ContDiff ℝ ∞ η)
    (hc : HasCompactSupport η) (t : ℝ) :
    Integrable (RelativeAction.relativeDensity p (fun _ => (1 : ℂ))
      (fun x => 1 + t * η x) e) := by
  simpa only [integrableOn_univ] using
    RelativeAction.integrableOn_relativeDensity_affine p isOpen_univ e
      (fun _ _ => contDiffAt_const) hη hc (Set.subset_univ _) t

/-- A compact change cannot make the unit background's full action density
integrable. Both full densities can therefore be nonintegrable while their
literal difference has a genuine integral. -/
theorem not_integrable_unitField_affine_density (p : MassiveParameters)
    {η : Covector → ℂ} (e : Fin 4 → Covector) (hη : ContDiff ℝ ∞ η)
    (hc : HasCompactSupport η) (t : ℝ) :
    ¬ Integrable (fun x =>
      (fieldPairing p (fun y => 1 + t * η y) (fun y => 1 + t * η y) e x).re) := by
  intro hfinite
  apply not_integrable_unitField_density p e
  have hrelative := integrable_relativeDensity_unitField_affine p e hη hc t
  convert hfinite.sub hrelative using 1
  ext x
  simp [RelativeAction.relativeDensity]

/-- The admissible nonintegrable unit background is not relatively stationary
on any nonempty open region. Thus the relative definition does not declare
nonintegrable backgrounds stationary merely through totalized integration. -/
theorem not_relativeStationaryOn_unitField (p : MassiveParameters) {U : Set Covector}
    (hU : IsOpen U) (hne : U.Nonempty) (e : Fin 4 → Covector) :
    ¬ RelativeStationaryOn p (fun _ => (1 : ℂ)) e U := by
  intro hstationary
  obtain ⟨x, hx⟩ := hne
  have hkg := (relativeStationaryOn_iff_kgOperator p hU e
    (fun _ _ => contDiffAt_const)).1 hstationary x hx
  rw [unitField_kgOperator] at hkg
  exact mul_ne_zero
    (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr (ne_of_gt p.m_pos)))
    (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr (ne_of_gt p.c_pos))) hkg

end FoliationQM.RelativeStationaryAction
