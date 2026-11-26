module

public import FoliationQM.OpenFundamentalLemma
public import FoliationQM.OpenIntegrationByParts
public import FoliationQM.RestPlaneWave

/-!
# Stationary action on an arbitrary open flat domain

Source: v13 `thm:kahler` and `eq:master_variational_equivalence`.
The action uses Lebesgue volume restricted to the domain. Compactly supported
interior tests remove the boundary term, without any regularity assumption on
the boundary. The background field is only C² locally on the domain; its
values and regularity outside the domain are unrestricted. The finite action
condition concerns the full real indefinite density.
-/
@[expose] public section

namespace FoliationQM.OpenStationaryAction

open MeasureTheory ActionVariation FlatIntegrationByParts PolarSecondDifferential
open scoped ComplexConjugate ContDiff

/-- Every affine compact interior perturbation has an integrable real action
density whenever the unperturbed density is integrable on the open domain. -/
theorem integrableOn_variation (p : MassiveParameters) {U : Set Covector}
    (hU : IsOpen U) {ψ η : Covector → ℂ} (e : Fin 4 → Covector)
    (hψ : ∀ x ∈ U, ContDiffAt ℝ 2 ψ x) (hη : ContDiff ℝ ∞ η)
    (hc : HasCompactSupport η) (hs : tsupport η ⊆ U)
    (hfinite : IntegrableOn (fun x => (fieldPairing p ψ ψ e x).re) U) (t : ℝ) :
    IntegrableOn (fun x =>
      (fieldPairing p (fun y => ψ y + t * η y) (fun y => ψ y + t * η y) e x).re) U := by
  have hη1 : ContDiff ℝ 1 η := hη.of_le (by norm_num)
  have hη2 : ContDiff ℝ 2 η := hη.of_le (by norm_num)
  have hψae : ∀ᵐ x ∂volume.restrict U, DifferentiableAt ℝ ψ x := by
    filter_upwards [ae_restrict_mem hU.measurableSet] with x hx
    exact (hψ x hx).differentiableAt (by norm_num)
  exact integrable_variation p ψ η e (volume.restrict U) hψae
    (Filter.Eventually.of_forall (hη.differentiable (by simp))) hfinite
    (OpenIntegrationByParts.integrable_fieldPairing p hη1 hψ hc hs e).re
    (FlatIntegrationByParts.integrable_fieldPairing p hη1 hη2 hc e).re.integrableOn t

/-- The derivative of the actual finite restricted action is the weak KG
pairing. The exact quadratic expansion justifies differentiation, and compact
interior support supplies integration by parts. -/
theorem hasDerivAt_action_eq_kg_pairing (p : MassiveParameters) {U : Set Covector}
    (hU : IsOpen U) {ψ η : Covector → ℂ} (e : Fin 4 → Covector)
    (hψ : ∀ x ∈ U, ContDiffAt ℝ 2 ψ x) (hη : ContDiff ℝ ∞ η)
    (hc : HasCompactSupport η) (hs : tsupport η ⊆ U)
    (hfinite : IntegrableOn (fun x => (fieldPairing p ψ ψ e x).re) U) :
    HasDerivAt (fun t : ℝ => action p (fun x => ψ x + t * η x) e (volume.restrict U))
      (-2 * ∫ x in U, (conj (η x) * kgOperator p ψ e x).re) 0 := by
  have hη1 : ContDiff ℝ 1 η := hη.of_le (by norm_num)
  have hη2 : ContDiff ℝ 2 η := hη.of_le (by norm_num)
  have hψae : ∀ᵐ x ∂volume.restrict U, DifferentiableAt ℝ ψ x := by
    filter_upwards [ae_restrict_mem hU.measurableSet] with x hx
    exact (hψ x hx).differentiableAt (by norm_num)
  have hd := hasDerivAt_action_variation p ψ η e (volume.restrict U) hψae
    (Filter.Eventually.of_forall (hη.differentiable (by simp))) hfinite
    (OpenIntegrationByParts.integrable_fieldPairing p hη1 hψ hc hs e).re
    (FlatIntegrationByParts.integrable_fieldPairing p hη1 hη2 hc e).re.integrableOn
  rw [OpenIntegrationByParts.integral_re_fieldPairing_eq p hη1 hψ hc hs e] at hd
  convert hd using 1
  ring

/-- Stationarity on a domain includes finiteness of its actual action and zero
derivative along every globally smooth compactly supported interior test. -/
def StationaryOn (p : MassiveParameters) (ψ : Covector → ℂ)
    (e : Fin 4 → Covector) (U : Set Covector) : Prop :=
  IntegrableOn (fun x => (fieldPairing p ψ ψ e x).re) U ∧
    ∀ η : Covector → ℂ, ContDiff ℝ ∞ η → HasCompactSupport η → tsupport η ⊆ U →
      HasDerivAt (fun t : ℝ => action p (fun x => ψ x + t * η x) e (volume.restrict U)) 0 0

/-- The actual restricted action is stationary precisely when its KG operator
vanishes pointwise on the open domain. No global background regularity is used. -/
theorem stationaryOn_iff_kgOperator (p : MassiveParameters) {U : Set Covector}
    (hU : IsOpen U) {ψ : Covector → ℂ} (e : Fin 4 → Covector)
    (hψ : ∀ x ∈ U, ContDiffAt ℝ 2 ψ x)
    (hfinite : IntegrableOn (fun x => (fieldPairing p ψ ψ e x).re) U) :
    StationaryOn p ψ e U ↔ ∀ x ∈ U, kgOperator p ψ e x = 0 := by
  constructor
  · intro hstationary
    apply OpenFundamentalLemma.continuousOn_eq_zero_of_test_pairings hU
      (kgOperator p ψ e) (OpenIntegrationByParts.continuousOn_kgOperator p hψ e)
    intro η hη hc hs
    have hd := hasDerivAt_action_eq_kg_pairing p hU e hψ hη hc hs hfinite
    have hz := (hstationary.2 η hη hc hs).unique hd
    linarith
  · intro hkg
    refine ⟨hfinite, ?_⟩
    intro η hη hc hs
    have hd := hasDerivAt_action_eq_kg_pairing p hU e hψ hη hc hs hfinite
    have hz : (∫ x in U, (conj (η x) * kgOperator p ψ e x).re) = 0 := by
      apply integral_eq_zero_of_ae
      filter_upwards [ae_restrict_mem hU.measurableSet] with x hx
      simp only [hkg x hx, mul_zero, Complex.zero_re, Pi.zero_apply]
    simpa only [hz, mul_zero] using hd

/-- In the source coordinate directions, open-domain stationarity is exactly
the normalized Klein--Gordon equation at every point of the domain. -/
theorem stationaryOn_iff_kleinGordon (p : MassiveParameters) {U : Set Covector}
    (hU : IsOpen U) {ψ : Covector → ℂ}
    (hψ : ∀ x ∈ U, ContDiffAt ℝ 2 ψ x)
    (hfinite : IntegrableOn (fun x =>
      (fieldPairing p ψ ψ Madelung.coordinateVector x).re) U) :
    StationaryOn p ψ Madelung.coordinateVector U ↔ ∀ x ∈ U,
      box ψ Madelung.coordinateVector x +
        (((p.m ^ 2 * p.c ^ 2 / p.hbar ^ 2 : ℝ) : ℂ) * ψ x) = 0 := by
  rw [stationaryOn_iff_kgOperator p hU Madelung.coordinateVector hψ hfinite]
  exact forall_congr' fun x => forall_congr' fun _ =>
    StationaryAction.kgOperator_eq_zero_iff p ψ Madelung.coordinateVector x

/-- The open-domain stationarity definition recovers the existing whole-space
definition when the domain is all flat spacetime. -/
theorem stationaryOn_univ_iff (p : MassiveParameters) (ψ : Covector → ℂ)
    (e : Fin 4 → Covector) :
    StationaryOn p ψ e Set.univ ↔ StationaryAction.Stationary p ψ e := by
  simp [StationaryOn, StationaryAction.Stationary, IntegrableOn]

/-- The nowhere-zero unit rest wave supplies a finite stationary example on
every open domain, including domains with irregular or unbounded boundary. -/
theorem restWave_stationaryOn (p : MassiveParameters) {U : Set Covector} (hU : IsOpen U) :
    StationaryOn p (RestPlaneWave.restWave p) Madelung.coordinateVector U := by
  apply (stationaryOn_iff_kleinGordon p hU
    (fun x _ => (RestPlaneWave.contDiff_restWave p 2).contDiffAt)
    (RestPlaneWave.integrable_restWave_self p (volume.restrict U))).2
  exact fun x _ => RestPlaneWave.restWave_kg p x

end FoliationQM.OpenStationaryAction
