module

public import FoliationQM.OpenIntegrationByParts

/-!
# Relative quadratic action on open flat domains

Sources: v13 `thm:kahler` and `eq:master_variational_equivalence`.
The relative action integrates the difference of the perturbed and background
densities. Compact interior changes make this difference integrable without
any integrability assumption on the background density itself. The exact
quadratic expansion supplies an actual first derivative, and interior-test
integration by parts identifies its Klein--Gordon pairing.
-/
@[expose] public section

namespace FoliationQM.RelativeAction

open MeasureTheory ActionVariation FlatIntegrationByParts
open scoped ComplexConjugate ContDiff

/-- The literal real density difference, with the background field first. -/
noncomputable def relativeDensity (p : MassiveParameters) (ψ φ : Covector → ℂ)
    (e : Fin 4 → Covector) (x : Covector) : ℝ :=
  (fieldPairing p φ φ e x).re - (fieldPairing p ψ ψ e x).re

/-- Relative action integrates the density difference on the domain. It is
not defined by subtracting two separately totalized action integrals. -/
noncomputable def relativeAction (p : MassiveParameters) (ψ φ : Covector → ℂ)
    (e : Fin 4 → Covector) (U : Set Covector) : ℝ :=
  ∫ x in U, relativeDensity p ψ φ e x

/-- An unchanged field has identically zero relative density. -/
theorem relativeDensity_self (p : MassiveParameters) (ψ : Covector → ℂ)
    (e : Fin 4 → Covector) (x : Covector) : relativeDensity p ψ ψ e x = 0 := by
  simp [relativeDensity]

/-- An unchanged field has zero relative action on every domain. -/
theorem relativeAction_self (p : MassiveParameters) (ψ : Covector → ℂ)
    (e : Fin 4 → Covector) (U : Set Covector) : relativeAction p ψ ψ e U = 0 := by
  simp [relativeAction, relativeDensity_self]

/-- When both full densities are genuinely integrable, the relative action
agrees with the difference of their ordinary actions. -/
theorem relativeAction_eq_action_sub_action (p : MassiveParameters)
    (ψ φ : Covector → ℂ) (e : Fin 4 → Covector) (U : Set Covector)
    (hψ : IntegrableOn (fun x => (fieldPairing p ψ ψ e x).re) U)
    (hφ : IntegrableOn (fun x => (fieldPairing p φ φ e x).re) U) :
    relativeAction p ψ φ e U =
      action p φ e (volume.restrict U) - action p ψ e (volume.restrict U) := by
  exact integral_sub hφ hψ

/-- Exact pointwise quadratic expansion of the relative density along an
affine real-parameter complex field variation. -/
theorem relativeDensity_affine (p : MassiveParameters) {ψ η : Covector → ℂ}
    {x : Covector} (hψ : DifferentiableAt ℝ ψ x) (hη : DifferentiableAt ℝ η x)
    (e : Fin 4 → Covector) (t : ℝ) :
    relativeDensity p ψ (fun y => ψ y + t * η y) e x =
      2 * t * (fieldPairing p η ψ e x).re +
        t ^ 2 * (fieldPairing p η η e x).re := by
  unfold relativeDensity
  rw [fieldPairing_variation_re p hψ hη e t]
  ring

/-- Every compact interior affine perturbation has integrable relative
density, even when neither full action density is integrable. -/
theorem integrableOn_relativeDensity_affine (p : MassiveParameters) {U : Set Covector}
    (hU : IsOpen U) {ψ η : Covector → ℂ} (e : Fin 4 → Covector)
    (hψ : ∀ x ∈ U, ContDiffAt ℝ 2 ψ x) (hη : ContDiff ℝ ∞ η)
    (hc : HasCompactSupport η) (hs : tsupport η ⊆ U) (t : ℝ) :
    IntegrableOn (relativeDensity p ψ (fun y => ψ y + t * η y) e) U := by
  have hη1 : ContDiff ℝ 1 η := hη.of_le (by norm_num)
  have hη2 : ContDiff ℝ 2 η := hη.of_le (by norm_num)
  have hcross : IntegrableOn (fun x => (fieldPairing p η ψ e x).re) U :=
    (OpenIntegrationByParts.integrable_fieldPairing p hη1 hψ hc hs e).re
  have htest : IntegrableOn (fun x => (fieldPairing p η η e x).re) U :=
    (FlatIntegrationByParts.integrable_fieldPairing p hη1 hη2 hc e).re.integrableOn
  apply ((hcross.const_mul (2 * t)).add (htest.const_mul (t ^ 2))).congr
  filter_upwards [ae_restrict_mem hU.measurableSet] with x hx
  exact (relativeDensity_affine p ((hψ x hx).differentiableAt (by norm_num))
    (hη.differentiable (by simp) x) e t).symm

/-- The relative action is an exact quadratic polynomial in the perturbation
parameter without any finiteness assumption on the background action. -/
theorem relativeAction_affine (p : MassiveParameters) {U : Set Covector}
    (hU : IsOpen U) {ψ η : Covector → ℂ} (e : Fin 4 → Covector)
    (hψ : ∀ x ∈ U, ContDiffAt ℝ 2 ψ x) (hη : ContDiff ℝ ∞ η)
    (hc : HasCompactSupport η) (hs : tsupport η ⊆ U) (t : ℝ) :
    relativeAction p ψ (fun y => ψ y + t * η y) e U =
      2 * t * (∫ x in U, (fieldPairing p η ψ e x).re) +
        t ^ 2 * action p η e (volume.restrict U) := by
  have hη1 : ContDiff ℝ 1 η := hη.of_le (by norm_num)
  have hη2 : ContDiff ℝ 2 η := hη.of_le (by norm_num)
  have hcross : IntegrableOn (fun x => (fieldPairing p η ψ e x).re) U :=
    (OpenIntegrationByParts.integrable_fieldPairing p hη1 hψ hc hs e).re
  have htest : IntegrableOn (fun x => (fieldPairing p η η e x).re) U :=
    (FlatIntegrationByParts.integrable_fieldPairing p hη1 hη2 hc e).re.integrableOn
  unfold relativeAction action
  calc
    _ = ∫ x in U, 2 * t * (fieldPairing p η ψ e x).re +
        t ^ 2 * (fieldPairing p η η e x).re := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem hU.measurableSet] with x hx
      exact relativeDensity_affine p ((hψ x hx).differentiableAt (by norm_num))
        (hη.differentiable (by simp) x) e t
    _ = _ := by
      rw [integral_add (hcross.const_mul (2 * t)) (htest.const_mul (t ^ 2)),
        integral_const_mul, integral_const_mul]

/-- Differentiating the exact relative-action polynomial gives the genuine
first variation; no interchange of differentiation and integration is used. -/
theorem hasDerivAt_relativeAction_affine (p : MassiveParameters) {U : Set Covector}
    (hU : IsOpen U) {ψ η : Covector → ℂ} (e : Fin 4 → Covector)
    (hψ : ∀ x ∈ U, ContDiffAt ℝ 2 ψ x) (hη : ContDiff ℝ ∞ η)
    (hc : HasCompactSupport η) (hs : tsupport η ⊆ U) :
    HasDerivAt (fun t : ℝ => relativeAction p ψ (fun x => ψ x + t * η x) e U)
      (2 * ∫ x in U, (fieldPairing p η ψ e x).re) 0 := by
  have heq : (fun t : ℝ => relativeAction p ψ (fun x => ψ x + t * η x) e U) =
      (fun t => 2 * t * (∫ x in U, (fieldPairing p η ψ e x).re) +
        t ^ 2 * action p η e (volume.restrict U)) :=
    funext (relativeAction_affine p hU e hψ hη hc hs)
  rw [heq]
  convert ((((hasDerivAt_id (0 : ℝ)).const_mul 2).mul_const
    (∫ x in U, (fieldPairing p η ψ e x).re))).add
    (((hasDerivAt_id (0 : ℝ)).pow 2).mul_const (action p η e (volume.restrict U))) using 1
  · funext t
    rfl
  · norm_num

/-- The actual affine relative-action derivative is the weak KG pairing on
an arbitrary open domain, with only local background C² regularity. -/
theorem hasDerivAt_relativeAction_affine_eq_kg_pairing (p : MassiveParameters)
    {U : Set Covector} (hU : IsOpen U) {ψ η : Covector → ℂ} (e : Fin 4 → Covector)
    (hψ : ∀ x ∈ U, ContDiffAt ℝ 2 ψ x) (hη : ContDiff ℝ ∞ η)
    (hc : HasCompactSupport η) (hs : tsupport η ⊆ U) :
    HasDerivAt (fun t : ℝ => relativeAction p ψ (fun x => ψ x + t * η x) e U)
      (-2 * ∫ x in U, (conj (η x) * kgOperator p ψ e x).re) 0 := by
  have hd := hasDerivAt_relativeAction_affine p hU e hψ hη hc hs
  rw [OpenIntegrationByParts.integral_re_fieldPairing_eq p
    (hη.of_le (by norm_num)) hψ hc hs e] at hd
  convert hd using 1
  ring

end FoliationQM.RelativeAction
