module

public import FoliationQM.StationaryAction
public import FoliationQM.CompactIntegralVariation
public import FoliationQM.SmoothActionDensity

/-!
# Compact smooth variation of the actual quadratic action

Source: v13 `thm:kahler`. Equality of fields outside one compact set also
controls their spatial derivatives. This module applies that support
control to actual derivatives of the integrated flat action.
-/
@[expose] public section

namespace FoliationQM.CompactActionVariation

open ActionVariation PolarSecondDifferential StationaryAction FlatIntegrationByParts
open MeasureTheory
open SmoothActionDensity
open scoped Topology ContDiff ComplexConjugate

/-- Equality outside a closed set gives equality on a neighborhood of each
point outside the set, so actual derivatives agree there as well. -/
theorem eventuallyEq_of_eq_outside {f g : Covector → ℂ} {K : Set Covector}
    (hK : IsClosed K) {x : Covector} (hx : x ∉ K)
    (heq : ∀ y, y ∉ K → f y = g y) : f =ᶠ[𝓝 x] g := by
  filter_upwards [hK.isOpen_compl.mem_nhds hx] with y hy
  exact heq y hy

/-- The literal field pairing depends only on the local field germs. -/
theorem fieldPairing_congr_of_eventuallyEq (p : MassiveParameters)
    {f g f' g' : Covector → ℂ} {x : Covector}
    (hf : f =ᶠ[𝓝 x] f') (hg : g =ᶠ[𝓝 x] g') (e : Fin 4 → Covector) :
    fieldPairing p f g e x = fieldPairing p f' g' e x := by
  simp only [fieldPairing, directionalDerivative, hf.eq_of_nhds, hg.eq_of_nhds,
    hf.fderiv_eq (𝕜 := ℝ), hg.fderiv_eq (𝕜 := ℝ)]

/-- A locally zero first factor has zero polarized density, including its
actual derivative terms. -/
theorem fieldPairing_zero_of_eventuallyEq (p : MassiveParameters)
    {η ψ : Covector → ℂ} {x : Covector} (hη : η =ᶠ[𝓝 x] 0)
    (e : Fin 4 → Covector) : fieldPairing p η ψ e x = 0 := by
  rw [fieldPairing_congr_of_eventuallyEq p hη (Filter.EventuallyEq.refl _ _) e]
  simp [fieldPairing, pairing, kineticPairing, directionalDerivative]

/-- A curve fixed outside a compact region has zero actual parameter
velocity there. The conclusion follows from a derivative of a locally
constant parameter slice, not an independent velocity assumption. -/
theorem parameterDerivative_zero_of_eq_outside {Ψ : ℝ × Covector → ℂ}
    {s : Set ℝ} (hs : IsOpen s) {t : ℝ} (ht : t ∈ s) {K : Set Covector}
    {x : Covector} (hx : x ∉ K) (hΨ : DifferentiableAt ℝ Ψ (t, x))
    (heq : ∀ r ∈ s, ∀ y ∉ K, Ψ (r, y) = Ψ (0, y)) :
    fderiv ℝ Ψ (t, x) (1, 0) = 0 := by
  have hp : HasDerivAt (fun r : ℝ => (r, x)) ((1 : ℝ), (0 : Covector)) t :=
    (hasFDerivAt_prodMk_left (𝕜 := ℝ) t x).hasDerivAt
  have hd := hΨ.hasFDerivAt.comp_hasDerivAt t hp
  have he : (fun r => Ψ (r, x)) =ᶠ[𝓝 t] (fun _ => Ψ (0, x)) := by
    filter_upwards [hs.mem_nhds ht] with r hr
    exact heq r hr x hx
  exact hd.unique ((hasDerivAt_const t (Ψ (0, x))).congr_of_eventuallyEq he)

/-- The real self-density equals its unperturbed value outside the common
compact support of a field variation, including all spatial derivative terms. -/
theorem density_eq_outside (p : MassiveParameters) {Ψ : ℝ × Covector → ℂ}
    {s : Set ℝ} {K : Set Covector} (hK : IsClosed K)
    (heq : ∀ t ∈ s, ∀ x ∉ K, Ψ (t, x) = Ψ (0, x))
    {t : ℝ} (ht : t ∈ s) {x : Covector} (hx : x ∉ K)
    (e : Fin 4 → Covector) :
    (fieldPairing p (slice Ψ t) (slice Ψ t) e x).re =
      (fieldPairing p (slice Ψ 0) (slice Ψ 0) e x).re := by
  have hg : slice Ψ t =ᶠ[𝓝 x] slice Ψ 0 :=
    eventuallyEq_of_eq_outside hK hx (heq t ht)
  rw [fieldPairing_congr_of_eventuallyEq p hg hg e]

/-- Compactly supported smooth field changes have finite action density
throughout the supplied parameter neighborhood whenever the base does. -/
theorem integrable_density_curve (p : MassiveParameters) {Ψ : ℝ × Covector → ℂ}
    {s : Set ℝ} (hzero : (0 : ℝ) ∈ s)
    (hΨ : ∀ t ∈ s, ∀ x, ContDiffAt ℝ ∞ Ψ (t, x))
    {K : Set Covector} (hK : IsCompact K)
    (heq : ∀ t ∈ s, ∀ x ∉ K, Ψ (t, x) = Ψ (0, x))
    (e : Fin 4 → Covector)
    (hbase : Integrable (fun x => (fieldPairing p (slice Ψ 0) (slice Ψ 0) e x).re))
    {t : ℝ} (ht : t ∈ s) :
    Integrable (fun x => (fieldPairing p (slice Ψ t) (slice Ψ t) e x).re) := by
  exact CompactIntegralVariation.integrable_of_eq_outside_compact
    (fun z hz => (continuousAt_density p (hΨ z.1 hz.1 z.2) e).continuousWithinAt)
    hzero hK (fun t ht x hx => density_eq_outside p hK.isClosed heq ht hx e) hbase ht

/-- The actual integrated quadratic action has first derivative twice its
real polarized pairing with the actual curve velocity. Joint smoothness and
one compact support derive the required integrable domination. -/
theorem hasDerivAt_action_curve (p : MassiveParameters) {Ψ : ℝ × Covector → ℂ}
    {s : Set ℝ} (hs : IsOpen s) (hzero : (0 : ℝ) ∈ s)
    (hΨ : ∀ t ∈ s, ∀ x, ContDiffAt ℝ ∞ Ψ (t, x))
    {K : Set Covector} (hK : IsCompact K)
    (heq : ∀ t ∈ s, ∀ x ∉ K, Ψ (t, x) = Ψ (0, x))
    (e : Fin 4 → Covector)
    (hbase : Integrable (fun x => (fieldPairing p (slice Ψ 0) (slice Ψ 0) e x).re)) :
    HasDerivAt (fun t => action p (slice Ψ t) e volume)
      (2 * ∫ x, (fieldPairing p (velocity Ψ 0) (slice Ψ 0) e x).re) 0 := by
  have hvel : ∀ t ∈ s, ∀ x ∉ K, velocity Ψ t x = 0 := by
    intro t ht x hx
    exact parameterDerivative_zero_of_eq_outside hs ht hx
      ((hΨ t ht x).differentiableAt (by simp)) heq
  have hsupp : ∀ t ∈ s, ∀ x ∉ K,
      2 * (fieldPairing p (velocity Ψ t) (slice Ψ t) e x).re = 0 := by
    intro t ht x hx
    have hv : velocity Ψ t =ᶠ[𝓝 x] 0 :=
      eventuallyEq_of_eq_outside hK.isClosed hx (hvel t ht)
    rw [fieldPairing_zero_of_eventuallyEq p hv e]
    simp
  have hd := CompactIntegralVariation.hasDerivAt_integral_of_compact_support
    (hs.mem_nhds hzero)
    (fun z hz => (continuousAt_density p (hΨ z.1 hz.1 z.2) e).continuousWithinAt)
    (fun z hz => (continuousAt_densityDerivative p (hΨ z.1 hz.1 z.2) e).continuousWithinAt)
    hK hsupp (fun t ht x => hasDerivAt_density p (hΨ t ht x) e) hbase
  simpa only [action, integral_const_mul] using hd.2

/-- Integration by parts gives the actual first variation for any jointly
smooth compact field curve, not only affine complex curves. -/
theorem hasDerivAt_action_curve_eq_kg (p : MassiveParameters) {Ψ : ℝ × Covector → ℂ}
    {s : Set ℝ} (hs : IsOpen s) (hzero : (0 : ℝ) ∈ s)
    (hΨ : ∀ t ∈ s, ∀ x, ContDiffAt ℝ ∞ Ψ (t, x))
    {K : Set Covector} (hK : IsCompact K)
    (heq : ∀ t ∈ s, ∀ x ∉ K, Ψ (t, x) = Ψ (0, x))
    (e : Fin 4 → Covector)
    (hbase : Integrable (fun x => (fieldPairing p (slice Ψ 0) (slice Ψ 0) e x).re)) :
    HasDerivAt (fun t => action p (slice Ψ t) e volume)
      (-2 * ∫ x, (conj (velocity Ψ 0 x) * kgOperator p (slice Ψ 0) e x).re) 0 := by
  have hslice : ContDiff ℝ ∞ (slice Ψ 0) :=
    contDiff_iff_contDiffAt.mpr (fun x => contDiffAt_slice (hΨ 0 hzero x))
  have hvel : ContDiff ℝ ∞ (velocity Ψ 0) :=
    contDiff_iff_contDiffAt.mpr (fun x => contDiffAt_velocity (hΨ 0 hzero x))
  have hc : HasCompactSupport (velocity Ψ 0) := by
    apply HasCompactSupport.intro hK
    intro x hx
    exact parameterDerivative_zero_of_eq_outside hs hzero hx
      ((hΨ 0 hzero x).differentiableAt (by simp)) heq
  have hd := hasDerivAt_action_curve p hs hzero hΨ hK heq e hbase
  rw [integral_re_fieldPairing_eq p (hvel.of_le (by norm_num))
    (hslice.of_le (by norm_num)) hc e] at hd
  convert hd using 1
  ring

end FoliationQM.CompactActionVariation
