module

public import FoliationQM.CompactActionVariation
public import FoliationQM.OpenCompactIntegralVariation
public import FoliationQM.OpenIntegrationByParts
public import FoliationQM.OpenPolarVariations

/-!
# Compact smooth action curves on an open domain

Source: v13 `thm:kahler`. A field curve is jointly smooth only inside the
open spacetime domain and is fixed outside a compact subset of that domain.
Its actual action derivative uses restricted Lebesgue volume. Compact interior
support removes boundary terms without boundary regularity assumptions.
The background field may be arbitrary outside the domain.
-/
@[expose] public section

namespace FoliationQM.OpenActionVariation

open ActionVariation PolarSecondDifferential StationaryAction FlatIntegrationByParts
open MeasureTheory SmoothActionDensity CompactActionVariation
open scoped Topology ContDiff ComplexConjugate

/-- A parameter curve fixed outside the common compact support has zero total
parameter-direction derivative there, including points where the background
is not differentiable. This support fact needs no outside-domain regularity. -/
theorem parameterDerivative_zero_of_eq_outside {Ψ : ℝ × Covector → ℂ}
    {s : Set ℝ} (hs : IsOpen s) {t : ℝ} (ht : t ∈ s) {K : Set Covector}
    {x : Covector} (hx : x ∉ K)
    (heq : ∀ r ∈ s, ∀ y ∉ K, Ψ (r, y) = Ψ (0, y)) :
    velocity Ψ t x = 0 := by
  by_cases hd : DifferentiableAt ℝ Ψ (t, x)
  · exact CompactActionVariation.parameterDerivative_zero_of_eq_outside hs ht hx hd heq
  · simp only [velocity, fderiv_zero_of_not_differentiableAt hd, zero_apply]

/-- A compact interior field change preserves integrability of the actual
action density throughout its parameter neighborhood. -/
theorem integrable_density_curve (p : MassiveParameters) {Ψ : ℝ × Covector → ℂ}
    {U : Set Covector} (hU : IsOpen U) {s : Set ℝ} (hzero : (0 : ℝ) ∈ s)
    (hΨ : ∀ t ∈ s, ∀ x ∈ U, ContDiffAt ℝ ∞ Ψ (t, x))
    {K : Set Covector} (hK : IsCompact K) (hKU : K ⊆ U)
    (heq : ∀ t ∈ s, ∀ x ∉ K, Ψ (t, x) = Ψ (0, x))
    (e : Fin 4 → Covector)
    (hbase : IntegrableOn
      (fun x => (fieldPairing p (slice Ψ 0) (slice Ψ 0) e x).re) U)
    {t : ℝ} (ht : t ∈ s) :
    IntegrableOn (fun x => (fieldPairing p (slice Ψ t) (slice Ψ t) e x).re) U := by
  exact OpenCompactIntegralVariation.integrable_of_eq_outside_compact hU
    (fun z hz => (continuousAt_density p (hΨ z.1 hz.1 z.2 hz.2) e).continuousWithinAt)
    hzero hK hKU
    (fun t ht x _ hx => density_eq_outside p hK.isClosed heq ht hx e) hbase ht

/-- The restricted action has actual first derivative twice its polarized
pairing with the actual velocity. Domination follows from compactness inside
the open domain, with no smoothness hypothesis outside that domain. -/
theorem hasDerivAt_action_curve (p : MassiveParameters) {Ψ : ℝ × Covector → ℂ}
    {U : Set Covector} (hU : IsOpen U)
    {s : Set ℝ} (hs : IsOpen s) (hzero : (0 : ℝ) ∈ s)
    (hΨ : ∀ t ∈ s, ∀ x ∈ U, ContDiffAt ℝ ∞ Ψ (t, x))
    {K : Set Covector} (hK : IsCompact K) (hKU : K ⊆ U)
    (heq : ∀ t ∈ s, ∀ x ∉ K, Ψ (t, x) = Ψ (0, x))
    (e : Fin 4 → Covector)
    (hbase : IntegrableOn
      (fun x => (fieldPairing p (slice Ψ 0) (slice Ψ 0) e x).re) U) :
    HasDerivAt (fun t => action p (slice Ψ t) e (volume.restrict U))
      (2 * ∫ x in U, (fieldPairing p (velocity Ψ 0) (slice Ψ 0) e x).re) 0 := by
  have hvel : ∀ t ∈ s, ∀ x ∉ K, velocity Ψ t x = 0 :=
    fun _ ht _ hx => parameterDerivative_zero_of_eq_outside hs ht hx heq
  have hsupp : ∀ t ∈ s, ∀ x ∈ U, x ∉ K →
      2 * (fieldPairing p (velocity Ψ t) (slice Ψ t) e x).re = 0 := by
    intro t ht x _ hx
    have hv : velocity Ψ t =ᶠ[𝓝 x] 0 :=
      eventuallyEq_of_eq_outside hK.isClosed hx (hvel t ht)
    rw [fieldPairing_zero_of_eventuallyEq p hv e]
    simp
  have hd := OpenCompactIntegralVariation.hasDerivAt_integral_of_compact_support hU
    (hs.mem_nhds hzero)
    (fun z hz => (continuousAt_density p (hΨ z.1 hz.1 z.2 hz.2) e).continuousWithinAt)
    (fun z hz =>
      (continuousAt_densityDerivative p (hΨ z.1 hz.1 z.2 hz.2) e).continuousWithinAt)
    hK hKU hsupp (fun t ht x hx => hasDerivAt_density p (hΨ t ht x hx) e) hbase
  simpa only [action, integral_const_mul] using hd.2

/-- Compact interior tests turn the restricted action's actual derivative
into the weak Klein--Gordon pairing. The velocity is globally smooth because
it is locally smooth inside the domain and locally zero outside its support. -/
theorem hasDerivAt_action_curve_eq_kg (p : MassiveParameters) {Ψ : ℝ × Covector → ℂ}
    {U : Set Covector} (hU : IsOpen U)
    {s : Set ℝ} (hs : IsOpen s) (hzero : (0 : ℝ) ∈ s)
    (hΨ : ∀ t ∈ s, ∀ x ∈ U, ContDiffAt ℝ ∞ Ψ (t, x))
    {K : Set Covector} (hK : IsCompact K) (hKU : K ⊆ U)
    (heq : ∀ t ∈ s, ∀ x ∉ K, Ψ (t, x) = Ψ (0, x))
    (e : Fin 4 → Covector)
    (hbase : IntegrableOn
      (fun x => (fieldPairing p (slice Ψ 0) (slice Ψ 0) e x).re) U) :
    HasDerivAt (fun t => action p (slice Ψ t) e (volume.restrict U))
      (-2 * ∫ x in U, (conj (velocity Ψ 0 x) * kgOperator p (slice Ψ 0) e x).re) 0 := by
  have hslice : ∀ x ∈ U, ContDiffAt ℝ ∞ (slice Ψ 0) x :=
    fun x hx => contDiffAt_slice (hΨ 0 hzero x hx)
  have hsupp : tsupport (velocity Ψ 0) ⊆ K := by
    apply closure_minimal _ hK.isClosed
    intro x hx
    by_contra hn
    exact hx (parameterDerivative_zero_of_eq_outside hs hzero hn heq)
  have hvel : ContDiff ℝ ∞ (velocity Ψ 0) :=
    OpenPolarVariations.contDiff_of_tsupport_subset
      (fun x hx => contDiffAt_velocity (hΨ 0 hzero x hx)) (hsupp.trans hKU)
  have hc : HasCompactSupport (velocity Ψ 0) :=
    hK.of_isClosed_subset (isClosed_tsupport _) hsupp
  have hd := hasDerivAt_action_curve p hU hs hzero hΨ hK hKU heq e hbase
  rw [OpenIntegrationByParts.integral_re_fieldPairing_eq p (hvel.of_le (by simp))
    (fun x hx => (hslice x hx).of_le (by simp)) hc (hsupp.trans hKU) e] at hd
  convert hd using 1
  ring

end FoliationQM.OpenActionVariation
