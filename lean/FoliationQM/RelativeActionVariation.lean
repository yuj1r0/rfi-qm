module

public import FoliationQM.RelativeAction
public import FoliationQM.OpenActionVariation

/-!
# Relative action along compact interior smooth field curves

Source: v13 `thm:kahler`, local analytic support for action variation.
The relative action integrates the difference of two action densities.
Joint smoothness is required only inside the open domain and the field curve
is fixed outside one compact subset of that domain. The density difference
and its actual derivative are integrable without requiring either full
background or full perturbed action to be integrable.
-/
@[expose] public section

namespace FoliationQM.RelativeActionVariation

open ActionVariation PolarSecondDifferential StationaryAction FlatIntegrationByParts
open MeasureTheory SmoothActionDensity CompactActionVariation RelativeAction
open scoped Topology ContDiff ComplexConjugate

/-- The relative action of a change supported in a compact set equals the
integral of its density difference over that compact set. This equality
does not require either full action to exist as a finite integral. -/
theorem relativeAction_curve_eq_integral_compact (p : MassiveParameters)
    {Ψ : ℝ × Covector → ℂ} {s : Set ℝ} {K : Set Covector}
    (hK : IsCompact K)
    (heq : ∀ t ∈ s, ∀ x ∉ K, Ψ (t, x) = Ψ (0, x))
    {t : ℝ} (ht : t ∈ s) (e : Fin 4 → Covector)
    {U : Set Covector} (hU : MeasurableSet U) (hKU : K ⊆ U) :
    relativeAction p (slice Ψ 0) (slice Ψ t) e U =
      ∫ x in K, relativeDensity p (slice Ψ 0) (slice Ψ t) e x := by
  apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hU hKU
  intro x hx
  simp only [relativeDensity, density_eq_outside p hK.isClosed heq ht hx.2 e, sub_self]

/-- The relative action of a compact field change is independent of the
measurable integration region as long as both regions contain its support. -/
theorem relativeAction_curve_eq_of_support_subset (p : MassiveParameters)
    {Ψ : ℝ × Covector → ℂ} {s : Set ℝ} {K : Set Covector}
    (hK : IsCompact K)
    (heq : ∀ t ∈ s, ∀ x ∉ K, Ψ (t, x) = Ψ (0, x))
    {t : ℝ} (ht : t ∈ s) (e : Fin 4 → Covector)
    {U V : Set Covector} (hU : MeasurableSet U) (hV : MeasurableSet V)
    (hKU : K ⊆ U) (hKV : K ⊆ V) :
    relativeAction p (slice Ψ 0) (slice Ψ t) e U =
      relativeAction p (slice Ψ 0) (slice Ψ t) e V := by
  rw [relativeAction_curve_eq_integral_compact p hK heq ht e hU hKU,
    relativeAction_curve_eq_integral_compact p hK heq ht e hV hKV]

/-- Joint continuity of the relative density requires smoothness only on the
parameter neighborhood times the open spacetime region. -/
theorem continuousOn_relativeDensity_curve (p : MassiveParameters)
    {Ψ : ℝ × Covector → ℂ} {U : Set Covector} {s : Set ℝ}
    (hzero : (0 : ℝ) ∈ s)
    (hΨ : ∀ t ∈ s, ∀ x ∈ U, ContDiffAt ℝ ∞ Ψ (t, x))
    (e : Fin 4 → Covector) :
    ContinuousOn (fun z : ℝ × Covector =>
      relativeDensity p (slice Ψ 0) (slice Ψ z.1) e z.2) (s ×ˢ U) := by
  intro z hz
  have hbase : ContinuousAt (fun w : ℝ × Covector =>
      (fieldPairing p (slice Ψ 0) (slice Ψ 0) e w.2).re) z :=
    (continuousAt_density p (hΨ 0 hzero z.2 hz.2) e).comp
      (f := fun w : ℝ × Covector => ((0 : ℝ), w.2)) (x := z)
      (show ContinuousAt (fun w : ℝ × Covector => ((0 : ℝ), w.2)) z from
        continuousAt_const.prodMk continuousAt_snd)
  exact ((continuousAt_density p (hΨ z.1 hz.1 z.2 hz.2) e).sub hbase).continuousWithinAt

/-- A compact interior change has an integrable relative density throughout
the parameter neighborhood, even when its background action diverges. -/
theorem integrableOn_relativeDensity_curve (p : MassiveParameters)
    {Ψ : ℝ × Covector → ℂ} {U : Set Covector} (hU : IsOpen U)
    {s : Set ℝ} (hzero : (0 : ℝ) ∈ s)
    (hΨ : ∀ t ∈ s, ∀ x ∈ U, ContDiffAt ℝ ∞ Ψ (t, x))
    {K : Set Covector} (hK : IsCompact K) (hKU : K ⊆ U)
    (heq : ∀ t ∈ s, ∀ x ∉ K, Ψ (t, x) = Ψ (0, x))
    (e : Fin 4 → Covector) {t : ℝ} (ht : t ∈ s) :
    IntegrableOn (relativeDensity p (slice Ψ 0) (slice Ψ t) e) U := by
  apply OpenCompactIntegralVariation.integrable_of_eq_outside_compact hU
    (F := fun t x => relativeDensity p (slice Ψ 0) (slice Ψ t) e x)
    (continuousOn_relativeDensity_curve p hzero hΨ e) hzero hK hKU
    (fun t ht x _ hx => ?_) (by simp [relativeDensity]) ht
  simp only [relativeDensity, density_eq_outside p hK.isClosed heq ht hx e, sub_self]

/-- The actual relative-action derivative is twice the polarized pairing of
the initial velocity with the initial field. Compactness derives domination,
while the initial relative density is identically zero. -/
theorem hasDerivAt_relativeAction_curve (p : MassiveParameters)
    {Ψ : ℝ × Covector → ℂ} {U : Set Covector} (hU : IsOpen U)
    {s : Set ℝ} (hs : IsOpen s) (hzero : (0 : ℝ) ∈ s)
    (hΨ : ∀ t ∈ s, ∀ x ∈ U, ContDiffAt ℝ ∞ Ψ (t, x))
    {K : Set Covector} (hK : IsCompact K) (hKU : K ⊆ U)
    (heq : ∀ t ∈ s, ∀ x ∉ K, Ψ (t, x) = Ψ (0, x))
    (e : Fin 4 → Covector) :
    HasDerivAt (fun t => relativeAction p (slice Ψ 0) (slice Ψ t) e U)
      (2 * ∫ x in U, (fieldPairing p (velocity Ψ 0) (slice Ψ 0) e x).re) 0 := by
  have hvel : ∀ t ∈ s, ∀ x ∉ K, velocity Ψ t x = 0 :=
    fun _ ht _ hx => OpenActionVariation.parameterDerivative_zero_of_eq_outside hs ht hx heq
  have hsupp : ∀ t ∈ s, ∀ x ∈ U, x ∉ K →
      2 * (fieldPairing p (velocity Ψ t) (slice Ψ t) e x).re = 0 := by
    intro t ht x _ hx
    have hv : velocity Ψ t =ᶠ[𝓝 x] 0 :=
      eventuallyEq_of_eq_outside hK.isClosed hx (hvel t ht)
    rw [fieldPairing_zero_of_eventuallyEq p hv e]
    simp
  have hd := OpenCompactIntegralVariation.hasDerivAt_integral_of_compact_support hU
    (F := fun t x => relativeDensity p (slice Ψ 0) (slice Ψ t) e x)
    (hs.mem_nhds hzero) (continuousOn_relativeDensity_curve p hzero hΨ e)
    (fun z hz =>
      (continuousAt_densityDerivative p (hΨ z.1 hz.1 z.2 hz.2) e).continuousWithinAt)
    hK hKU hsupp
    (fun t ht x hx => (hasDerivAt_density p (hΨ t ht x hx) e).sub_const
      ((fieldPairing p (slice Ψ 0) (slice Ψ 0) e x).re))
    (by simp [relativeDensity])
  simpa only [relativeAction, integral_const_mul] using hd.2

/-- Integration by parts turns the actual relative-action derivative into
the weak Klein--Gordon pairing without any background integrability premise. -/
theorem hasDerivAt_relativeAction_curve_eq_kg (p : MassiveParameters)
    {Ψ : ℝ × Covector → ℂ} {U : Set Covector} (hU : IsOpen U)
    {s : Set ℝ} (hs : IsOpen s) (hzero : (0 : ℝ) ∈ s)
    (hΨ : ∀ t ∈ s, ∀ x ∈ U, ContDiffAt ℝ ∞ Ψ (t, x))
    {K : Set Covector} (hK : IsCompact K) (hKU : K ⊆ U)
    (heq : ∀ t ∈ s, ∀ x ∉ K, Ψ (t, x) = Ψ (0, x))
    (e : Fin 4 → Covector) :
    HasDerivAt (fun t => relativeAction p (slice Ψ 0) (slice Ψ t) e U)
      (-2 * ∫ x in U, (conj (velocity Ψ 0 x) * kgOperator p (slice Ψ 0) e x).re) 0 := by
  have hslice : ∀ x ∈ U, ContDiffAt ℝ ∞ (slice Ψ 0) x :=
    fun x hx => contDiffAt_slice (hΨ 0 hzero x hx)
  have hsupp : tsupport (velocity Ψ 0) ⊆ K := by
    apply closure_minimal _ hK.isClosed
    intro x hx
    by_contra hn
    exact hx (OpenActionVariation.parameterDerivative_zero_of_eq_outside hs hzero hn heq)
  have hvel : ContDiff ℝ ∞ (velocity Ψ 0) :=
    OpenPolarVariations.contDiff_of_tsupport_subset
      (fun x hx => contDiffAt_velocity (hΨ 0 hzero x hx)) (hsupp.trans hKU)
  have hc : HasCompactSupport (velocity Ψ 0) :=
    hK.of_isClosed_subset (isClosed_tsupport _) hsupp
  have hd := hasDerivAt_relativeAction_curve p hU hs hzero hΨ hK hKU heq e
  rw [OpenIntegrationByParts.integral_re_fieldPairing_eq p (hvel.of_le (by simp))
    (fun x hx => (hslice x hx).of_le (by simp)) hc (hsupp.trans hKU) e] at hd
  convert hd using 1
  ring

/-- Equal initial fields and actual initial velocities give equal actual
relative-action derivatives for two compact interior smooth curves. -/
theorem deriv_relativeAction_curve_eq_of_same_initial_data (p : MassiveParameters)
    {Ψ Χ : ℝ × Covector → ℂ} {U : Set Covector} (hU : IsOpen U)
    {s r : Set ℝ} (hs : IsOpen s) (hszero : (0 : ℝ) ∈ s)
    (hr : IsOpen r) (hrzero : (0 : ℝ) ∈ r)
    (hΨ : ∀ t ∈ s, ∀ x ∈ U, ContDiffAt ℝ ∞ Ψ (t, x))
    (hΧ : ∀ t ∈ r, ∀ x ∈ U, ContDiffAt ℝ ∞ Χ (t, x))
    {K L : Set Covector} (hK : IsCompact K) (hKU : K ⊆ U)
    (hL : IsCompact L) (hLU : L ⊆ U)
    (hΨoutside : ∀ t ∈ s, ∀ x ∉ K, Ψ (t, x) = Ψ (0, x))
    (hΧoutside : ∀ t ∈ r, ∀ x ∉ L, Χ (t, x) = Χ (0, x))
    (e : Fin 4 → Covector)
    (hinitial : slice Ψ 0 = slice Χ 0)
    (hvelocity : velocity Ψ 0 = velocity Χ 0) :
    deriv (fun t => relativeAction p (slice Ψ 0) (slice Ψ t) e U) 0 =
      deriv (fun t => relativeAction p (slice Χ 0) (slice Χ t) e U) 0 := by
  rw [(hasDerivAt_relativeAction_curve p hU hs hszero hΨ hK hKU hΨoutside e).deriv,
    (hasDerivAt_relativeAction_curve p hU hr hrzero hΧ hL hLU hΧoutside e).deriv,
    hinitial, hvelocity]

/-- A pointwise Klein--Gordon field has zero actual relative-action derivative
along every jointly smooth compact interior curve through that field. -/
theorem hasDerivAt_relativeAction_curve_zero_of_kgOperator (p : MassiveParameters)
    {Ψ : ℝ × Covector → ℂ} {U : Set Covector} (hU : IsOpen U)
    {s : Set ℝ} (hs : IsOpen s) (hzero : (0 : ℝ) ∈ s)
    (hΨ : ∀ t ∈ s, ∀ x ∈ U, ContDiffAt ℝ ∞ Ψ (t, x))
    {K : Set Covector} (hK : IsCompact K) (hKU : K ⊆ U)
    (heq : ∀ t ∈ s, ∀ x ∉ K, Ψ (t, x) = Ψ (0, x))
    (e : Fin 4 → Covector)
    (hkg : ∀ x ∈ U, kgOperator p (slice Ψ 0) e x = 0) :
    HasDerivAt (fun t => relativeAction p (slice Ψ 0) (slice Ψ t) e U) 0 0 := by
  have hd := hasDerivAt_relativeAction_curve_eq_kg p hU hs hzero hΨ hK hKU heq e
  have hz : (∫ x in U, (conj (velocity Ψ 0 x) * kgOperator p (slice Ψ 0) e x).re) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [ae_restrict_mem hU.measurableSet] with x hx
    simp only [hkg x hx, mul_zero, Complex.zero_re, Pi.zero_apply]
  simpa only [hz, mul_zero] using hd

end FoliationQM.RelativeActionVariation
