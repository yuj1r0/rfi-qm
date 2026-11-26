module

public import FoliationQM.CompactActionVariation

/-!
# Independence of the variation curve and stationarity

Source: v13 `thm:kahler`. The actual integrated first variation depends only
on the initial field and actual initial velocity. Existing stationarity under
smooth compact affine complex variations therefore controls arbitrary jointly
smooth field curves fixed outside one compact spatial set near parameter zero.
These are flat whole-space finite-action results.
-/
@[expose] public section

namespace FoliationQM.SmoothCurveStationarity

open ActionVariation SmoothActionDensity CompactActionVariation
open StationaryAction FlatIntegrationByParts MeasureTheory
open scoped ContDiff

/-- Two jointly smooth compact field curves with the same initial field and
actual initial velocity have the same actual action derivative. Their compact
supports and parameter neighborhoods may differ. -/
theorem deriv_action_curve_eq_of_same_initial_data (p : MassiveParameters)
    {Ψ Χ : ℝ × Covector → ℂ} {s r : Set ℝ}
    (hs : IsOpen s) (hszero : (0 : ℝ) ∈ s)
    (hr : IsOpen r) (hrzero : (0 : ℝ) ∈ r)
    (hΨ : ∀ t ∈ s, ∀ x, ContDiffAt ℝ ∞ Ψ (t, x))
    (hΧ : ∀ t ∈ r, ∀ x, ContDiffAt ℝ ∞ Χ (t, x))
    {K L : Set Covector} (hK : IsCompact K) (hL : IsCompact L)
    (hΨoutside : ∀ t ∈ s, ∀ x ∉ K, Ψ (t, x) = Ψ (0, x))
    (hΧoutside : ∀ t ∈ r, ∀ x ∉ L, Χ (t, x) = Χ (0, x))
    (e : Fin 4 → Covector)
    (hbase : Integrable (fun x => (fieldPairing p (slice Ψ 0) (slice Ψ 0) e x).re))
    (hinitial : slice Ψ 0 = slice Χ 0)
    (hvelocity : velocity Ψ 0 = velocity Χ 0) :
    deriv (fun t => action p (slice Ψ t) e volume) 0 =
      deriv (fun t => action p (slice Χ t) e volume) 0 := by
  have hbaseΧ : Integrable
      (fun x => (fieldPairing p (slice Χ 0) (slice Χ 0) e x).re) := by
    simpa only [← hinitial] using hbase
  rw [(hasDerivAt_action_curve p hs hszero hΨ hK hΨoutside e hbase).deriv,
    (hasDerivAt_action_curve p hr hrzero hΧ hL hΧoutside e hbaseΧ).deriv,
    hinitial, hvelocity]

/-- Stationarity under smooth compact affine variations gives zero actual
action derivative along every admissible smooth compact field curve. -/
theorem hasDerivAt_action_curve_zero_of_stationary (p : MassiveParameters)
    {Ψ : ℝ × Covector → ℂ} {s : Set ℝ} (hs : IsOpen s) (hzero : (0 : ℝ) ∈ s)
    (hΨ : ∀ t ∈ s, ∀ x, ContDiffAt ℝ ∞ Ψ (t, x))
    {K : Set Covector} (hK : IsCompact K)
    (heq : ∀ t ∈ s, ∀ x ∉ K, Ψ (t, x) = Ψ (0, x))
    (e : Fin 4 → Covector) (hstationary : Stationary p (slice Ψ 0) e) :
    HasDerivAt (fun t => action p (slice Ψ t) e volume) 0 0 := by
  have hslice : ContDiff ℝ ∞ (slice Ψ 0) :=
    contDiff_iff_contDiffAt.mpr (fun x => contDiffAt_slice (hΨ 0 hzero x))
  have hkg := (stationary_iff_kgOperator p e (hslice.of_le (by simp)) hstationary.1).mp
    hstationary
  have hd := hasDerivAt_action_curve_eq_kg p hs hzero hΨ hK heq e hstationary.1
  simpa only [hkg, mul_zero, Complex.zero_re, integral_zero] using hd

end FoliationQM.SmoothCurveStationarity
