module

public import FoliationQM.GaussianNormalSpectralSign
public import Mathlib.Topology.Order.IntermediateValue

/-!
# Temporal current reversal on the real Gaussian initial slice

For the positive-frequency packet of mass-shell parameter μ, the real
positive initial amplitude makes its temporal current a strictly positive
factor times the normal coefficient. Below the necessary width from the
three-frequency test, the current is positive near the center and negative
on an open set of positive volume. Along any straight segment from the
center to that set, the current passes through zero while the field remains
nonzero. This concerns the whole-slice future orientation used by the
free-Gaussian clause at v13 line 767.
-/

@[expose] public section
noncomputable section

namespace FoliationQM.GaussianPacketCurrentSign

open Filter Set LorentzCoordinates OsmoticSliceFields MeasureTheory
open GaussianPositiveFrequencyPacket GaussianNormalSpectralSign
open scoped Topology

/-- The actual temporal component of the scalar current, restricted to initial laboratory time. -/
def temporal (p : MassiveParameters) (μ σ : ℝ) (y : Spatial) : ℝ :=
  ScalarPhaseCurrent.current p (packet μ σ) (slicePoint 0 y) 0

/-- The temporal current equals (ℏ/m) times the real Gaussian amplitude and its normal coefficient. -/
theorem temporal_eq (p : MassiveParameters) (μ : ℝ) {σ : ℝ} (hσ : 0 < σ) (y : Spatial) :
    temporal p μ σ y = (p.hbar / p.m) * GaussianCauchySlice.amplitude σ y * normalCoefficient μ σ y :=
  GaussianNormalOrientation.current_normal p (initial_value μ hσ y) (initial_normal μ hσ y)

/-- Positive, negative and zero temporal currents correspond respectively to the three signs
of the actual normal coefficient. -/
theorem temporal_sign (p : MassiveParameters) (μ : ℝ) {σ : ℝ} (hσ : 0 < σ) (y : Spatial) :
    (0 < temporal p μ σ y ↔ 0 < normalCoefficient μ σ y) ∧
    (temporal p μ σ y < 0 ↔ normalCoefficient μ σ y < 0) ∧
    (temporal p μ σ y = 0 ↔ normalCoefficient μ σ y = 0) :=
  GaussianNormalOrientation.current_normal_sign p (GaussianCauchySlice.amplitude_pos σ y)
    (initial_value μ hσ y) (initial_normal μ hσ y)

/-- For positive mass and width, the actual temporal current is strictly positive in
a neighborhood of the packet center. -/
theorem eventually_future (p : MassiveParameters) {μ σ : ℝ} (hμ : 0 < μ) (hσ : 0 < σ) :
    ∀ᶠ y in 𝓝 (0 : Spatial), 0 < temporal p μ σ y :=
  (eventually_normal_pos hμ hσ).mono fun y hy => (temporal_sign p μ hσ y).1.mpr hy

private theorem past_set_eq (p : MassiveParameters) (μ : ℝ) {σ : ℝ} (hσ : 0 < σ) :
    {y : Spatial | temporal p μ σ y < 0} = {y | normalCoefficient μ σ y < 0} :=
  Set.ext fun y => (temporal_sign p μ hσ y).2.1

/-- The negative temporal current occupies an open region of the initial spatial slice. -/
theorem isOpen_past (p : MassiveParameters) (μ : ℝ) {σ : ℝ} (hσ : 0 < σ) :
    IsOpen {y : Spatial | temporal p μ σ y < 0} := by
  rw [past_set_eq p μ hσ]
  exact isOpen_lt (smooth_normalCoefficient μ hσ).continuous continuous_const

/-- At widths with σ²μ² below (1+√2)/2 the past temporal component occurs on a
set of positive volume for the actual smooth positive-frequency packet. -/
theorem past_volume_below_width (p : MassiveParameters) {μ σ : ℝ} (hμ : 0 < μ) (hσ : 0 < σ)
    (hnarrow : σ^2 * μ^2 < (1 + Real.sqrt 2) / 2) :
    0 < volume {y : Spatial | temporal p μ σ y < 0} := by
  rw [past_set_eq p μ hσ]
  exact negative_volume_below_width hμ hσ hnarrow

/-- The explicit three-frequency witness certifies positive volume of the past-current region
when the spatial width is exactly one reduced Compton length. -/
theorem past_volume_at_compton (p : MassiveParameters) {μ σ : ℝ} (hμ : 0 < μ) (hσ : 0 < σ)
    (hσμ : σ * μ = 1) : 0 < volume {y : Spatial | temporal p μ σ y < 0} := by
  rw [past_set_eq p μ hσ]
  exact negative_volume_at_compton hμ hσ hσμ

/-- The actual wave is nonzero everywhere on the initial slice, even at a point where
its current changes sign. -/
theorem initial_wave_ne_zero (μ : ℝ) {σ : ℝ} (hσ : 0 < σ) (y : Spatial) :
    packet μ σ (slicePoint 0 y) ≠ 0 := by
  rw [initial_value μ hσ y]
  exact_mod_cast (GaussianCauchySlice.amplitude_pos σ y).ne'

private theorem continuous_temporal_current (p : MassiveParameters) (μ : ℝ) {σ : ℝ} (hσ : 0 < σ) :
    Continuous (fun x => ScalarPhaseCurrent.current p (packet μ σ) x 0) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  exact continuousAt_pi.mp (ScalarPhaseCurrent.continuousAt_current p
    ((smooth_packet μ hσ).contDiffAt.of_le (by simp))) 0

/-- In spacetime, points carrying a nonzero wave and strictly negative temporal current
form an open set. -/
theorem isOpen_spacetime_past (p : MassiveParameters) (μ : ℝ) {σ : ℝ} (hσ : 0 < σ) :
    IsOpen {x : Covector | ScalarPhaseCurrent.current p (packet μ σ) x 0 < 0 ∧ packet μ σ x ≠ 0} :=
  (isOpen_lt (continuous_temporal_current p μ hσ) continuous_const).inter
    (isOpen_ne_fun (smooth_packet μ hσ).continuous continuous_const)

/-- A past-current point on the initial slice persists as a nonzero wave with strictly
negative temporal current throughout a spacetime neighborhood. -/
theorem eventually_past_spacetime (p : MassiveParameters) {μ σ : ℝ} (hσ : 0 < σ)
    {y : Spatial} (hy : temporal p μ σ y < 0) :
    ∀ᶠ x in 𝓝 (slicePoint 0 y), ScalarPhaseCurrent.current p (packet μ σ) x 0 < 0 ∧ packet μ σ x ≠ 0 :=
  (isOpen_spacetime_past p μ hσ).mem_nhds ⟨hy, initial_wave_ne_zero μ hσ y⟩

/-- Near the initial center, the strictly positive temporal component and nonzero wave
also persist in the full spacetime topology. -/
theorem eventually_future_spacetime (p : MassiveParameters) {μ σ : ℝ} (hμ : 0 < μ) (hσ : 0 < σ) :
    ∀ᶠ x in 𝓝 (slicePoint 0 0), 0 < ScalarPhaseCurrent.current p (packet μ σ) x 0 ∧ packet μ σ x ≠ 0 := by
  have hpos := (temporal_sign p μ hσ 0).1.mpr (normal_center_pos hμ hσ)
  exact ((continuous_temporal_current p μ hσ).continuousAt.eventually (Ioi_mem_nhds hpos)).and
    ((smooth_packet μ hσ).continuous.continuousAt.eventually_ne (initial_wave_ne_zero μ hσ 0))

/-- Each segment from the packet center to a point with past temporal current contains
an interior zero of the temporal current at which the wave is nonzero. -/
theorem zero_on_segment (p : MassiveParameters) {μ σ : ℝ} (hμ : 0 < μ) (hσ : 0 < σ)
    {y : Spatial} (hy : temporal p μ σ y < 0) :
    ∃ t ∈ Ioo (0 : ℝ) 1, temporal p μ σ (t • y) = 0 ∧ packet μ σ (slicePoint 0 (t • y)) ≠ 0 := by
  let f := fun t : ℝ => normalCoefficient μ σ (t • y)
  have hc : Continuous f := (smooth_normalCoefficient μ hσ).continuous.comp
    (continuous_id.smul continuous_const)
  have h1 : f 1 < 0 := by simpa [f] using (temporal_sign p μ hσ y).2.1.mp hy
  have h0 : 0 < f 0 := by simpa [f] using normal_center_pos hμ hσ
  obtain ⟨t, ht, hz⟩ := intermediate_value_Ioo' (zero_le_one : (0 : ℝ) ≤ 1) hc.continuousOn
    (show (0 : ℝ) ∈ Ioo (f 1) (f 0) from ⟨h1,h0⟩)
  exact ⟨t, ht, (temporal_sign p μ hσ (t • y)).2.2.mpr hz, initial_wave_ne_zero μ hσ (t • y)⟩

/-- Below the necessary width, some spatial ray has a negative temporal current at
one point and a nonnodal zero of that current strictly between it and the center. -/
theorem exists_past_and_zero_below_width (p : MassiveParameters) {μ σ : ℝ} (hμ : 0 < μ) (hσ : 0 < σ)
    (hnarrow : σ^2 * μ^2 < (1 + Real.sqrt 2) / 2) :
    ∃ y : Spatial, temporal p μ σ y < 0 ∧
      ∃ t ∈ Ioo (0 : ℝ) 1, temporal p μ σ (t • y) = 0 ∧ packet μ σ (slicePoint 0 (t • y)) ≠ 0 := by
  obtain ⟨y, hy⟩ := MeasureTheory.nonempty_of_measure_ne_zero (past_volume_below_width p hμ hσ hnarrow).ne'
  exact ⟨y, hy, zero_on_segment p hμ hσ hy⟩

end FoliationQM.GaussianPacketCurrentSign
