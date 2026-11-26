module

public import FoliationQM.GaussianCompactFutureTube
public import FoliationQM.GaussianFutureCurrentGeometry

/-!
# Persistent future and past currents on fixed concentric regions

For the Gaussian clause of v13 Theorem 5.8(ii), choose a closed ball strictly
inside the initial transition radius and a sphere strictly outside it. A common
two-sided laboratory interval preserves both orientations and timelikeness on
these regions. The wave stays nonzero everywhere in the closed outer ball.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.GaussianCurrentCollar

open Set Metric LorentzCoordinates OsmoticSliceFields GaussianPacketPolarDomain
open GaussianEuclideanRegions GaussianFutureCurrentGeometry GaussianCompactFutureTube
open scoped Topology

/-- The physical four-current at laboratory time τ and spatial position y. -/
abbrev currentAt (p : MassiveParameters) (σ τ : ℝ) (y : Spatial) : Covector :=
  ScalarPhaseCurrent.current p (wave p σ) (slicePoint (p.c*τ) y)

/-- All four components of the physical Noether current vary continuously in spacetime. -/
theorem continuous_current (p : MassiveParameters) {σ : ℝ} (hσ : 0 < σ) :
    Continuous (ScalarPhaseCurrent.current p (wave p σ)) :=
  continuous_iff_continuousAt.mpr fun _ => ScalarPhaseCurrent.continuousAt_current p
    ((GaussianPositiveFrequencyPacket.smooth_packet _ hσ).contDiffAt.of_le (by simp))

/-- A laboratory interval with timelike future current on the closed inner ball,
timelike past current on the outer sphere, and nonzero wave on the closed outer ball. -/
structure Collar (p : MassiveParameters) (σ a b δ : ℝ) : Prop where
  inner_pos : ∀ τ ∈ Icc (-δ) δ, ∀ y ∈ closedRegion a, 0 < currentAt p σ τ y 0
  outer_neg : ∀ τ ∈ Icc (-δ) δ, ∀ y ∈ radialSphere b, currentAt p σ τ y 0 < 0
  wave_ne : ∀ τ ∈ Icc (-δ) δ, ∀ y ∈ closedRegion b, wave p σ (slicePoint (p.c*τ) y) ≠ 0
  inner_timelike : ∀ τ ∈ Icc (-δ) δ, ∀ y ∈ closedRegion a,
    0 < minkowski (currentAt p σ τ y) (currentAt p σ τ y)
  outer_timelike : ∀ τ ∈ Icc (-δ) δ, ∀ y ∈ radialSphere b,
    0 < minkowski (currentAt p σ τ y) (currentAt p σ τ y)

private theorem eventually_on_compact (p : MassiveParameters) {K : Set Spatial}
    (hK : IsCompact K) {U : Set Covector} (hU : IsOpen U)
    (hinit : ∀ y ∈ K, slicePoint 0 y ∈ U) :
    ∀ᶠ τ in 𝓝 (0 : ℝ), ∀ y ∈ K, slicePoint (p.c*τ) y ∈ U := by
  have hsub : ({0} : Set ℝ) ×ˢ K ⊆ sliceMap p ⁻¹' U := by
    rintro ⟨t,y⟩ ⟨(rfl : t = 0),hy⟩
    simpa [sliceMap] using hinit y hy
  obtain ⟨A,B,hA,_,h0,hB,hAB⟩ :=
    generalized_tube_lemma isCompact_singleton hK (hU.preimage (continuous_sliceMap p)) hsub
  filter_upwards [hA.mem_nhds (singleton_subset_iff.mp h0)] with τ hτ
  exact fun y hy => hAB (a := (τ,y)) ⟨hτ,hB hy⟩

/-- Each pair of fixed inner and outer radii strictly bracketing the initial
transition radius admits a common positive time radius for the current collar. -/
theorem exists_collar (p : MassiveParameters) {σ a b : ℝ} (hσ : 0 < σ) (_ha : 0 ≤ a)
    (hain : a < radius p σ) (hbout : radius p σ < b) :
    ∃ δ : ℝ, 0 < δ ∧ Collar p σ a b δ := by
  let J := ScalarPhaseCurrent.current p (wave p σ)
  have hj : Continuous J := continuous_current p hσ
  have ht : Continuous (fun x => J x 0) := (continuous_apply 0).comp hj
  have hm : Continuous (fun x => minkowski (J x) (J x)) :=
    (show Continuous (fun v : Covector => minkowski v v) by unfold minkowski; fun_prop).comp hj
  have hi := eventually_on_compact p (compact_closed a)
    ((isOpen_lt continuous_const ht).inter (isOpen_lt continuous_const hm)) (by
      intro y hy
      have hlt : euclideanSpeed y < radius p σ := lt_of_le_of_lt hy hain
      exact ⟨(temporal_signs p hσ y).1.mpr hlt, (current_timelike_iff p hσ y).mpr hlt.ne⟩)
  have ho := eventually_on_compact p (compact_sphere b)
    ((isOpen_lt ht continuous_const).inter (isOpen_lt continuous_const hm)) (by
      intro y hy
      have hlt : radius p σ < euclideanSpeed y := hbout.trans_eq (Eq.symm hy)
      exact (exterior_past_timelike p hσ hlt).symm)
  have hw := eventually_on_compact p (compact_closed b)
    (isOpen_ne_fun (GaussianPositiveFrequencyPacket.smooth_packet (p.m*p.c/p.hbar) hσ).continuous
      (continuous_const (y := (0 : ℂ)))) (fun y _ =>
        GaussianPacketCurrentSign.initial_wave_ne_zero _ hσ y)
  obtain ⟨δ,hδ,hball⟩ := nhds_basis_closedBall.mem_iff.mp (hi.and (ho.and hw))
  have htime (τ : ℝ) (hτ : τ ∈ Icc (-δ) δ) := hball (by
    simpa [Real.closedBall_eq_Icc] using hτ : τ ∈ closedBall (0 : ℝ) δ)
  exact ⟨δ,hδ,⟨fun τ hτ y hy => ((htime τ hτ).1 y hy).1,
    fun τ hτ y hy => ((htime τ hτ).2.1 y hy).1, fun τ hτ => (htime τ hτ).2.2,
    fun τ hτ y hy => ((htime τ hτ).1 y hy).2, fun τ hτ y hy => ((htime τ hτ).2.1 y hy).2⟩⟩

end FoliationQM.GaussianCurrentCollar
