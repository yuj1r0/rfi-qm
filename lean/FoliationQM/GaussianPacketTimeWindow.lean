module

public import FoliationQM.GaussianPacketTimeRegularity
public import FoliationQM.GaussianRegionalCoercivity

/-!
# Fixed spatial windows for the massive Gaussian packet

An off-center future point on the initial slice has positive spatial
log-density score, zero drift and zero dilatation. Local strict margins
for these continuous observables yield a single closed spatial ball for
all normal time coordinates in a two-sided interval. The norm on the
three Cartesian coordinate functions is the supremum norm.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.GaussianPacketTimeWindow

open Filter Set Metric LorentzCoordinates GaussianPacketPolarDomain GaussianPacketTimeRegularity
open OsmoticSliceFields ObserverFluxDensity
open scoped Topology

/-- On a fixed spacetime window the physical lab drift has cap c/2 and
the absolute dilatation is strictly below c/4 times the spatial score. -/
structure PointBounds (p : MassiveParameters) (σ : ℝ) (x : Covector) : Prop
    extends Fields p σ x where
  mem_domain : x ∈ domain p σ
  speed_lt : euclideanSpeed (phaseDrift p.c (action p σ) x) < p.c / 2
  score_pos : 0 < euclideanSpeed (spatialScore (density p σ) x)
  dilatation_lt : |dilatation p.c (action p σ) x| <
    (p.c / 4) * euclideanSpeed (spatialScore (density p σ) x)

private theorem continuous_slice : Continuous (fun w : ℝ × Spatial => slicePoint w.1 w.2) := by
  apply continuous_pi
  intro i
  fin_cases i
  · exact continuous_fst
  · exact (continuous_apply (0 : Fin 3)).comp continuous_snd
  · exact (continuous_apply (1 : Fin 3)).comp continuous_snd
  · exact (continuous_apply (2 : Fin 3)).comp continuous_snd

/-- At every off-center initial point the norm of the Gaussian spatial
log-density gradient is positive. -/
theorem initial_score_pos (p : MassiveParameters) {σ : ℝ} (hσ : 0 < σ)
    {y : Spatial} (hy : y ≠ 0) :
    0 < euclideanSpeed (spatialScore (density p σ) (slicePoint 0 y)) := by
  rw [euclideanSpeed, Real.sqrt_pos, spatial_score p hσ y, GaussianSliceMoments.score_eq]
  apply lt_of_le_of_ne (speedSq_nonneg _)
  intro he
  have hz := speedSq_eq_zero_iff _ |>.mp he.symm
  apply hy
  ext i
  have hi : -y i / σ ^ 2 = 0 := congrFun hz i
  simpa [hσ.ne'] using hi

/-- Every positive-width rest packet has an off-center future point on the initial slice,
since its future region contains a neighborhood of the center. -/
theorem exists_future_off_center (p : MassiveParameters) {σ : ℝ} (hσ : 0 < σ) :
    ∃ y : Spatial, 0 < coefficient p σ y ∧ y ≠ 0 := by
  have h := (GaussianRegionalCoercivity.futureRegion_open p hσ).mem_nhds
    (GaussianRegionalCoercivity.center_mem_futureRegion p hσ)
  have hp : ∀ᶠ y in 𝓝[≠] (0 : Spatial), 0 < coefficient p σ y :=
    mem_nhdsWithin_of_mem_nhds h
  have hn : ∀ᶠ y in 𝓝[≠] (0 : Spatial), y ≠ 0 := self_mem_nhdsWithin
  exact (hp.and hn).exists

/-- Around any off-center future initial point there is a spacetime neighborhood
with the same drift and dilatation caps. -/
theorem eventually_bounds (p : MassiveParameters) {σ : ℝ} (hσ : 0 < σ)
    (y : Spatial) (hy : 0 < coefficient p σ y) (hn : y ≠ 0) :
    ∀ᶠ x in 𝓝 (slicePoint 0 y), PointBounds p σ x := by
  have hx := slice_mem_domain p hσ y hy
  have hf := fields p hσ hx
  have hG := initial_score_pos p hσ hn
  have hspeed : euclideanSpeed (phaseDrift p.c (action p σ) (slicePoint 0 y)) < p.c / 2 := by
    rw [drift_zero p hσ y]
    simpa [euclideanSpeed, speedSq, spatialDot] using half_pos p.c_pos
  have hD : |dilatation p.c (action p σ) (slicePoint 0 y)| <
      (p.c / 4) * euclideanSpeed (spatialScore (density p σ) (slicePoint 0 y)) := by
    rw [dilatation_zero p hσ y hy, abs_zero]
    exact mul_pos (div_pos p.c_pos (by norm_num)) hG
  filter_upwards [(isOpen_domain p hσ).mem_nhds hx,
    hf.speed_continuous.eventually_lt_const hspeed,
    hf.score_continuous.eventually_const_lt hG,
    hf.dilatation_smooth.continuousAt.abs.eventually_lt
      (continuousAt_const.mul hf.score_continuous) hD] with x hdom hv hg hd
  exact ⟨fields p hσ hdom, hdom, hv, hg, hd⟩

/-- Every prescribed off-center future point admits a nonzero two-sided time interval
and a fixed closed spatial ball centered there, with the stated strict bounds on the full cylinder. -/
theorem exists_window_at (p : MassiveParameters) {σ : ℝ} (hσ : 0 < σ)
    (y₀ : Spatial) (hy : 0 < coefficient p σ y₀) (hn : y₀ ≠ 0) :
    ∃ r : ℝ, 0 < r ∧ ∀ t ∈ Icc (-r) r, ∀ y ∈ closedBall y₀ r,
      PointBounds p σ (slicePoint t y) := by
  have h : ∀ᶠ w : ℝ × Spatial in 𝓝 (0, y₀), PointBounds p σ (slicePoint w.1 w.2) :=
    continuous_slice.continuousAt (eventually_bounds p hσ y₀ hy hn)
  obtain ⟨r, hr, hball⟩ := nhds_basis_closedBall.mem_iff.mp h
  refine ⟨r, hr, fun t ht y hy' => ?_⟩
  apply hball (a := (t,y))
  rw [← closedBall_prod_same]
  exact ⟨by simpa [Real.closedBall_eq_Icc] using ht, hy'⟩

/-- For every positive width, one fixed positive-radius spatial ball satisfies the
uniform bounds at all normal times in a nonzero interval about the initial slice. -/
theorem exists_window (p : MassiveParameters) {σ : ℝ} (hσ : 0 < σ) :
    ∃ (y₀ : Spatial) (r : ℝ), 0 < r ∧ ∀ t ∈ Icc (-r) r, ∀ y ∈ closedBall y₀ r,
      PointBounds p σ (slicePoint t y) := by
  obtain ⟨y₀, hy, hn⟩ := exists_future_off_center p hσ
  exact ⟨y₀, exists_window_at p hσ y₀ hy hn⟩

end FoliationQM.GaussianPacketTimeWindow
