module

public import FoliationQM.GaussianCurrentCollar
public import FoliationQM.DeBrogliePhase

/-!
# Temporal current zeros on every spatial ray at nearby laboratory times

The massive positive-frequency Gaussian in v13 Theorem 5.8(ii) has an
initial current transition sphere. On two spheres of fixed radii bracketing
it, the temporal currents retain opposite signs for a common time interval.
The field stays nonzero throughout the intervening shell. Continuity along
each radial segment then gives a zero of the temporal current component.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.GaussianPersistentCurrentZero

open Set LorentzCoordinates OsmoticSliceFields GaussianPacketPolarDomain
open GaussianFutureCurrentGeometry GaussianEuclideanRegions GaussianCurrentCollar

private theorem ray_radius {e : Spatial} (he : euclideanSpeed e = 1) {r : ℝ} (hr : 0 ≤ r) :
    euclideanSpeed (r • e) = r := by
  rw [DeBrogliePhase.euclideanSpeed_smul, abs_of_nonneg hr, he, mul_one]

private theorem square_nonpos {j : Covector} (h : j 0 = 0) : minkowski j j ≤ 0 := by
  rw [minkowski, h, zero_mul]
  nlinarith only [sq_nonneg (j 1), sq_nonneg (j 2), sq_nonneg (j 3)]

/-- Every unit spatial ray has a nonnodal temporal current zero strictly between the
two prescribed radii at each laboratory time in one common symmetric interval.
The Minkowski square of the current at that event is nonpositive. -/
theorem zero_on_rays (p : MassiveParameters) {σ a b : ℝ} (hσ : 0 < σ) (ha : 0 ≤ a)
    (hain : a < radius p σ) (hbout : radius p σ < b) :
    ∃ T : ℝ, 0 < T ∧ ∀ τ ∈ Icc (-T) T, ∀ e : Spatial, euclideanSpeed e = 1 →
      ∃ r ∈ Ioo a b, let x := slicePoint (p.c*τ) (r • e)
        let j := ScalarPhaseCurrent.current p (wave p σ) x
        j 0 = 0 ∧ wave p σ x ≠ 0 ∧ minkowski j j ≤ 0 := by
  obtain ⟨T, hT, collar⟩ := exists_collar p hσ ha hain hbout
  refine ⟨T, hT, ?_⟩
  intro τ hτ e he
  let point := fun r : ℝ => slicePoint (p.c*τ) (r • e)
  let f := fun r : ℝ => ScalarPhaseCurrent.current p (wave p σ) (point r) 0
  have hpoint : Continuous point := (SpatialFisherEnergy.contDiff_slicePoint (p.c*τ) 1).continuous.comp
    (continuous_id.smul continuous_const)
  have hf : Continuous f := (continuous_apply (0 : Fin 4)).comp ((continuous_current p hσ).comp hpoint)
  have hab := hain.trans hbout
  have hlo : 0 < f a := collar.inner_pos τ hτ _ (show euclideanSpeed (a • e) ≤ a from (ray_radius he ha).le)
  have hhi : f b < 0 := collar.outer_neg τ hτ _ (ray_radius he (ha.trans hab.le))
  obtain ⟨r, hr, hz⟩ := intermediate_value_Ioo' hab.le hf.continuousOn
    (show (0 : ℝ) ∈ Ioo (f b) (f a) from ⟨hhi, hlo⟩)
  have hy : r • e ∈ closedRegion b := (ray_radius he (ha.trans hr.1.le)).le.trans hr.2.le
  exact ⟨r, hr, hz, collar.wave_ne τ hτ _ hy, square_nonpos hz⟩

/-- Given any positive radial tolerance, one symmetric laboratory time interval
works simultaneously for every direction. Each ray meets a nonnodal temporal
zero at a positive radius within the tolerance of the initial transition sphere. -/
theorem zero_in_arbitrarily_thin_collar (p : MassiveParameters) {σ ε : ℝ} (hσ : 0 < σ)
    (hε : 0 < ε) :
    ∃ T : ℝ, 0 < T ∧ ∀ τ ∈ Icc (-T) T, ∀ e : Spatial, euclideanSpeed e = 1 →
      ∃ r : ℝ, 0 < r ∧ |r - radius p σ| < ε ∧
        let x := slicePoint (p.c*τ) (r • e)
        let j := ScalarPhaseCurrent.current p (wave p σ) x
        j 0 = 0 ∧ wave p σ x ≠ 0 ∧ minkowski j j ≤ 0 := by
  let R := radius p σ
  have hR : 0 < R := radius_pos p hσ
  let a := max 0 (R - ε)
  have ha : 0 ≤ a := le_max_left _ _
  have hain : a < R := max_lt hR (sub_lt_self _ hε)
  have hbout : R < R + ε := lt_add_of_pos_right _ hε
  obtain ⟨T, hT, hall⟩ := zero_on_rays p hσ ha hain hbout
  refine ⟨T, hT, ?_⟩
  intro τ hτ e he
  obtain ⟨r, hr, hz⟩ := hall τ hτ e he
  have hlo : R - ε < r := (le_max_right _ _).trans_lt hr.1
  have hhi : r < R + ε := hr.2
  have hd : |r - R| < ε := abs_lt.mpr ⟨by linarith, by linarith⟩
  exact ⟨r, ha.trans_lt hr.1, hd, hz⟩

end FoliationQM.GaussianPersistentCurrentZero
