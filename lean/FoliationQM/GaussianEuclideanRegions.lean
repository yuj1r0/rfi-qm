module

public import FoliationQM.LorentzCoordinates
public import FoliationQM.GaussianNormalTransitionRadius
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-!
# Euclidean radial regions in the observer's spatial coordinates

The scalar Fourier profile depends on the sum of the three squared
coordinates. The volume-preserving identification with Euclidean space
gives the volume and boundary of its radial regions in the original
coordinate Lebesgue measure used by v13 Eqs. 57–58.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.GaussianEuclideanRegions

open LorentzCoordinates MeasureTheory Metric Set

/-- Interior of the Euclidean ball of radius r about the spatial origin. -/
def openRegion (r : ℝ) : Set Spatial := {y | euclideanSpeed y < r}

/-- Closed Euclidean ball of radius r in the observer coordinates. -/
def closedRegion (r : ℝ) : Set Spatial := {y | euclideanSpeed y ≤ r}

/-- Points of exact Euclidean radius r. -/
def radialSphere (r : ℝ) : Set Spatial := {y | euclideanSpeed y = r}

private abbrev coordinates : Spatial ≃ₜ EuclideanSpace ℝ (Fin 3) :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.toHomeomorph

private theorem norm_coordinates (y : Spatial) : ‖coordinates y‖ = euclideanSpeed y := by
  rw [EuclideanSpace.norm_eq, euclideanSpeed, speedSq_eq_sum, Fin.sum_univ_three]
  simp [coordinates, Real.norm_eq_abs, sq_abs]

private theorem preimage_open (r : ℝ) : coordinates ⁻¹' ball 0 r = openRegion r := by
  ext y
  change dist (coordinates y) 0 < r ↔ euclideanSpeed y < r
  rw [dist_zero_right, norm_coordinates]

private theorem preimage_closed (r : ℝ) : coordinates ⁻¹' closedBall 0 r = closedRegion r := by
  ext y
  change dist (coordinates y) 0 ≤ r ↔ euclideanSpeed y ≤ r
  rw [dist_zero_right, norm_coordinates]

private theorem preimage_sphere (r : ℝ) : coordinates ⁻¹' sphere 0 r = radialSphere r := by
  ext y
  change dist (coordinates y) 0 = r ↔ euclideanSpeed y = r
  rw [dist_zero_right, norm_coordinates]

private theorem volume_coordinates : MeasurePreserving coordinates :=
  PiLp.volume_preserving_toLp (Fin 3)

/-- Closed Euclidean balls in the original spatial coordinates are compact. -/
theorem compact_closed (r : ℝ) : IsCompact (closedRegion r) := by
  rw [← preimage_closed]
  exact coordinates.isCompact_preimage.mpr (isCompact_closedBall _ _)

/-- Each spherical level set is compact in the spatial coordinates. -/
theorem compact_sphere (r : ℝ) : IsCompact (radialSphere r) := by
  rw [← preimage_sphere]
  exact coordinates.isCompact_preimage.mpr (isCompact_sphere _ _)

/-- The positive-radius sphere is precisely the topological boundary of its open interior. -/
theorem frontier_open {r : ℝ} (hr : 0 < r) : frontier (openRegion r) = radialSphere r := by
  rw [← preimage_open, ← coordinates.preimage_frontier, frontier_ball _ hr.ne', preimage_sphere]

/-- The interior has the usual three-dimensional Euclidean volume. -/
theorem volume_open (r : ℝ) :
    volume (openRegion r) = ENNReal.ofReal r ^ 3 * ENNReal.ofReal (Real.pi * 4 / 3) := by
  rw [← preimage_open, volume_coordinates.measure_preimage measurableSet_ball.nullMeasurableSet]
  exact EuclideanSpace.volume_ball_fin_three _ _

/-- The closed region has the same three-dimensional volume as its interior. -/
theorem volume_closed (r : ℝ) :
    volume (closedRegion r) = ENNReal.ofReal r ^ 3 * ENNReal.ofReal (Real.pi * 4 / 3) := by
  rw [← preimage_closed, volume_coordinates.measure_preimage measurableSet_closedBall.nullMeasurableSet]
  exact EuclideanSpace.volume_closedBall_fin_three _ _

/-- The Euclidean boundary sphere has zero three-dimensional spatial measure. -/
theorem volume_sphere (r : ℝ) : volume (radialSphere r) = 0 := by
  rw [← preimage_sphere, volume_coordinates.measure_preimage isClosed_sphere.measurableSet.nullMeasurableSet]
  exact Measure.addHaar_sphere volume _ _

/-- Every finite Euclidean ball leaves an exterior of infinite spatial volume. -/
theorem volume_exterior (r : ℝ) : volume {y : Spatial | r < euclideanSpeed y} = ⊤ := by
  have h : {y : Spatial | r < euclideanSpeed y} = (closedRegion r)ᶜ := by
    ext y
    simp [closedRegion]
  rw [h, measure_compl (compact_closed r).measurableSet (compact_closed r).measure_lt_top.ne]
  rw [measure_univ_of_isAddLeftInvariant]
  exact ENNReal.top_sub (compact_closed r).measure_lt_top.ne

/-- The positive normal coefficient fills a ball of the stated finite volume.
Its zero set has zero Lebesgue volume and its negative set has infinite volume. -/
theorem normal_region_measures {μ σ : ℝ} (hμ : 0 < μ) (hσ : 0 < σ) :
    let H := GaussianPositiveFrequencyPacket.normalCoefficient μ σ
    let r := GaussianNormalTransitionRadius.transitionRadius μ σ
    volume {y : Spatial | 0 < H y} = ENNReal.ofReal r ^ 3 * ENNReal.ofReal (Real.pi * 4 / 3) ∧
      volume {y : Spatial | H y = 0} = 0 ∧ volume {y : Spatial | H y < 0} = ⊤ := by
  dsimp only
  have signs := GaussianNormalTransitionRadius.normal_signs hμ hσ
  let r := GaussianNormalTransitionRadius.transitionRadius μ σ
  change volume _ = ENNReal.ofReal r ^ 3 * _ ∧ _
  rw [show {y : Spatial | 0 < GaussianPositiveFrequencyPacket.normalCoefficient μ σ y} =
      openRegion r from Set.ext fun y => (signs y).1,
    show {y : Spatial | GaussianPositiveFrequencyPacket.normalCoefficient μ σ y = 0} =
      radialSphere r from Set.ext fun y => (signs y).2.1,
    show {y : Spatial | GaussianPositiveFrequencyPacket.normalCoefficient μ σ y < 0} =
      {y | r < euclideanSpeed y} from Set.ext fun y => (signs y).2.2]
  exact ⟨volume_open r, volume_sphere r, volume_exterior r⟩

end FoliationQM.GaussianEuclideanRegions
