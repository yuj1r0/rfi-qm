module

public import FoliationQM.GaussianEuclideanRegions
public import FoliationQM.GaussianPacketCurrentSign
public import FoliationQM.GaussianRegionalCoercivity

/-!
# Physical current at the Gaussian transition sphere

At the initial laboratory time in the free rest-packet clause of v13
Theorem 5.8(ii), the Noether current has only its temporal component.
The transition radius separates the future-timelike ball from the
past-timelike exterior. The entire current vanishes on their common
sphere, where the wave amplitude and density are still positive.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.GaussianFutureCurrentGeometry

open Set MeasureTheory LorentzCoordinates OsmoticSliceFields GaussianEuclideanRegions
open GaussianNormalTransitionRadius GaussianPacketPolarDomain GaussianRegionalCoercivity

/-- The unique initial current transition radius at physical mass parameter `mc/ℏ`. -/
def radius (p : MassiveParameters) (σ : ℝ) : ℝ := transitionRadius (p.m * p.c / p.hbar) σ

/-- The physical transition radius is strictly positive for every positive width. -/
theorem radius_pos (p : MassiveParameters) {σ : ℝ} (hσ : 0 < σ) : 0 < radius p σ :=
  transitionRadius_pos (div_pos (mul_pos p.m_pos p.c_pos) p.hbar_pos) hσ

/-- The initial future-timelike polar domain is exactly the physical open Euclidean ball. -/
theorem futureRegion_eq (p : MassiveParameters) {σ : ℝ} (hσ : 0 < σ) :
    futureRegion p σ = openRegion (radius p σ) := Set.ext fun y =>
  (normal_signs (div_pos (mul_pos p.m_pos p.c_pos) p.hbar_pos) hσ y).1

/-- The Noether four-current of the actual physical packet at zero laboratory time. -/
abbrev initialCurrent (p : MassiveParameters) (σ : ℝ) (y : Spatial) : Covector :=
  ScalarPhaseCurrent.current p (wave p σ) (slicePoint 0 y)

/-- The interior, sphere and exterior give all three temporal signs of the actual current. -/
theorem temporal_signs (p : MassiveParameters) {σ : ℝ} (hσ : 0 < σ) (y : Spatial) :
    (0 < initialCurrent p σ y 0 ↔ euclideanSpeed y < radius p σ) ∧
    (initialCurrent p σ y 0 = 0 ↔ euclideanSpeed y = radius p σ) ∧
    (initialCurrent p σ y 0 < 0 ↔ radius p σ < euclideanSpeed y) := by
  have h := normal_signs (div_pos (mul_pos p.m_pos p.c_pos) p.hbar_pos) hσ y
  have hj := GaussianPacketCurrentSign.temporal_sign p (p.m*p.c/p.hbar) hσ y
  exact ⟨hj.1.trans h.1, hj.2.2.trans h.2.1, hj.2.1.trans h.2.2⟩

/-- The whole four-current vanishes precisely on the transition sphere. -/
theorem current_zero_iff (p : MassiveParameters) {σ : ℝ} (hσ : 0 < σ) (y : Spatial) :
    initialCurrent p σ y = 0 ↔ y ∈ radialSphere (radius p σ) := by
  have ht := (temporal_signs p hσ y).2.1
  constructor
  · intro hj
    exact ht.mp (congrFun hj 0)
  · intro hy
    funext i
    exact Fin.cases (ht.mpr hy) (spatial_current p hσ y) i

/-- The zero-current sphere carries a strictly positive real wave amplitude and density. -/
theorem sphere_fields (p : MassiveParameters) {σ : ℝ} (hσ : 0 < σ) {y : Spatial}
    (hy : y ∈ radialSphere (radius p σ)) :
    initialCurrent p σ y = 0 ∧
      wave p σ (slicePoint 0 y) = (GaussianCauchySlice.amplitude σ y : ℂ) ∧
      0 < GaussianCauchySlice.amplitude σ y ∧ 0 < density p σ (slicePoint 0 y) :=
  ⟨(current_zero_iff p hσ y).mpr hy, GaussianPositiveFrequencyPacket.initial_value _ hσ y,
    GaussianCauchySlice.amplitude_pos σ y, (regularity p hσ y).2.2⟩

/-- The transition sphere is the topological boundary of the physical future region. -/
theorem frontier_futureRegion (p : MassiveParameters) {σ : ℝ} (hσ : 0 < σ) :
    frontier (futureRegion p σ) = radialSphere (radius p σ) := by
  rw [futureRegion_eq p hσ, frontier_open (radius_pos p hσ)]

/-- The current's Minkowski square on the slice equals its temporal component squared. -/
theorem current_square (p : MassiveParameters) {σ : ℝ} (hσ : 0 < σ) (y : Spatial) :
    minkowski (initialCurrent p σ y) (initialCurrent p σ y) = (initialCurrent p σ y 0)^2 := by
  have h1 : initialCurrent p σ y 1 = 0 := spatial_current p hσ y 0
  have h2 : initialCurrent p σ y 2 = 0 := spatial_current p hσ y 1
  have h3 : initialCurrent p σ y 3 = 0 := spatial_current p hσ y 2
  simp [minkowski, h1, h2, h3, sq]

/-- Exactly the points off the transition sphere carry a timelike four-current. -/
theorem current_timelike_iff (p : MassiveParameters) {σ : ℝ} (hσ : 0 < σ) (y : Spatial) :
    0 < minkowski (initialCurrent p σ y) (initialCurrent p σ y) ↔
      y ∉ radialSphere (radius p σ) := by
  rw [current_square p hσ, sq_pos_iff]
  exact (temporal_signs p hσ y).2.1.not

/-- The open future region defined by the polar phase is also the exact set where
the original wave's four-current is future-timelike. -/
theorem future_current_iff (p : MassiveParameters) {σ : ℝ} (hσ : 0 < σ) (y : Spatial) :
    (0 < initialCurrent p σ y 0 ∧ 0 < minkowski (initialCurrent p σ y) (initialCurrent p σ y)) ↔
      y ∈ futureRegion p σ := by
  rw [futureRegion_eq p hσ]
  exact ⟨fun h => (temporal_signs p hσ y).1.mp h.1, fun hy =>
    ⟨(temporal_signs p hσ y).1.mpr hy, (current_timelike_iff p hσ y).mpr (ne_of_lt hy)⟩⟩

/-- Beyond the transition radius the physical packet carries a past-timelike four-current. -/
theorem exterior_past_timelike (p : MassiveParameters) {σ : ℝ} (hσ : 0 < σ) {y : Spatial}
    (hy : radius p σ < euclideanSpeed y) :
    0 < minkowski (initialCurrent p σ y) (initialCurrent p σ y) ∧ initialCurrent p σ y 0 < 0 :=
  ⟨(current_timelike_iff p hσ y).mpr (ne_of_gt hy), (temporal_signs p hσ y).2.2.mpr hy⟩

/-- At initial time the future-current ball has Euclidean volume `4πr³/3`, the zero-current
sphere has zero spatial volume, and the past-oriented exterior has infinite spatial volume. -/
theorem current_region_volumes (p : MassiveParameters) {σ : ℝ} (hσ : 0 < σ) :
    volume (futureRegion p σ) = ENNReal.ofReal (radius p σ)^3 * ENNReal.ofReal (Real.pi*4/3) ∧
    volume {y : Spatial | initialCurrent p σ y = 0} = 0 ∧
    volume {y : Spatial | initialCurrent p σ y 0 < 0} = ⊤ := by
  rw [futureRegion_eq p hσ,
    show {y : Spatial | initialCurrent p σ y = 0} = radialSphere (radius p σ) from
      Set.ext (current_zero_iff p hσ),
    show {y : Spatial | initialCurrent p σ y 0 < 0} = {y | radius p σ < euclideanSpeed y} from
      Set.ext fun y => (temporal_signs p hσ y).2.2]
  exact ⟨volume_open _, volume_sphere _, volume_exterior _⟩

end FoliationQM.GaussianFutureCurrentGeometry
