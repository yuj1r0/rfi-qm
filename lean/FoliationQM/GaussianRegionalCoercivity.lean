module

public import FoliationQM.GaussianSliceCoercivity
public import FoliationQM.GaussianPacketPolarDomain

/-!
# Initial Gaussian coercivity on the future-timelike region

For the free Gaussian in v13, lines 754–772, the physical drift and the
dilatation vanish initially wherever the positive-frequency packet has
future-timelike phase. A strict weighted bound on a spatial region also
requires a strictly positive spatial Fisher integral on that region.
-/

@[expose] public section
noncomputable section

namespace FoliationQM.GaussianRegionalCoercivity

open MeasureTheory LorentzCoordinates GaussianSliceMoments SpatialFisherEnergy

private theorem score_zero_iff {σ : ℝ} (hσ : 0 < σ) (y : Spatial) :
    score (density σ) y = 0 ↔ y = 0 := by
  rw [score_eq]
  constructor
  · intro h
    ext i
    have hi : -y i / σ ^ 2 = 0 := congrFun h i
    simpa [hσ.ne'] using hi
  · rintro rfl
    ext i
    simp

/-- The Gaussian Fisher integral is strictly positive on every spatial set
of positive Lebesgue volume. Its integrand vanishes only at the origin. -/
theorem fisher_pos_on_of_volume_pos {σ : ℝ} (hσ : 0 < σ) {A : Set Spatial} (hA : 0 < volume A) :
    0 < ∫ y in A, density σ y * speedSq (score (density σ) y) := by
  let f := fun y => density σ y * speedSq (score (density σ) y)
  have hf (y : Spatial) : 0 ≤ f y := mul_nonneg (density_pos σ y).le (speedSq_nonneg _)
  have he : Function.support f ∩ A = A \ {0} := by
    ext y
    simp only [Set.mem_inter_iff, Function.mem_support, f, ne_eq, mul_eq_zero, (density_pos σ y).ne',
      false_or, speedSq_eq_zero_iff, score_zero_iff hσ, Set.mem_sdiff, Set.mem_singleton_iff]
    exact and_comm
  change 0 < ∫ y in A, f y
  rw [setIntegral_pos_iff_support_of_nonneg_ae (ae_of_all _ hf) (integrable_fisher hσ).integrableOn,
    he, measure_sdiff_null (measure_singleton (0 : Spatial))]
  exact hA

/-- Every nonempty open spatial region carries strictly positive Gaussian
Fisher information at every positive width. -/
theorem fisher_pos_on_open {σ : ℝ} (hσ : 0 < σ) {A : Set Spatial} (ho : IsOpen A) (hn : A.Nonempty) :
    0 < ∫ y in A, density σ y * speedSq (score (density σ) y) :=
  fisher_pos_on_of_volume_pos hσ (ho.measure_pos volume hn)

open OsmoticSliceFields WeightedOsmoticCoercivity SpacelikeOsmoticIntegral
open DressedMassDensityVariation ActionDensity ObserverFluxDensity

/-- The spatial points of the initial positive-frequency packet with
positive real normal coefficient. -/
def futureRegion (p : MassiveParameters) (σ : ℝ) : Set Spatial :=
  {y | 0 < GaussianPacketPolarDomain.coefficient p σ y}

/-- This spatial region is exactly the intersection of the initial slice
with the future-timelike polar domain. -/
theorem mem_futureRegion_iff (p : MassiveParameters) {σ : ℝ} (hσ : 0 < σ) (y : Spatial) :
    y ∈ futureRegion p σ ↔
      0 < normalMomentum (GaussianPacketPolarDomain.action p σ) (slicePoint 0 y) ∧
      0 < minkowski (phaseDifferential (GaussianPacketPolarDomain.action p σ) (slicePoint 0 y))
        (phaseDifferential (GaussianPacketPolarDomain.action p σ) (slicePoint 0 y)) :=
  (GaussianPacketPolarDomain.future_iff p hσ y).symm

/-- The future portion of the initial slice is open. -/
theorem futureRegion_open (p : MassiveParameters) {σ : ℝ} (hσ : 0 < σ) : IsOpen (futureRegion p σ) :=
  isOpen_lt continuous_const (GaussianPositiveFrequencyPacket.smooth_normalCoefficient _ hσ).continuous

/-- The future portion contains the packet center for every positive width. -/
theorem center_mem_futureRegion (p : MassiveParameters) {σ : ℝ} (hσ : 0 < σ) :
    (0 : Spatial) ∈ futureRegion p σ :=
  GaussianPositiveFrequencyPacket.normal_center_pos (div_pos (mul_pos p.m_pos p.c_pos) p.hbar_pos) hσ

/-- The weighted norm of the actual spatial score is the square root of the
restricted Gaussian Fisher integral, on every spatial set. -/
theorem spatial_norm_eq (p : MassiveParameters) {σ : ℝ} (hσ : 0 < σ) (A : Set Spatial) :
    weightedNorm (volume.restrict A) (GaussianPacketPolarDomain.density p σ ∘ slicePoint 0)
      (scoreMagnitude (GaussianPacketPolarDomain.density p σ) 0) =
        Real.sqrt (∫ y in A, density σ y * speedSq (score (density σ) y)) := by
  rw [weightedNorm, GaussianPacketPolarDomain.density_eq p hσ]
  simp only [scoreMagnitude, euclideanSpeed_sq, GaussianPacketPolarDomain.spatial_score p hσ]

/-- The actual weighted dilatation norm vanishes on every spatial set
contained in the packet's initial future region. -/
theorem dilatation_norm_zero (p : MassiveParameters) {σ : ℝ} (hσ : 0 < σ) {A : Set Spatial}
    (hA : A ⊆ futureRegion p σ) :
    weightedNorm (volume.restrict A) (GaussianPacketPolarDomain.density p σ ∘ slicePoint 0)
      (dilatation p.c (GaussianPacketPolarDomain.action p σ) ∘ slicePoint 0) = 0 := by
  unfold weightedNorm
  rw [setIntegral_eq_zero_of_forall_eq_zero, Real.sqrt_zero]
  intro y hy
  simp only [Function.comp_apply, GaussianPacketPolarDomain.dilatation_zero p hσ y (hA hy),
    zero_pow (by decide : 2 ≠ 0), mul_zero]

/-- The strict weighted dilatation inequality of v13 Eq. 57 restricted to
the set A on the initial laboratory slice, for speed bound V. -/
def DilatationBoundOn (p : MassiveParameters) (σ : ℝ) (A : Set Spatial) (V : ℝ) : Prop :=
  weightedNorm (volume.restrict A) (GaussianPacketPolarDomain.density p σ ∘ slicePoint 0)
    (dilatation p.c (GaussianPacketPolarDomain.action p σ) ∘ slicePoint 0) <
    (p.c - V) * weightedNorm (volume.restrict A)
      (GaussianPacketPolarDomain.density p σ ∘ slicePoint 0)
      (scoreMagnitude (GaussianPacketPolarDomain.density p σ) 0)

/-- The supremum of the initial drift speed is zero on any nonempty set,
providing the uniform speed bound on the future region used in Eq. 57. -/
theorem speed_sup_on (p : MassiveParameters) {σ : ℝ} (hσ : 0 < σ) {A : Set Spatial}
    (hn : A.Nonempty) :
    (⨆ y : A, euclideanSpeed (phaseDrift p.c (GaussianPacketPolarDomain.action p σ)
      (slicePoint 0 y.val))) = 0 := by
  obtain ⟨y, hy⟩ := hn
  let : Nonempty A := ⟨⟨y, hy⟩⟩
  simp [GaussianPacketPolarDomain.drift_zero p hσ, euclideanSpeed, speedSq, spatialDot]

/-- On every positive-volume subset of the initial future region, the
packet satisfies the strict weighted bound at every speed bound below c. -/
theorem strict_on_of_volume_pos (p : MassiveParameters) {σ : ℝ} (hσ : 0 < σ) {A : Set Spatial}
    (hvol : 0 < volume A) (hA : A ⊆ futureRegion p σ) {V : ℝ} (hV : V < p.c) :
    DilatationBoundOn p σ A V := by
  rw [DilatationBoundOn, dilatation_norm_zero p hσ hA, spatial_norm_eq p hσ]
  exact mul_pos (sub_pos.mpr hV) (Real.sqrt_pos.mpr (fisher_pos_on_of_volume_pos hσ hvol))

/-- Every nonempty open subset of the future region satisfies the strict
weighted inequality with zero speed bound, the actual initial drift speed. -/
theorem strict_on_open (p : MassiveParameters) {σ : ℝ} (hσ : 0 < σ) {A : Set Spatial}
    (ho : IsOpen A) (hn : A.Nonempty) (hA : A ⊆ futureRegion p σ) :
    DilatationBoundOn p σ A 0 :=
  strict_on_of_volume_pos p hσ (ho.measure_pos volume hn) hA p.c_pos

/-- The entire open future region, containing the center, satisfies the
strict weighted dilatation bound on the initial slice at every positive width. -/
theorem strict_on_future_region (p : MassiveParameters) {σ : ℝ} (hσ : 0 < σ) :
    DilatationBoundOn p σ (futureRegion p σ) 0 :=
  strict_on_open p hσ (futureRegion_open p hσ) ⟨0, center_mem_futureRegion p hσ⟩ (Set.Subset.rfl)

end FoliationQM.GaussianRegionalCoercivity
