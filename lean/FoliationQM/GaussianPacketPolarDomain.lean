module

public import FoliationQM.GaussianGlobalCauchyData
public import FoliationQM.GaussianPositiveFrequencyPacket

/-!
# Polar data on the initial slice of the positive-frequency Gaussian packet

For the physical mass shell Ω² = (mc/ℏ)² + |k|², the initial amplitude R is
positive at every spatial point. Its normal derivative is −iH, where H is
the actual inverse cosine transform of the frequency-weighted spectrum.
In the laboratory frame of v13 lines 752–767 the normal momentum is ℏH/R.
We identify the future-timelike region and evaluate the dilatation there.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.GaussianPacketPolarDomain

open LorentzCoordinates OsmoticSliceFields ObserverFluxDensity DressedMassDensityVariation
open GaussianCauchySlice GaussianPositiveFrequencyPacket PolarSecondDifferential ActionDensity
open scoped ContDiff

/-- The massive positive-frequency Gaussian spacetime field. -/
abbrev wave (p : MassiveParameters) (σ : ℝ) : Covector → ℂ := packet (p.m * p.c / p.hbar) σ

/-- Squared modulus of the physical packet. -/
abbrev density (p : MassiveParameters) (σ : ℝ) : Covector → ℝ :=
  GaussianGlobalCauchyData.density (wave p σ)

/-- Action in the logarithm chart containing the positive real initial slice. -/
abbrev action (p : MassiveParameters) (σ : ℝ) : Covector → ℝ :=
  GaussianGlobalCauchyData.action p (wave p σ)

/-- The real coefficient H of the physical packet's imaginary normal derivative. -/
abbrev coefficient (p : MassiveParameters) (σ : ℝ) : Spatial → ℝ :=
  normalCoefficient (p.m * p.c / p.hbar) σ

private theorem initial_wave (p : MassiveParameters) {σ : ℝ} (hσ : 0 < σ) (y : Spatial) :
    actionField p (density p σ) (action p σ) (slicePoint 0 y) = (amplitude σ y : ℂ) := by
  rw [GaussianGlobalCauchyData.reconstruct]
  exact initial_value _ hσ y

private theorem initial_slope (p : MassiveParameters) {σ : ℝ} (hσ : 0 < σ) (y : Spatial) :
    directionalDerivative (actionField p (density p σ) (action p σ))
      (Madelung.coordinateVector 0) (slicePoint 0 y) =
      actionField p (density p σ) (action p σ) (slicePoint 0 y) *
        (((0 : ℝ) : ℂ) - Complex.I * ((coefficient p σ y / amplitude σ y : ℝ) : ℂ)) := by
  rw [initial_wave p hσ y, GaussianGlobalCauchyData.reconstruct, initial_normal _ hσ y]
  push_cast
  have hR : (amplitude σ y : ℂ) ≠ 0 := by exact_mod_cast (amplitude_pos σ y).ne'
  field_simp [hR]
  ring

/-- The actual density is strictly positive and both polar fields are smooth at every
initial point, including points where the temporal current vanishes. -/
theorem regularity (p : MassiveParameters) {σ : ℝ} (hσ : 0 < σ) (y : Spatial) :
    ContDiffAt ℝ ∞ (density p σ) (slicePoint 0 y) ∧
      ContDiffAt ℝ ∞ (action p σ) (slicePoint 0 y) ∧ 0 < density p σ (slicePoint 0 y) := by
  have hs := (smooth_packet (p.m * p.c / p.hbar) hσ).contDiffAt (x := slicePoint 0 y)
  have hm : wave p σ (slicePoint 0 y) ∈ PolarLocalInverse.chartDomain 1 := by
    rw [show wave p σ (slicePoint 0 y) = _ from initial_value _ hσ y]
    simpa [PolarLocalInverse.chartDomain] using Complex.ofReal_mem_slitPlane.mpr (amplitude_pos σ y)
  exact ⟨(PolarLocalInverse.contDiff_normSq ∞).contDiffAt.comp _ hs,
    (PolarLocalInverse.contDiffAt_localAction p hm ∞).comp _ hs,
    PolarLocalInverse.normSq_pos_of_mem_chartDomain hm⟩

/-- The physical density restricts to the Gaussian intensity with variance σ² per axis. -/
theorem density_eq (p : MassiveParameters) {σ : ℝ} (hσ : 0 < σ) :
    density p σ ∘ slicePoint 0 = GaussianSliceMoments.density σ := by
  funext y
  change density p σ (slicePoint 0 y) = _
  rw [density_of_real_slice p (initial_wave p hσ) y (regularity p hσ y).2.2.le]
  unfold amplitude GaussianSliceMoments.density
  rw [sq, ← Real.exp_add]
  congr 1
  ring

/-- The ambient spatial log-density gradient restricts to the true Gaussian score. -/
theorem spatial_score (p : MassiveParameters) {σ : ℝ} (hσ : 0 < σ) (y : Spatial) :
    spatialScore (density p σ) (slicePoint 0 y) =
      SpatialFisherEnergy.score (GaussianSliceMoments.density σ) y := by
  obtain ⟨hr, _, hp⟩ := regularity p hσ y
  rw [← SpatialFisherEnergy.score_slice 0 (hr.differentiableAt (by simp)) hp, density_eq p hσ]

private theorem normal_values (p : MassiveParameters) {σ : ℝ} (hσ : 0 < σ) (y : Spatial) :
    normalScore (density p σ) (slicePoint 0 y) = 0 ∧
      normalMomentum (action p σ) (slicePoint 0 y) = p.hbar * (coefficient p σ y / amplitude σ y) := by
  obtain ⟨hr, hs, hp⟩ := regularity p hσ y
  simpa only [mul_zero] using normal_data p (hr.differentiableAt (by simp))
    (hs.differentiableAt (by simp)) hp 0 _ (initial_slope p hσ y)

/-- The normal logarithmic density derivative is zero everywhere on the initial slice. -/
theorem normal_score (p : MassiveParameters) {σ : ℝ} (hσ : 0 < σ) (y : Spatial) :
    normalScore (density p σ) (slicePoint 0 y) = 0 := (normal_values p hσ y).1

/-- The actual normal phase momentum is ℏ times the signed local rate H/R. -/
theorem normal_momentum (p : MassiveParameters) {σ : ℝ} (hσ : 0 < σ) (y : Spatial) :
    normalMomentum (action p σ) (slicePoint 0 y) =
      p.hbar * (coefficient p σ y / amplitude σ y) := (normal_values p hσ y).2

/-- Every spatial component of the original packet's Noether current vanishes on the slice. -/
theorem spatial_current (p : MassiveParameters) {σ : ℝ} (hσ : 0 < σ) (y : Spatial) (i : Fin 3) :
    ScalarPhaseCurrent.current p (wave p σ) (slicePoint 0 y) i.succ = 0 := by
  obtain ⟨hr, hs, hp⟩ := regularity p hσ y
  have hc := (slice_current p (hr.differentiableAt (by simp)) (hs.differentiableAt (by simp))
    hp ((smooth_amplitude σ).differentiable (by simp) y) (initial_wave p hσ) 0 _
    (initial_slope p hσ y)).1
  rw [GaussianGlobalCauchyData.reconstruct] at hc
  exact (congrFun hc i.succ).trans (Pi.single_eq_of_ne (Fin.succ_ne_zero i) _)

/-- The spatial phase differential vanishes even on the zero and past temporal-current sets. -/
theorem phase_spatial (p : MassiveParameters) {σ : ℝ} (hσ : 0 < σ) (y : Spatial) (i : Fin 3) :
    phaseDifferential (action p σ) (slicePoint 0 y) i.succ = 0 := by
  obtain ⟨hr, hs, hp⟩ := regularity p hσ y
  have hc := ScalarDressedCurrent.current_actionField p (hr.differentiableAt (by simp))
    (hs.differentiableAt (by simp)) hp i.succ
  rw [GaussianGlobalCauchyData.reconstruct, spatial_current p hσ y i] at hc
  exact (mul_eq_zero.mp hc.symm).resolve_left (neg_ne_zero.mpr (div_ne_zero hp.ne' p.m_pos.ne'))

/-- The laboratory drift is identically zero on the initial spatial slice. -/
theorem drift_zero (p : MassiveParameters) {σ : ℝ} (hσ : 0 < σ) (y : Spatial) :
    phaseDrift p.c (action p σ) (slicePoint 0 y) = 0 := by
  funext i
  simp [phaseDrift, phase_spatial p hσ y i]

/-- Exactly the points with H > 0 have both future normal phase momentum and positive
Minkowski square. This equivalence also tests the points H = 0. -/
theorem future_iff (p : MassiveParameters) {σ : ℝ} (hσ : 0 < σ) (y : Spatial) :
    (0 < normalMomentum (action p σ) (slicePoint 0 y) ∧
      0 < minkowski (phaseDifferential (action p σ) (slicePoint 0 y))
        (phaseDifferential (action p σ) (slicePoint 0 y))) ↔ 0 < coefficient p σ y := by
  have he : 0 < normalMomentum (action p σ) (slicePoint 0 y) ↔ 0 < coefficient p σ y := by
    rw [normal_momentum p hσ y, mul_pos_iff_of_pos_left p.hbar_pos,
      div_pos_iff_of_pos_right (amplitude_pos σ y)]
  refine ⟨fun h => he.mp h.1, fun h => ⟨he.mpr h, ?_⟩⟩
  have hn : phaseDifferential (action p σ) (slicePoint 0 y) 0 < 0 := neg_pos.mp (he.mpr h)
  unfold minkowski
  simp only [show phaseDifferential (action p σ) (slicePoint 0 y) 1 = 0 from phase_spatial p hσ y 0,
    show phaseDifferential (action p σ) (slicePoint 0 y) 2 = 0 from phase_spatial p hσ y 1,
    show phaseDifferential (action p σ) (slicePoint 0 y) 3 = 0 from phase_spatial p hσ y 2,
    zero_mul, sub_zero]
  exact mul_pos_of_neg_of_neg hn hn

/-- On the future-timelike region, the physical dilatation vanishes by the local
Klein–Gordon balance with zero real normal amplitude rate and positive phase rate H/R. -/
theorem dilatation_zero (p : MassiveParameters) {σ : ℝ} (hσ : 0 < σ) (y : Spatial)
    (hy : 0 < coefficient p σ y) :
    dilatation p.c (action p σ) (slicePoint 0 y) = 0 := by
  obtain ⟨hr, hs, hp⟩ := regularity p hσ y
  have hkg := massive_klein_gordon p hσ (slicePoint 0 y)
  have hd := gaussian_dilatation p σ 0 (coefficient p σ y / amplitude σ y) hσ
    (div_pos hy (amplitude_pos σ y)) (initial_wave p hσ) y (hr.of_le (by simp))
    (hs.of_le (by simp)) hp (initial_slope p hσ y) (by simpa only [GaussianGlobalCauchyData.reconstruct] using hkg)
  simpa only [mul_zero] using hd.2.2

end FoliationQM.GaussianPacketPolarDomain
