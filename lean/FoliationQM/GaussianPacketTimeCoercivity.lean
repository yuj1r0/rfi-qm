module

public import FoliationQM.GaussianRegionalCoercivity
public import FoliationQM.GaussianPacketTimeWindow

/-!
# Persistence of the Gaussian dilatation bound on a fixed laboratory region

The strict estimate in v13 Eq. 57 uses the actual density, spatial score and
material dilatation on the same slice. A positive-measure cell permits a
uniform pointwise comparison to be integrated with a strict margin.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.GaussianPacketTimeCoercivity

open MeasureTheory LorentzCoordinates OsmoticSliceFields ObserverFluxDensity
open WeightedOsmoticCoercivity SpacelikeOsmoticIntegral GaussianPacketPolarDomain

/-- A positive spatial score and density on a positive-volume cell give a strictly
positive weighted score norm. A uniform pointwise rate bound there controls the
weighted dilatation norm with the same coefficient. -/
theorem weighted_control {A : Set Spatial} (hA : MeasurableSet A) (hvol : 0 < volume A)
    {r D G : Spatial → ℝ} {q : ℝ} (hq : 0 ≤ q)
    (hr : ∀ y ∈ A, 0 < r y) (hG : ∀ y ∈ A, 0 < G y)
    (hD : ∀ y ∈ A, |D y| ≤ q * G y)
    (hiG : IntegrableOn (fun y => r y * (G y)^2) A)
    (hiD : IntegrableOn (fun y => r y * (D y)^2) A) :
    0 < weightedNorm (volume.restrict A) r G ∧
      weightedNorm (volume.restrict A) r D ≤ q * weightedNorm (volume.restrict A) r G := by
  have hr' : ∀ᵐ y ∂volume.restrict A, 0 ≤ r y := by
    filter_upwards [ae_restrict_mem hA] with y hy using (hr y hy).le
  have hpos (y : Spatial) (hy : y ∈ A) : 0 < r y * (G y)^2 :=
    mul_pos (hr y hy) (sq_pos_of_pos (hG y hy))
  have hs : Function.support (fun y => r y * (G y)^2) ∩ A = A :=
    Set.inter_eq_right.mpr (fun y hy => (hpos y hy).ne')
  constructor
  · apply Real.sqrt_pos.mpr
    have hf : ∀ᵐ y ∂volume.restrict A, 0 ≤ r y * (G y)^2 := by
      filter_upwards [ae_restrict_mem hA] with y hy using (hpos y hy).le
    rwa [setIntegral_pos_iff_support_of_nonneg_ae hf hiG, hs]
  · have hnD : 0 ≤ weightedNorm (volume.restrict A) r D := Real.sqrt_nonneg _
    have hnG : 0 ≤ weightedNorm (volume.restrict A) r G := Real.sqrt_nonneg _
    apply (sq_le_sq₀ hnD (mul_nonneg hq hnG)).mp
    rw [mul_pow, weightedNorm_sq hr', weightedNorm_sq hr']
    calc
      _ ≤ ∫ y in A, q^2 * (r y * (G y)^2) := by
        apply setIntegral_mono_on hiD (hiG.const_mul _) hA
        intro y hy
        have h := (sq_le_sq₀ (abs_nonneg (D y)) (mul_nonneg hq (hG y hy).le)).mpr (hD y hy)
        rw [sq_abs, mul_pow] at h
        calc
          _ ≤ r y * (q^2 * (G y)^2) := mul_le_mul_of_nonneg_left h (hr y hy).le
          _ = _ := by ring
      _ = _ := integral_const_mul _ _

/-- The source's weighted inequality for the actual positive-frequency packet on a
fixed spatial region at normal time t=ct_lab and prescribed speed bound V. -/
def DilatationBoundOn (p : MassiveParameters) (σ t : ℝ) (A : Set Spatial) (V : ℝ) : Prop :=
  weightedNorm (volume.restrict A) (density p σ ∘ slicePoint t)
      (dilatation p.c (action p σ) ∘ slicePoint t) <
    (p.c - V) * weightedNorm (volume.restrict A) (density p σ ∘ slicePoint t)
      (scoreMagnitude (density p σ) t)

/-- The time-dependent inequality at zero time agrees with the initial-slice comparison. -/
theorem at_initial_time (p : MassiveParameters) (σ : ℝ) (A : Set Spatial) (V : ℝ) :
    DilatationBoundOn p σ 0 A V ↔ GaussianRegionalCoercivity.DilatationBoundOn p σ A V := Iff.rfl

open GaussianPacketTimeWindow

/-- The two weighted squares in Eq. 57 are Lebesgue integrable on any compact
spatial slice on which the packet satisfies the window bounds. -/
theorem integrable_squares (p : MassiveParameters) (σ t : ℝ) {K : Set Spatial} (hc : IsCompact K)
    (hb : ∀ y ∈ K, PointBounds p σ (slicePoint t y)) :
    IntegrableOn (fun y => density p σ (slicePoint t y) * (scoreMagnitude (density p σ) t y)^2) K ∧
    IntegrableOn (fun y => density p σ (slicePoint t y) * (dilatation p.c (action p σ) (slicePoint t y))^2) K := by
  have hs := (SpatialFisherEnergy.contDiff_slicePoint t 1).continuous
  have hr : ContinuousOn (density p σ ∘ slicePoint t) K :=
    fun y hy => ((hb y hy).density_smooth.continuousAt.comp hs.continuousAt).continuousWithinAt
  have hG : ContinuousOn (scoreMagnitude (density p σ) t) K :=
    fun y hy => ((hb y hy).score_continuous.comp hs.continuousAt).continuousWithinAt
  have hD : ContinuousOn (dilatation p.c (action p σ) ∘ slicePoint t) K :=
    fun y hy => ((hb y hy).dilatation_smooth.continuousAt.comp hs.continuousAt).continuousWithinAt
  exact ⟨(hr.mul (hG.pow 2)).integrableOn_compact hc, (hr.mul (hD.pow 2)).integrableOn_compact hc⟩

/-- On each measurable positive-volume part of a compact window slice the
weighted spatial norm is positive, and the dilatation norm is at most c/4 times it. -/
theorem quarter_bound_on_subset (p : MassiveParameters) (σ t : ℝ) {K A : Set Spatial}
    (hc : IsCompact K) (hb : ∀ y ∈ K, PointBounds p σ (slicePoint t y))
    (hA : MeasurableSet A) (hAK : A ⊆ K) (hvol : 0 < volume A) :
    let μ := volume.restrict A
    let r := density p σ ∘ slicePoint t
    0 < weightedNorm μ r (scoreMagnitude (density p σ) t) ∧
      weightedNorm μ r (dilatation p.c (action p σ) ∘ slicePoint t) ≤
        (p.c/4) * weightedNorm μ r (scoreMagnitude (density p σ) t) := by
  obtain ⟨hiG, hiD⟩ := integrable_squares p σ t hc hb
  apply weighted_control hA hvol (div_nonneg p.c_pos.le (by norm_num))
  · exact fun y hy => (hb y (hAK hy)).density_pos
  · exact fun y hy => (hb y (hAK hy)).score_pos
  · exact fun y hy => (hb y (hAK hy)).dilatation_lt.le
  · exact hiG.mono_set hAK
  · exact hiD.mono_set hAK

/-- The actual regional drift-speed supremum is at most c/2, and the manuscript's
strict inequality follows with that same speed cap and the actual packet fields. -/
theorem strict_on_subset (p : MassiveParameters) (σ t : ℝ) {K A : Set Spatial}
    (hc : IsCompact K) (hb : ∀ y ∈ K, PointBounds p σ (slicePoint t y))
    (hA : MeasurableSet A) (hAK : A ⊆ K) (hvol : 0 < volume A) :
    (⨆ y : A, euclideanSpeed (phaseDrift p.c (action p σ) (slicePoint t y.val))) ≤ p.c/2 ∧
      DilatationBoundOn p σ t A (p.c/2) := by
  obtain ⟨hG,hD⟩ := quarter_bound_on_subset p σ t hc hb hA hAK hvol
  obtain ⟨y,hy⟩ := nonempty_of_measure_ne_zero hvol.ne'
  let : Nonempty A := ⟨⟨y,hy⟩⟩
  refine ⟨ciSup_le fun z => (hb z.val (hAK z.property)).speed_lt.le, ?_⟩
  apply lt_of_le_of_lt hD
  exact mul_lt_mul_of_pos_right (by linarith [p.c_pos] : p.c/4 < p.c - p.c/2) hG

/-- For every positive Gaussian width there is a single fixed closed spatial ball
of positive volume and a two-sided time interval of positive length. On every
slice in this interval the positive-frequency packet obeys the strict weighted
dilatation inequality with uniform drift-speed bound c/2. -/
theorem exists_fixed_ball_interval (p : MassiveParameters) {σ : ℝ} (hσ : 0 < σ) :
    ∃ (y₀ : Spatial) (r : ℝ), 0 < r ∧ 0 < volume (Metric.closedBall y₀ r) ∧
      ∀ t ∈ Set.Icc (-r) r,
        (⨆ y : Metric.closedBall y₀ r,
          euclideanSpeed (phaseDrift p.c (action p σ) (slicePoint t y.val))) ≤ p.c/2 ∧
        DilatationBoundOn p σ t (Metric.closedBall y₀ r) (p.c/2) := by
  obtain ⟨y₀,r,hr,hwin⟩ := exists_window p hσ
  have hv := Metric.measure_closedBall_pos (volume : Measure Spatial) y₀ hr
  refine ⟨y₀,r,hr,hv, fun t ht => ?_⟩
  exact strict_on_subset p σ t (isCompact_closedBall y₀ r) (hwin t ht)
    Metric.isClosed_closedBall.measurableSet Set.Subset.rfl hv

end FoliationQM.GaussianPacketTimeCoercivity
