module

public import FoliationQM.GaussianPacketLaboratoryInterval
public import FoliationQM.GaussianCompactSliceMoments

/-!
# Coercivity on a prescribed compact future region

For v13 Eqs. 57–58 the initial weighted score is strictly positive on each
fixed positive-volume spatial set. Its spatial pointwise value can vanish
at the center. The argument uses the time dependence of the actual integrals
on that set and the Klein–Gordon transport identity on its future chart.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.GaussianPrescribedRegion

open MeasureTheory LorentzCoordinates GaussianPacketPolarDomain GaussianPacketTimeRegularity
open OsmoticSliceFields ObserverFluxDensity GaussianPacketTimeCoercivity SpacelikeOsmoticIntegral
open GaussianPacketLaboratoryInterval WeightedOsmoticCoercivity Filter Set
open scoped Topology

/-- On a compact future slice the speed bound and the actual weighted dilatation
inequality imply strict negativity of the regional osmotic integral via transport. -/
theorem signed_negative_of_bound (p : MassiveParameters) {σ : ℝ} (hσ : 0 < σ)
    (s : ℝ) {K : Set Spatial} (hK : IsCompact K) {V : ℝ} (hV : 0 ≤ V) (hVc : V < p.c)
    (hdom : ∀ y ∈ K, slicePoint s y ∈ domain p σ)
    (hv : ∀ y ∈ K, euclideanSpeed (phaseDrift p.c (action p σ) (slicePoint s y)) ≤ V)
    (hgap : DilatationBoundOn p σ s K V) : signedIntegral p σ s K < 0 := by
  have hd (y : Spatial) (hy : y ∈ K) := fields p hσ (hdom y hy)
  have hc := (SpatialFisherEnergy.contDiff_slicePoint s 1).continuous
  have hr : ContinuousOn (density p σ ∘ slicePoint s) K :=
    fun y hy => ((hd y hy).density_smooth.continuousAt.comp hc.continuousAt).continuousWithinAt
  have hN : ContinuousOn (normalScore (density p σ) ∘ slicePoint s) K :=
    fun y hy => ((hd y hy).normal_score_smooth.continuousAt.comp hc.continuousAt).continuousWithinAt
  have hD : ContinuousOn (dilatation p.c (action p σ) ∘ slicePoint s) K :=
    fun y hy => ((hd y hy).dilatation_smooth.continuousAt.comp hc.continuousAt).continuousWithinAt
  have hG : ContinuousOn (scoreMagnitude (density p σ) s) K :=
    fun y hy => ((hd y hy).score_continuous.comp hc.continuousAt).continuousWithinAt
  have hm := hK.measurableSet
  apply (integral_spacelike p (density p σ) (action p σ) s K hV hVc _ _ _
    ((hr.mul (hN.pow 2)).aestronglyMeasurable hm)
    ((hr.mul (hG.pow 2)).integrableOn_compact hK)
    ((hr.mul (hD.pow 2)).integrableOn_compact hK) hgap).2
  · filter_upwards [ae_restrict_mem hm] with y hy using (hd y hy).density_pos.le
  · filter_upwards [ae_restrict_mem hm] with y hy using transport p hσ (hdom y hy)
  · filter_upwards [ae_restrict_mem hm] with y hy using hv y hy

/-- A zero initial dilatation norm and a positive initial score norm have a common
two-sided interval with a strict quarter-speed comparison and a fixed positive
lower bound for the score, whenever both norms are continuous on the original interval. -/
theorem persist_norms {G D : ℝ → ℝ} {δ c : ℝ} (hδ : 0 < δ) (hc : 0 < c)
    (hD : ContinuousOn D (Icc (-δ) δ)) (hG : ContinuousOn G (Icc (-δ) δ))
    (hd : D 0 = 0) (hg : 0 < G 0) :
    ∃ T : ℝ, 0 < T ∧ ∀ τ ∈ Icc (-T) T, τ ∈ Icc (-δ) δ ∧
      G 0 / 2 < G τ ∧ D τ < c / 4 * G τ := by
  have hI : Icc (-δ) δ ∈ 𝓝 (0 : ℝ) := Icc_mem_nhds (neg_lt_zero.mpr hδ) hδ
  have h0 : (0 : ℝ) ∈ Icc (-δ) δ := mem_of_mem_nhds hI
  have hg' := (hG 0 h0).continuousAt hI
  have hd' := (hD 0 h0).continuousAt hI
  have hs : ∀ᶠ τ in 𝓝 (0 : ℝ), G 0 / 2 < G τ :=
    continuousAt_const.eventually_lt hg' (half_lt_self hg)
  have hgap : ∀ᶠ τ in 𝓝 (0 : ℝ), D τ < c / 4 * G τ :=
    hd'.eventually_lt (continuousAt_const.mul hg') (by rw [hd]; positivity)
  have hall : ∀ᶠ τ in 𝓝 (0 : ℝ),
      τ ∈ Icc (-δ) δ ∧ G 0 / 2 < G τ ∧ D τ < c / 4 * G τ :=
    Filter.Eventually.and hI (hs.and hgap)
  obtain ⟨ε,hε,hsub⟩ := Metric.mem_nhds_iff.mp hall
  refine ⟨ε/2, half_pos hε, fun τ hτ => hsub ?_⟩
  rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt]
  constructor <;> linarith [hτ.1,hτ.2]

/-- Weighted spatial log-score of the physical packet on K at laboratory time τ. -/
abbrev scoreNorm (p : MassiveParameters) (σ : ℝ) (K : Set Spatial) (τ : ℝ) : ℝ :=
  weightedNorm (volume.restrict K) (density p σ ∘ slicePoint (p.c*τ))
    (scoreMagnitude (density p σ) (p.c*τ))

/-- Weighted full material dilatation of the physical packet on K at laboratory time τ. -/
abbrev dilatationNorm (p : MassiveParameters) (σ : ℝ) (K : Set Spatial) (τ : ℝ) : ℝ :=
  weightedNorm (volume.restrict K) (density p σ ∘ slicePoint (p.c*τ))
    (dilatation p.c (action p σ) ∘ slicePoint (p.c*τ))

/-- On every prescribed compact positive-volume portion of the initial future
region there is a two-sided laboratory interval on which the actual drift supremum
is at most c/2, the strict Eq. 57 bound holds with a uniform norm margin, and the
signed Eq. 58 integral is negative. The chosen region may include the center. -/
theorem interval (p : MassiveParameters) {σ : ℝ} (hσ : 0 < σ) {K : Set Spatial}
    (hK : IsCompact K) (hvol : 0 < volume K) (hfuture : K ⊆ GaussianRegionalCoercivity.futureRegion p σ) :
    ∃ T : ℝ, 0 < T ∧ ∀ τ ∈ Icc (-T) T,
      scoreNorm p σ K 0 / 2 < scoreNorm p σ K τ ∧
      dilatationNorm p σ K τ < (p.c/4)*scoreNorm p σ K τ ∧
      (⨆ y : K, euclideanSpeed (phaseDrift p.c (action p σ) (slicePoint (p.c*τ) y.val))) ≤ p.c/2 ∧
      DilatationBoundOn p σ (p.c*τ) K (p.c/2) ∧ signedIntegral p σ (p.c*τ) K < 0 := by
  obtain ⟨δ,hδ,tube⟩ := GaussianCompactFutureTube.exists_tube p hσ hK hfuture
  obtain ⟨hD,hG,_⟩ := GaussianCompactSliceMoments.norms_continuousOn p hσ isCompact_Icc hK tube.in_domain
  obtain ⟨hd,hg,_⟩ := GaussianCompactSliceMoments.initial_norms p hσ hvol hfuture
  have hzero : dilatationNorm p σ K 0 = 0 := by simpa only [dilatationNorm, mul_zero] using hd
  have hpos : 0 < scoreNorm p σ K 0 := by simpa only [scoreNorm, mul_zero] using hg
  obtain ⟨T,hT,hmargin⟩ := persist_norms (D := dilatationNorm p σ K) (G := scoreNorm p σ K)
    hδ p.c_pos hD hG hzero hpos
  refine ⟨T,hT,fun τ hτ => ?_⟩
  obtain ⟨hδτ,hGτ,hDτ⟩ := hmargin τ hτ
  have hs (y : Spatial) (hy : y ∈ K) := (tube.speed_lt τ hδτ y hy).le
  have hgap : DilatationBoundOn p σ (p.c*τ) K (p.c/2) :=
    hDτ.trans (mul_lt_mul_of_pos_right (by linarith [p.c_pos] : p.c/4 < p.c - p.c/2)
      ((half_pos hpos).trans hGτ))
  obtain ⟨y,hy⟩ := nonempty_of_measure_ne_zero hvol.ne'
  let : Nonempty K := ⟨⟨y,hy⟩⟩
  exact ⟨hGτ,hDτ,ciSup_le (fun z => hs z.val z.property),hgap,
    signed_negative_of_bound p hσ _ hK (by linarith [p.c_pos]) (by linarith [p.c_pos])
      (tube.in_domain τ hδτ) hs hgap⟩

end FoliationQM.GaussianPrescribedRegion
