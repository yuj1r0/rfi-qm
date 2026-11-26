module

public import FoliationQM.GaussianCompactOsmoticMargin
public import FoliationQM.GaussianCenterDilatation

/-!
# Failure of a common Gaussian coercivity interval on shrinking balls

V13 Eqs. 57–58 involve separate spatial and normal derivatives. The regular
positive-frequency packet has zero spatial score at its center by parity.
At nearby positive times its nonzero normal derivative and positive material
dilatation persist on sufficiently small spatial balls around that point.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.GaussianShrinkingBallFailure

open Set MeasureTheory Filter Metric LorentzCoordinates GaussianPacketPolarDomain
open GaussianPacketTimeRegularity OsmoticSliceFields ObserverFluxDensity GaussianPrescribedRegion
open GaussianPacketLaboratoryInterval WeightedOsmoticCoercivity SpacelikeOsmoticIntegral
open scoped Topology

private theorem positive_integral {K : Set Spatial} (hm : MeasurableSet K) (hv : 0 < volume K)
    {f : Spatial → ℝ} (hi : IntegrableOn f K) (hpos : ∀ y ∈ K, 0 < f y) :
    0 < ∫ y in K, f y := by
  have hf : 0 ≤ᵐ[volume.restrict K] f := by
    filter_upwards [ae_restrict_mem hm] with y hy using (hpos y hy).le
  have hsup : Function.support f ∩ K = K := inter_eq_right.mpr (fun y hy => (hpos y hy).ne')
  rwa [setIntegral_pos_iff_support_of_nonneg_ae hf hi, hsup]

/-- If local dilatation exceeds c times the score, the weighted norms on a
positive-volume compact future slice satisfy the reversed strict inequality. -/
theorem reversed_on_compact (p : MassiveParameters) {σ : ℝ} (hσ : 0 < σ) (τ : ℝ)
    {K : Set Spatial} (hK : IsCompact K) (hv : 0 < volume K)
    (hd : ∀ y ∈ K, slicePoint (p.c*τ) y ∈ domain p σ)
    (hcomp : ∀ y ∈ K, p.c * scoreMagnitude (density p σ) (p.c*τ) y <
      dilatation p.c (action p σ) (slicePoint (p.c*τ) y)) :
    p.c * scoreNorm p σ K τ < dilatationNorm p σ K τ := by
  let s := p.c*τ
  let r := density p σ ∘ slicePoint s
  let G := scoreMagnitude (density p σ) s
  let D := dilatation p.c (action p σ) ∘ slicePoint s
  have hc := (SpatialFisherEnergy.contDiff_slicePoint s 1).continuous
  have hF (y : Spatial) (hy : y ∈ K) := fields p hσ (hd y hy)
  have hr : ContinuousOn r K :=
    fun y hy => ((hF y hy).density_smooth.continuousAt.comp hc.continuousAt).continuousWithinAt
  have hG : ContinuousOn G K :=
    fun y hy => ((hF y hy).score_continuous.comp hc.continuousAt).continuousWithinAt
  have hD : ContinuousOn D K :=
    fun y hy => ((hF y hy).dilatation_smooth.continuousAt.comp hc.continuousAt).continuousWithinAt
  have hiG : IntegrableOn (fun y => r y * (G y)^2) K := (hr.mul (hG.pow 2)).integrableOn_compact hK
  have hiD : IntegrableOn (fun y => r y * (D y)^2) K := (hr.mul (hD.pow 2)).integrableOn_compact hK
  have hn : 0 ≤ᵐ[volume.restrict K] r := by
    filter_upwards [ae_restrict_mem hK.measurableSet] with y hy using (hF y hy).density_pos.le
  have hN1 : 0 ≤ p.c * weightedNorm (volume.restrict K) r G :=
    mul_nonneg p.c_pos.le (Real.sqrt_nonneg _)
  have hN2 : 0 ≤ weightedNorm (volume.restrict K) r D := Real.sqrt_nonneg _
  apply (sq_lt_sq₀ hN1 hN2).mp
  rw [mul_pow, weightedNorm_sq hn, weightedNorm_sq hn, ← sub_pos, ← integral_const_mul,
    ← integral_sub hiD (hiG.const_mul (p.c^2))]
  apply positive_integral hK.measurableSet hv (hiD.sub (hiG.const_mul _))
  intro y hy
  have hg : 0 ≤ G y := Real.sqrt_nonneg _
  have hlt : p.c * G y < D y := hcomp y hy
  have hp : 0 < r y := (hF y hy).density_pos
  have hsq := (sq_lt_sq₀ (mul_nonneg p.c_pos.le hg) ((mul_nonneg p.c_pos.le hg).trans hlt.le)).mpr hlt
  have hm := mul_lt_mul_of_pos_left hsq hp
  dsimp only [Pi.sub_apply]
  nlinarith only [hm]

/-- If the negative normal log-score exceeds the spatial score in magnitude on
a compact positive-volume future slice, the physical signed osmotic integral is positive. -/
theorem signed_positive_on_compact (p : MassiveParameters) {σ : ℝ} (hσ : 0 < σ) (τ : ℝ)
    {K : Set Spatial} (hK : IsCompact K) (hv : 0 < volume K)
    (hd : ∀ y ∈ K, slicePoint (p.c*τ) y ∈ domain p σ)
    (hcomp : ∀ y ∈ K, scoreMagnitude (density p σ) (p.c*τ) y <
      -normalScore (density p σ) (slicePoint (p.c*τ) y)) :
    0 < signedIntegral p σ (p.c*τ) K := by
  let s := p.c*τ
  let r := density p σ ∘ slicePoint s
  let G := scoreMagnitude (density p σ) s
  let N := normalScore (density p σ) ∘ slicePoint s
  have hc := (SpatialFisherEnergy.contDiff_slicePoint s 1).continuous
  have hF (y : Spatial) (hy : y ∈ K) := fields p hσ (hd y hy)
  have hr : ContinuousOn r K :=
    fun y hy => ((hF y hy).density_smooth.continuousAt.comp hc.continuousAt).continuousWithinAt
  have hG : ContinuousOn G K :=
    fun y hy => ((hF y hy).score_continuous.comp hc.continuousAt).continuousWithinAt
  have hN : ContinuousOn N K :=
    fun y hy => ((hF y hy).normal_score_smooth.continuousAt.comp hc.continuousAt).continuousWithinAt
  let f := fun y => r y * ((p.hbar^2/4) * ((N y)^2 - (G y)^2))
  have hEq : signedIntegral p σ s K = ∫ y in K, f y := by
    apply integral_congr_ae
    filter_upwards with y
    simp only [f, r, G, N, Function.comp_apply, info_square, scoreMagnitude, euclideanSpeed_sq]
  rw [show p.c*τ = s from rfl, hEq]
  have hi : IntegrableOn f K :=
    (hr.mul (continuousOn_const.mul ((hN.pow 2).sub (hG.pow 2)))).integrableOn_compact hK
  apply positive_integral hK.measurableSet hv hi
  intro y hy
  have hg : 0 ≤ G y := Real.sqrt_nonneg _
  have hn : G y < -N y := hcomp y hy
  have hsq := (sq_lt_sq₀ hg (hg.trans hn.le)).mpr hn
  dsimp only [f]
  exact mul_pos (hF y hy).density_pos (mul_pos (div_pos (sq_pos_of_pos p.hbar_pos) (by norm_num))
    (by nlinarith only [hsq]))

/-- A compact spatial cell is initially future and is still regular and subluminal
at the indicated time, while its strict weighted comparison has reversed and its
signed integral has passed from negative at time zero to positive. -/
structure FailureOn (p : MassiveParameters) (σ τ : ℝ) (K : Set Spatial) : Prop where
  initial_future : K ⊆ GaussianRegionalCoercivity.futureRegion p σ
  regular : ∀ y ∈ K, slicePoint (p.c*τ) y ∈ domain p σ
  speed_lt : ∀ y ∈ K, euclideanSpeed (phaseDrift p.c (action p σ) (slicePoint (p.c*τ) y)) < p.c/2
  reverse : p.c * scoreNorm p σ K τ < dilatationNorm p σ K τ
  initial_negative : signedIntegral p σ 0 K < 0
  signed_positive : 0 < signedIntegral p σ (p.c*τ) K

/-- Reversal of the weighted comparison rules out Eq. 57 for every nonnegative
speed cap, including the largest possible right-hand side at V=0. -/
theorem FailureOn.not_bound {p : MassiveParameters} {σ τ : ℝ} {K : Set Spatial}
    (h : FailureOn p σ τ K) {V : ℝ} (hV : 0 ≤ V) :
    ¬ GaussianPacketTimeCoercivity.DilatationBoundOn p σ (p.c*τ) K V := by
  have hg : 0 ≤ scoreNorm p σ K τ := Real.sqrt_nonneg _
  exact (h.reverse.le.trans' (mul_le_mul_of_nonneg_right (sub_le_self _ hV) hg)).not_gt

private theorem balls_of_center (p : MassiveParameters) {σ : ℝ} (hσ : 0 < σ)
    (τ : ℝ) {R δ : ℝ} (hR : 0 < R)
    (hf : closedBall (0 : Spatial) R ⊆ GaussianRegionalCoercivity.futureRegion p σ)
    (tube : GaussianCompactFutureTube.Tube p σ δ (closedBall (0 : Spatial) R))
    (ht : τ ∈ Icc (-δ) δ)
    (hG₀ : spatialScore (density p σ) (slicePoint (p.c*τ) 0) = 0)
    (hN₀ : normalScore (density p σ) (slicePoint (p.c*τ) 0) < 0)
    (hD₀ : 0 < dilatation p.c (action p σ) (slicePoint (p.c*τ) 0)) :
    ∃ b : ℝ, 0 < b ∧ ∀ r ∈ Ioc 0 b, FailureOn p σ τ (closedBall (0 : Spatial) r) := by
  let x := slicePoint (p.c*τ)
  let G := scoreMagnitude (density p σ) (p.c*τ)
  let N := normalScore (density p σ) ∘ x
  let D := dilatation p.c (action p σ) ∘ x
  have hc := (SpatialFisherEnergy.contDiff_slicePoint (p.c*τ) 1).continuous.continuousAt (x := 0)
  have hF := fields p hσ (tube.in_domain τ ht 0 (mem_closedBall_self hR.le))
  have hG : ContinuousAt G 0 := hF.score_continuous.comp hc
  have hN : ContinuousAt N 0 := hF.normal_score_smooth.continuousAt.comp hc
  have hD : ContinuousAt D 0 := hF.dilatation_smooth.continuousAt.comp hc
  have hg₀ : G 0 = 0 := by simp [G, scoreMagnitude, hG₀, euclideanSpeed, speedSq, spatialDot]
  have hd₀ : p.c * G 0 < D 0 := by rw [hg₀,mul_zero]; exact hD₀
  have hn₀ : G 0 < -N 0 := by rw [hg₀]; exact neg_pos.mpr hN₀
  have hnear : ∀ᶠ y in 𝓝 (0 : Spatial), p.c * G y < D y ∧ G y < -N y :=
    ((continuousAt_const.mul hG).eventually_lt hD hd₀).and (hG.eventually_lt hN.neg hn₀)
  obtain ⟨b,hb,hball⟩ := nhds_basis_closedBall.mem_iff.mp hnear
  refine ⟨min b R, lt_min hb hR, fun r hr => ?_⟩
  have hsmall : closedBall (0 : Spatial) r ⊆ closedBall 0 b :=
    closedBall_subset_closedBall (hr.2.trans (min_le_left _ _))
  have hrad : closedBall (0 : Spatial) r ⊆ closedBall 0 R :=
    closedBall_subset_closedBall (hr.2.trans (min_le_right _ _))
  have hreg (y : Spatial) (hy : y ∈ closedBall (0 : Spatial) r) := tube.in_domain τ ht y (hrad hy)
  have hv := measure_closedBall_pos (volume : Measure Spatial) (0 : Spatial) hr.1
  have hK := isCompact_closedBall (0 : Spatial) r
  exact ⟨hrad.trans hf, hreg, fun y hy => tube.speed_lt τ ht y (hrad hy),
    reversed_on_compact p hσ τ hK hv hreg (fun _ hy => (hball (hsmall hy)).1),
    GaussianPacketOsmoticIntegral.integral_neg_on p hσ hv,
    signed_positive_on_compact p hσ τ hK hv hreg (fun _ hy => (hball (hsmall hy)).2)⟩

/-- At all sufficiently small positive laboratory times, all sufficiently small
positive-radius centered balls reverse the weighted comparison and have positive
signed osmotic integral while remaining regular and uniformly subluminal. -/
theorem eventually_failing_balls (p : MassiveParameters) {σ : ℝ} (hσ : 0 < σ) :
    ∀ᶠ τ : ℝ in 𝓝[>] 0, ∃ b : ℝ, 0 < b ∧ ∀ r ∈ Ioc 0 b,
      FailureOn p σ τ (closedBall (0 : Spatial) r) := by
  have hf := (GaussianRegionalCoercivity.futureRegion_open p hσ).mem_nhds
    (GaussianRegionalCoercivity.center_mem_futureRegion p hσ)
  obtain ⟨R,hR,hsub⟩ := nhds_basis_closedBall.mem_iff.mp hf
  obtain ⟨δ,hδ,tube⟩ := GaussianCompactFutureTube.exists_tube p hσ (isCompact_closedBall 0 R) hsub
  have ht : Icc (-δ) δ ∈ 𝓝[>] (0 : ℝ) := nhdsWithin_le_nhds (Icc_mem_nhds (neg_lt_zero.mpr hδ) hδ)
  filter_upwards [ht,GaussianCenterDilatation.eventually_positive_time p hσ] with τ hτ h
  exact balls_of_center p hσ τ hR hsub tube hτ h.2.1 h.2.2.1 h.2.2.2

/-- An arbitrarily short positive laboratory time and arbitrarily small initially
future centered ball realize a strict reversal of Eq. 57 and opposite signs of
the ball's signed osmotic integral at time zero and at the chosen time. -/
theorem arbitrarily_early_failure (p : MassiveParameters) {σ : ℝ} (hσ : 0 < σ)
    {T R : ℝ} (hT : 0 < T) (hR : 0 < R) :
    ∃ τ ∈ Ioo (0 : ℝ) T, ∃ r ∈ Ioo (0 : ℝ) R, FailureOn p σ τ (closedBall (0 : Spatial) r) := by
  have hτ : ∀ᶠ τ : ℝ in 𝓝[>] 0, τ ∈ Ioo 0 T :=
    Filter.Eventually.and self_mem_nhdsWithin (nhdsWithin_le_nhds (Iio_mem_nhds hT))
  obtain ⟨τ,ht,b,hb,hballs⟩ := (hτ.and (eventually_failing_balls p hσ)).exists
  let r := min b R / 2
  have hrs : 0 < r := half_pos (lt_min hb hR)
  have hsmall : r < min b R := half_lt_self (lt_min hb hR)
  exact ⟨τ, ht, r, ⟨hrs,hsmall.trans_le (min_le_right _ _)⟩,
    hballs r ⟨hrs,(hsmall.trans_le (min_le_left _ _)).le⟩⟩

/-- No common positive laboratory duration gives the strict weighted estimate on
every sufficiently small initially future centered ball, even with speed cap zero. -/
theorem no_common_interval (p : MassiveParameters) {σ : ℝ} (hσ : 0 < σ)
    {T R : ℝ} (hT : 0 < T) (hR : 0 < R) :
    ¬ (∀ r ∈ Ioo (0 : ℝ) R, closedBall (0 : Spatial) r ⊆ GaussianRegionalCoercivity.futureRegion p σ →
        ∀ τ ∈ Icc (-T) T,
          GaussianPacketTimeCoercivity.DilatationBoundOn p σ (p.c*τ) (closedBall (0 : Spatial) r) 0) := by
  intro hall
  obtain ⟨τ,hτ,r,hr,hfail⟩ := arbitrarily_early_failure p hσ hT hR
  exact hfail.not_bound (V := 0) le_rfl
    (hall r hr hfail.initial_future τ ⟨by linarith [hτ.1],hτ.2.le⟩)

end FoliationQM.GaussianShrinkingBallFailure
