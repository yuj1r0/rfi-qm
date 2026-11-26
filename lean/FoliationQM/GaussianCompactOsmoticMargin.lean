module

public import FoliationQM.GaussianPrescribedRegion
public import FoliationQM.GaussianPacketOsmoticIntegral

/-!
# Uniform signed osmotic margin on a prescribed spatial region

For the actual rest packet, v13 Eq. 58 defines a continuous function of
laboratory time on compact future cylinders. A fixed fraction of the
initial strictly negative integral bounds it throughout a shorter interval.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.GaussianCompactOsmoticMargin

open Set MeasureTheory LorentzCoordinates GaussianPacketPolarDomain GaussianCompactFutureTube
open GaussianPacketTimeRegularity GaussianPacketLaboratoryInterval OsmoticSliceFields
open scoped Topology

/-- On a compact future cylinder the signed osmotic integral on its fixed spatial
section varies continuously in laboratory time. -/
theorem continuous_signed (p : MassiveParameters) {σ : ℝ} (hσ : 0 < σ)
    {I : Set ℝ} {K : Set Spatial} (hI : IsCompact I) (hK : IsCompact K)
    (hdom : ∀ τ ∈ I, ∀ y ∈ K, slicePoint (p.c*τ) y ∈ domain p σ) :
    ContinuousOn (fun τ => signedIntegral p σ (p.c*τ) K) I := by
  let f := fun z : ℝ × Spatial => p.hbar^2/4 * (normalSquare p σ z - spatialSquare p σ z)
  have hf : ContinuousOn f (I ×ˢ K) :=
    continuousOn_const.mul ((continuous_normalSquare_on p hσ hdom).sub (continuous_spatialSquare_on p hσ hdom))
  have hc := GaussianCompactSliceMoments.continuousOn_integral hI hK hf
  apply hc.congr
  intro τ _
  change (∫ y in K, _) = ∫ y in K, f (τ,y)
  apply integral_congr_ae
  filter_upwards with y
  simp only [f, normalSquare, spatialSquare, massWeight, sliceMap,
    info_square, euclideanSpeed_sq]
  ring

/-- Every prescribed compact positive-volume part of the initial future region
retains at least half its initial negative osmotic margin in a nonzero time interval. -/
theorem uniform_signed_margin (p : MassiveParameters) {σ : ℝ} (hσ : 0 < σ) {K : Set Spatial}
    (hK : IsCompact K) (hv : 0 < volume K) (hf : K ⊆ GaussianRegionalCoercivity.futureRegion p σ) :
    ∃ T : ℝ, 0 < T ∧ signedIntegral p σ 0 K / 2 < 0 ∧
      ∀ τ ∈ Icc (-T) T, signedIntegral p σ (p.c*τ) K < signedIntegral p σ 0 K / 2 := by
  obtain ⟨δ,hδ,htube⟩ := exists_tube p hσ hK hf
  have hI : Icc (-δ) δ ∈ 𝓝 (0 : ℝ) := Icc_mem_nhds (neg_lt_zero.mpr hδ) hδ
  have h := continuous_signed p hσ isCompact_Icc hK htube.in_domain
  have hc := (h 0 (mem_of_mem_nhds hI)).continuousAt hI
  have hneg : signedIntegral p σ 0 K < 0 := GaussianPacketOsmoticIntegral.integral_neg_on p hσ hv
  have hlt : signedIntegral p σ (p.c*0) K < signedIntegral p σ 0 K/2 := by
    rw [mul_zero]; linarith
  obtain ⟨T,hT,ht⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hc.eventually_lt_const hlt)
  refine ⟨T,hT,by linarith,fun τ hτ => ht ?_⟩
  simpa [Real.closedBall_eq_Icc] using hτ

end FoliationQM.GaussianCompactOsmoticMargin
