module

public import FoliationQM.GaussianPacketPolarDomain
public import FoliationQM.DeBroglieLimit

/-!
# Spacetime regularity of the Gaussian packet on its future phase chart

The weighted bound in v13 Theorem 5.8(ii), lines 752–767, uses the actual
dilatation and logarithmic density gradient. We control their spacetime
regularity on the intersection of the packet's logarithm chart and its
future-timelike phase domain.
-/

@[expose] public section
noncomputable section

namespace FoliationQM.GaussianPacketTimeRegularity

open LorentzCoordinates GaussianPacketPolarDomain OsmoticSliceFields ObserverFluxDensity
open DressedMassDensityVariation LogDensityTransport
open scoped ContDiff Topology

/-- Points where the packet has a regular logarithm chart, future normal phase
momentum and strictly timelike phase differential. -/
def domain (p : MassiveParameters) (σ : ℝ) : Set Covector :=
  {x | wave p σ x ∈ PolarLocalInverse.chartDomain 1 ∧
    0 < normalMomentum (action p σ) x ∧
    0 < minkowski (phaseDifferential (action p σ) x) (phaseDifferential (action p σ) x)}

/-- Local spacetime regularity of the physical fields entering the drift,
Fisher and weighted dilatation estimates. -/
structure Fields (p : MassiveParameters) (σ : ℝ) (x : Covector) : Prop where
  density_pos : 0 < density p σ x
  normal_pos : 0 < normalMomentum (action p σ) x
  phase_sq_pos : 0 < minkowski (phaseDifferential (action p σ) x) (phaseDifferential (action p σ) x)
  density_smooth : ContDiffAt ℝ ∞ (density p σ) x
  action_smooth : ContDiffAt ℝ ∞ (action p σ) x
  normal_smooth : ContDiffAt ℝ ∞ (normalMomentum (action p σ)) x
  phase_sq_smooth : ContDiffAt ℝ ∞ (fun z => minkowski (phaseDifferential (action p σ) z)
    (phaseDifferential (action p σ) z)) x
  drift_smooth : ContDiffAt ℝ ∞ (phaseDrift p.c (action p σ)) x
  spatial_score_smooth : ContDiffAt ℝ ∞ (spatialScore (density p σ)) x
  normal_score_smooth : ContDiffAt ℝ ∞ (normalScore (density p σ)) x
  dilatation_smooth : ContDiffAt ℝ ∞ (dilatation p.c (action p σ)) x
  speed_continuous : ContinuousAt (fun z => euclideanSpeed (phaseDrift p.c (action p σ) z)) x
  score_continuous : ContinuousAt (fun z => euclideanSpeed (spatialScore (density p σ) z)) x

private theorem smooth_coordinate {f : Covector → ℝ} {x : Covector}
    (hf : ContDiffAt ℝ ∞ f x) (i : Fin 4) :
    ContDiffAt ℝ ∞ (fun z => phaseDifferential f z i) x :=
  (hf.fderiv_right (m := ∞) (by simp)).clm_apply contDiffAt_const

private theorem smooth_dilatation {S : Covector → ℝ} {x : Covector} (c : ℝ)
    (ha : ContDiffAt ℝ ∞ (normalMomentum S) x) (hp : normalMomentum S x ≠ 0)
    (hv : ContDiffAt ℝ ∞ (phaseDrift c S) x) : ContDiffAt ℝ ∞ (dilatation c S) x := by
  let v := phaseDrift c S
  have hvi (i : Fin 3) : ContDiffAt ℝ ∞ (fun z => v z i) x := contDiffAt_pi.mp hv i
  have hdiv : ContDiffAt ℝ ∞ (spatialDivergence v) x := by
    change ContDiffAt ℝ ∞ (fun z => ∑ i : Fin 3, phaseDifferential (fun u => v u i) z i.succ) x
    simp only [Fin.sum_univ_three]
    exact ((smooth_coordinate (hvi 0) _).add (smooth_coordinate (hvi 1) _)).add (smooth_coordinate (hvi 2) _)
  have hlog := ha.log hp
  have hmat : ContDiffAt ℝ ∞ (material c v (fun z => Real.log (normalMomentum S z))) x := by
    unfold material spatialDot spatialGradient
    exact (contDiffAt_const.mul (smooth_coordinate hlog 0)).add <|
      (((hvi 0).mul (smooth_coordinate hlog _)).add ((hvi 1).mul (smooth_coordinate hlog _))).add
        ((hvi 2).mul (smooth_coordinate hlog _))
  exact hdiv.add hmat

/-- Throughout this spacetime domain the packet's squared modulus, action,
normal momentum, drift, log scores and full material dilatation are smooth,
and the physical Euclidean drift and score magnitudes are continuous. -/
theorem fields (p : MassiveParameters) {σ : ℝ} (hσ : 0 < σ) {x : Covector}
    (hx : x ∈ domain p σ) : Fields p σ x := by
  obtain ⟨hchart, ha, htime⟩ := hx
  have hψ := (GaussianPositiveFrequencyPacket.smooth_packet (p.m*p.c/p.hbar) hσ).contDiffAt (x := x)
  have hr : ContDiffAt ℝ ∞ (density p σ) x := (PolarLocalInverse.contDiff_normSq ∞).contDiffAt.comp _ hψ
  have hs : ContDiffAt ℝ ∞ (action p σ) x := (PolarLocalInverse.contDiffAt_localAction p hchart ∞).comp _ hψ
  have hp : 0 < density p σ x := PolarLocalInverse.normSq_pos_of_mem_chartDomain hchart
  have hn : ContDiffAt ℝ ∞ (normalMomentum (action p σ)) x := (smooth_coordinate hs 0).neg
  have hv : ContDiffAt ℝ ∞ (phaseDrift p.c (action p σ)) x :=
    contDiffAt_pi.mpr fun i => (contDiffAt_const.mul (smooth_coordinate hs i.succ)).div hn ha.ne'
  have hl := hr.log hp.ne'
  have hg : ContDiffAt ℝ ∞ (spatialScore (density p σ)) x := contDiffAt_pi.mpr fun i => smooth_coordinate hl i.succ
  have hm (i : Fin 4) := (smooth_coordinate hs i).mul (smooth_coordinate hs i)
  exact ⟨hp, ha, htime, hr, hs, hn, (((hm 0).sub (hm 1)).sub (hm 2)).sub (hm 3),
    hv, hg, smooth_coordinate hl 0, smooth_dilatation p.c hn ha.ne' hv,
    DeBroglieLimit.continuous_euclideanSpeed.continuousAt.comp hv.continuousAt,
    DeBroglieLimit.continuous_euclideanSpeed.continuousAt.comp hg.continuousAt⟩

/-- The future phase chart is open in all four spacetime coordinates. -/
theorem isOpen_domain (p : MassiveParameters) {σ : ℝ} (hσ : 0 < σ) : IsOpen (domain p σ) := by
  apply isOpen_iff_mem_nhds.mpr
  intro x hx
  have f := fields p hσ hx
  have hw := (GaussianPositiveFrequencyPacket.smooth_packet (p.m*p.c/p.hbar) hσ).continuous
  have hchart : ∀ᶠ z in 𝓝 x, wave p σ z ∈ PolarLocalInverse.chartDomain 1 :=
    hw.continuousAt.preimage_mem_nhds ((PolarLocalInverse.isOpen_chartDomain 1).mem_nhds hx.1)
  filter_upwards [hchart, f.normal_smooth.continuousAt.eventually (lt_mem_nhds f.normal_pos),
    f.phase_sq_smooth.continuousAt.eventually (lt_mem_nhds f.phase_sq_pos)] with z hz ha hq
  exact ⟨hz, ha, hq⟩

/-- Every initial point with positive normal coefficient has a regular
future-timelike spacetime neighborhood. -/
theorem slice_mem_domain (p : MassiveParameters) {σ : ℝ} (hσ : 0 < σ) (y : Spatial)
    (hy : 0 < coefficient p σ y) : slicePoint 0 y ∈ domain p σ := by
  refine ⟨?_, (future_iff p hσ y).mpr hy⟩
  change GaussianPositiveFrequencyPacket.packet _ σ (slicePoint 0 y) ∈ _
  rw [GaussianPositiveFrequencyPacket.initial_value _ hσ]
  simpa [PolarLocalInverse.chartDomain] using
    Complex.ofReal_mem_slitPlane.mpr (GaussianCauchySlice.amplitude_pos σ y)

end FoliationQM.GaussianPacketTimeRegularity
