module

public import FoliationQM.GaussianCompactFutureTube
public import FoliationQM.GaussianRegionalCoercivity
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Temporal continuity of the packet's compact regional moments

The v13 dilatation condition compares two weighted norms on a fixed spatial
region. Compactness of a laboratory-time strip bounds each continuous
weighted square by one integrable constant. Its slice integrals therefore
vary continuously, including when the region contains the packet center.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.GaussianCompactSliceMoments

open LorentzCoordinates GaussianPacketPolarDomain GaussianPacketTimeRegularity
open GaussianCompactFutureTube GaussianRegionalCoercivity
open OsmoticSliceFields WeightedOsmoticCoercivity SpacelikeOsmoticIntegral
open Set MeasureTheory Filter

/-- For a jointly continuous real integrand on compact time and spatial
sets, its integral over the same spatial set is continuous in time. -/
theorem continuousOn_integral {I : Set ℝ} {K : Set Spatial} (hI : IsCompact I)
    (hK : IsCompact K) {f : ℝ × Spatial → ℝ} (hf : ContinuousOn f (I ×ˢ K)) :
    ContinuousOn (fun t => ∫ y in K, f (t,y)) I := by
  obtain ⟨M, hM⟩ := (hI.prod hK).bddAbove_image hf.norm
  apply continuousOn_of_dominated (bound := fun _ => M)
  · intro t ht
    have hslice : ContinuousOn (fun y => f (t,y)) K :=
      hf.comp (continuous_const.prodMk continuous_id).continuousOn (fun _ hy => ⟨ht, hy⟩)
    exact (hslice.integrableOn_compact hK).aestronglyMeasurable
  · intro t ht
    filter_upwards [self_mem_ae_restrict hK.measurableSet] with y hy
    exact hM (mem_image_of_mem _ (show (t,y) ∈ I ×ˢ K from ⟨ht,hy⟩))
  · exact integrableOn_const hK.measure_ne_top
  · filter_upwards [self_mem_ae_restrict hK.measurableSet] with y hy
    exact hf.comp (continuous_id.prodMk continuous_const).continuousOn (fun _ ht => ⟨ht,hy⟩)

/-- On a fixed compact region inside the regular future chart for a compact
laboratory time set, the weighted dilatation, spatial-score and normal-score
norms are continuous functions of laboratory time. -/
theorem norms_continuousOn (p : MassiveParameters) {σ : ℝ} (hσ : 0 < σ)
    {I : Set ℝ} {K : Set Spatial} (hI : IsCompact I) (hK : IsCompact K)
    (hdom : ∀ t ∈ I, ∀ y ∈ K, slicePoint (p.c*t) y ∈ domain p σ) :
    ContinuousOn (fun t => weightedNorm (volume.restrict K) (density p σ ∘ slicePoint (p.c*t))
      (dilatation p.c (action p σ) ∘ slicePoint (p.c*t))) I ∧
    ContinuousOn (fun t => weightedNorm (volume.restrict K) (density p σ ∘ slicePoint (p.c*t))
      (scoreMagnitude (density p σ) (p.c*t))) I ∧
    ContinuousOn (fun t => weightedNorm (volume.restrict K) (density p σ ∘ slicePoint (p.c*t))
      (normalScore (density p σ) ∘ slicePoint (p.c*t))) I := by
  exact ⟨(continuousOn_integral hI hK (continuous_dilatationSquare_on p hσ hdom)).sqrt,
    (continuousOn_integral hI hK (continuous_spatialSquare_on p hσ hdom)).sqrt,
    (continuousOn_integral hI hK (continuous_normalSquare_on p hσ hdom)).sqrt⟩

/-- At initial time the dilatation norm and the normal-score norm vanish
on the future region, while the spatial-score norm is positive on every
positive-volume part, even if that part contains the packet center. -/
theorem initial_norms (p : MassiveParameters) {σ : ℝ} (hσ : 0 < σ) {K : Set Spatial}
    (hvol : 0 < volume K) (hfuture : K ⊆ futureRegion p σ) :
    weightedNorm (volume.restrict K) (density p σ ∘ slicePoint 0)
      (dilatation p.c (action p σ) ∘ slicePoint 0) = 0 ∧
    0 < weightedNorm (volume.restrict K) (density p σ ∘ slicePoint 0)
      (scoreMagnitude (density p σ) 0) ∧
    weightedNorm (volume.restrict K) (density p σ ∘ slicePoint 0)
      (normalScore (density p σ) ∘ slicePoint 0) = 0 := by
  refine ⟨dilatation_norm_zero p hσ hfuture, ?_, ?_⟩
  · rw [spatial_norm_eq p hσ K]
    exact Real.sqrt_pos.mpr (fisher_pos_on_of_volume_pos hσ hvol)
  · unfold weightedNorm
    rw [setIntegral_eq_zero_of_forall_eq_zero, Real.sqrt_zero]
    intro y _
    simp [GaussianPacketPolarDomain.normal_score p hσ y]

end FoliationQM.GaussianCompactSliceMoments
