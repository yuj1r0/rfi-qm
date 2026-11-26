module

public import FoliationQM.OsmoticSliceFields
public import FoliationQM.WeightedOsmoticCoercivity

/-! The v13 osmotic mass-shell estimate is a strict inequality for a spatial
integral. The integration variable here lies on a fixed laboratory slice,
whose time coordinate t equals ct_lab. Its measure is flat Lebesgue volume
restricted to A, including A = univ. The hypothesis concerns the actual
weighted L² norms of the score and the dilatation, without a pointwise sign
assumption on osmotic momentum. -/

@[expose] public section
noncomputable section
namespace FoliationQM.SpacelikeOsmoticIntegral
open MeasureTheory OsmoticSliceFields LorentzCoordinates ObserverFluxDensity WeightedOsmoticCoercivity
open scoped ContDiff

/-- The Euclidean magnitude of the spatial logarithmic gradient on a slice. -/
def scoreMagnitude (ρ : Covector → ℝ) (t : ℝ) (y : Spatial) : ℝ :=
  euclideanSpeed (spatialScore ρ (slicePoint t y))

private theorem magnitude_sq (ρ : Covector → ℝ) (t : ℝ) (y : Spatial) :
    scoreMagnitude ρ t y ^ 2 = speedSq (spatialScore ρ (slicePoint t y)) := by
  exact Real.sq_sqrt (speedSq_nonneg _)

private theorem normal_estimate {c V : ℝ} {ρ S : Covector → ℝ} {x : Covector} (hc : 0 < c)
    (h : NormalLogDensity.Formulas c ρ S x) (hv : euclideanSpeed (phaseDrift c S x) ≤ V) :
    c * |normalScore ρ x| ≤ V * euclideanSpeed (spatialScore ρ x) + |dilatation c S x| := by
  calc
    c * |normalScore ρ x| = |c * normalScore ρ x| := by rw [abs_mul, abs_of_pos hc]
    _ = |spatialDot (phaseDrift c S x) (spatialScore ρ x) + dilatation c S x| := by
      rw [normal_balance hc h, ← abs_neg (spatialDot (phaseDrift c S x) (spatialScore ρ x) + dilatation c S x)]
      congr 1
      ring
    _ ≤ _ := (abs_add_le _ _).trans (add_le_add
      ((abs_spatialDot_le _ _).trans (mul_le_mul_of_nonneg_right hv (Real.sqrt_nonneg _))) (le_refl _))

/-- The norm estimate used in the source proof on the physical slice. The
normal derivative is controlled by the spatial score and the full dilatation. -/
theorem slice_norm_estimate {c V : ℝ} (ρ S : Covector → ℝ) (t : ℝ) (A : Set Spatial)
    (hc : 0 < c) (hV : 0 ≤ V) (hVc : V < c)
    (hr : ∀ᵐ y ∂volume.restrict A, 0 ≤ ρ (slicePoint t y))
    (hf : ∀ᵐ y ∂volume.restrict A, NormalLogDensity.Formulas c ρ S (slicePoint t y))
    (hv : ∀ᵐ y ∂volume.restrict A, euclideanSpeed (phaseDrift c S (slicePoint t y)) ≤ V)
    (hm : AEStronglyMeasurable (fun y => ρ (slicePoint t y) * normalScore ρ (slicePoint t y)^2)
      (volume.restrict A))
    (hg : IntegrableOn (fun y => ρ (slicePoint t y) * (scoreMagnitude ρ t y)^2) A)
    (hd : IntegrableOn (fun y => ρ (slicePoint t y) * dilatation c S (slicePoint t y)^2) A) :
    let μ := volume.restrict A
    let r := ρ ∘ slicePoint t
    c * weightedNorm μ r (normalScore ρ ∘ slicePoint t) ≤
      V * weightedNorm μ r (scoreMagnitude ρ t) + weightedNorm μ r (dilatation c S ∘ slicePoint t) := by
  apply norm_estimate hc hV hVc hr (ae_of_all _ fun _ => Real.sqrt_nonneg _) _ hm hg hd
  filter_upwards [hf, hv] with y hy hyv
  exact normal_estimate hc hy hyv

/-- Exact equality and strict negativity of the v13 signed osmotic integral
on a laboratory slice under its weighted dilatation and speed bounds. -/
theorem integral_spacelike (p : MassiveParameters) (ρ S : Covector → ℝ) (t : ℝ) (A : Set Spatial)
    {V : ℝ} (hV : 0 ≤ V) (hVc : V < p.c)
    (hρ : ∀ᵐ y ∂volume.restrict A, 0 ≤ ρ (slicePoint t y))
    (hform : ∀ᵐ y ∂volume.restrict A, NormalLogDensity.Formulas p.c ρ S (slicePoint t y))
    (hv : ∀ᵐ y ∂volume.restrict A, euclideanSpeed (phaseDrift p.c S (slicePoint t y)) ≤ V)
    (hm : AEStronglyMeasurable (fun y => ρ (slicePoint t y) * normalScore ρ (slicePoint t y)^2)
      (volume.restrict A))
    (hg : IntegrableOn (fun y => ρ (slicePoint t y) * (scoreMagnitude ρ t y)^2) A)
    (hd : IntegrableOn (fun y => ρ (slicePoint t y) * dilatation p.c S (slicePoint t y)^2) A)
    (hgap : weightedNorm (volume.restrict A) (ρ ∘ slicePoint t) (dilatation p.c S ∘ slicePoint t) <
      (p.c - V) * weightedNorm (volume.restrict A) (ρ ∘ slicePoint t) (scoreMagnitude ρ t)) :
    let P := fun y => infoMomentum p ρ (slicePoint t y)
    let signed := ∫ y in A, ρ (slicePoint t y) * minkowski (P y) (P y)
    signed = p.hbar^2 / 4 * ∫ y in A, ρ (slicePoint t y) *
      (normalScore ρ (slicePoint t y)^2 - speedSq (spatialScore ρ (slicePoint t y))) ∧ signed < 0 := by
  dsimp only
  have hs := integral_neg (μ := volume.restrict A) (r := ρ ∘ slicePoint t) (G := scoreMagnitude ρ t)
    (D := dilatation p.c S ∘ slicePoint t) (N := normalScore ρ ∘ slicePoint t) p.c_pos hV hVc hρ
    (ae_of_all _ fun y => (Real.sqrt_nonneg _ : 0 ≤ scoreMagnitude ρ t y))
    (by filter_upwards [hform,hv] with y hy hyv; exact normal_estimate p.c_pos hy hyv)
    hm hg hd hgap
  simp only [Function.comp_apply, magnitude_sq] at hs
  have he : (∫ y in A, ρ (slicePoint t y) * minkowski (infoMomentum p ρ (slicePoint t y))
      (infoMomentum p ρ (slicePoint t y))) = p.hbar^2 / 4 * ∫ y in A, ρ (slicePoint t y) *
        (normalScore ρ (slicePoint t y)^2 - speedSq (spatialScore ρ (slicePoint t y))) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with y
    rw [info_square]; ring
  exact ⟨he, he ▸ mul_neg_of_pos_of_neg (div_pos (sq_pos_of_pos p.hbar_pos) (by norm_num)) hs⟩

private theorem continuous_slicePoint (t : ℝ) : Continuous (slicePoint t) := by
  apply continuous_pi
  intro i
  fin_cases i <;> first | exact continuous_const | exact continuous_apply (_ : Fin 3)

/-- The scalar extremal supplies the logarithmic transport equation and the
measurability of the actual normal term. Only the speed and weighted estimates
on the slice are imposed in addition to the regular future-timelike chart. -/
theorem of_scalar_extremal (p : MassiveParameters) {ρ S : Covector → ℝ} {U : Set Covector}
    (hU : IsOpen U) (hρ : ∀ x ∈ U, ContDiffAt ℝ ∞ ρ x) (hS : ∀ x ∈ U, ContDiffAt ℝ ∞ S x)
    (hp : ∀ x ∈ U, 0 < ρ x)
    (hst : RelativePolarStationaryAction.RelativePolarStationaryOn p ρ S Madelung.coordinateVector U)
    (t : ℝ) {A : Set Spatial} (hA : MeasurableSet A) (hu : ∀ y ∈ A, slicePoint t y ∈ U)
    (ha : ∀ y ∈ A, 0 < normalMomentum S (slicePoint t y))
    (ht : ∀ y ∈ A, 0 < minkowski (DressedMassDensityVariation.phaseDifferential S (slicePoint t y))
      (DressedMassDensityVariation.phaseDifferential S (slicePoint t y)))
    {V : ℝ} (hV : 0 ≤ V) (hVc : V < p.c)
    (hv : ∀ y ∈ A, euclideanSpeed (phaseDrift p.c S (slicePoint t y)) ≤ V)
    (hg : IntegrableOn (fun y => ρ (slicePoint t y) * (scoreMagnitude ρ t y)^2) A)
    (hd : IntegrableOn (fun y => ρ (slicePoint t y) * dilatation p.c S (slicePoint t y)^2) A)
    (hgap : weightedNorm (volume.restrict A) (ρ ∘ slicePoint t) (dilatation p.c S ∘ slicePoint t) <
      (p.c - V) * weightedNorm (volume.restrict A) (ρ ∘ slicePoint t) (scoreMagnitude ρ t)) :
    (∫ y in A, ρ (slicePoint t y) * minkowski (infoMomentum p ρ (slicePoint t y))
        (infoMomentum p ρ (slicePoint t y))) < 0 := by
  have hn : ContinuousOn (fun y => ρ (slicePoint t y) * normalScore ρ (slicePoint t y)^2) A := by
    intro y hy
    let x := slicePoint t y
    have hr := hρ x (hu y hy)
    have hl := hr.log (hp x (hu y hy)).ne'
    have hh : ContinuousAt (normalScore ρ) x :=
      (hl.fderiv_right (m := 1) (by simp)).continuousAt.clm_apply continuousAt_const
    exact ((hr.continuousAt.mul (hh.pow 2)).comp (continuous_slicePoint t).continuousAt).continuousWithinAt
  apply (integral_spacelike p ρ S t A hV hVc _ _ _ (hn.aestronglyMeasurable hA) hg hd hgap).2
  · filter_upwards [ae_restrict_mem hA] with y hy
    exact (hp _ (hu y hy)).le
  · filter_upwards [ae_restrict_mem hA] with y hy
    exact (NormalLogDensity.of_scalar_extremal p hU hρ hS hp hst (hu y hy) (ha y hy) (ht y hy)).2
  · filter_upwards [ae_restrict_mem hA] with y hy
    exact hv y hy

end FoliationQM.SpacelikeOsmoticIntegral
