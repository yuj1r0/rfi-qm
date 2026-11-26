module

public import FoliationQM.TwoParticleMarginals
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Measure.SeparableMeasure

/-!
# Remote Hilbert-space fibers of a joint spatial wave

A joint square-integrable wave determines a strongly measurable family of
remote square-integrable sections. The construction uses the measurable
representative of the joint wave and assigns zero on exceptional fibers.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.JointL2Sections

open LorentzCoordinates MeasureTheory Set
open scoped ENNReal

/-- Complex waves on the spatial configuration space of two particles. -/
abbrev Joint : Type := Lp ℂ 2 (volume : Measure (Spatial × Spatial))

/-- The Hilbert space of remote particle waves. -/
abbrev Remote : Type := Lp ℂ 2 (volume : Measure Spatial)

/-- Square-integrable remote-Hilbert-valued functions of the retained position. -/
abbrev Outer : Type := Lp Remote 2 (volume : Measure Spatial)

/-- Section of the canonical joint representative, with zero on exceptional fibers. -/
def sections (ψ : Joint) (x : Spatial) : Remote := by
  classical
  exact if hx : MemLp (fun y => ψ (x, y)) 2 volume then hx.toLp _ else 0

/-- Almost every remote fiber has square-integrable modulus. -/
theorem memLp_ae (ψ : Joint) : ∀ᵐ x ∂volume, MemLp (fun y => ψ (x, y)) 2 volume := by
  have h := (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable ψ)).mp (Lp.memLp ψ)
  filter_upwards [h.prod_right_ae] with x hx
  exact (memLp_two_iff_integrable_sq_norm
    ((Lp.stronglyMeasurable ψ).comp_measurable measurable_prodMk_left).aestronglyMeasurable).mpr hx

/-- A square-integrable fiber represents the original scalar section almost everywhere. -/
theorem coe_sections (ψ : Joint) (x : Spatial) (hx : MemLp (fun y => ψ (x, y)) 2 volume) :
    (sections ψ x : Spatial → ℂ) =ᵐ[volume] fun y => ψ (x, y) := by
  simpa [sections, hx] using hx.coeFn_toLp

/-- The fiber norm recovers the integral of the scalar Born density at each good position. -/
theorem norm_sq_sections (ψ : Joint) (x : Spatial)
    (hx : MemLp (fun y => ψ (x, y)) 2 volume) :
    ‖sections ψ x‖ ^ 2 = ∫ y, ‖ψ (x, y)‖ ^ 2 := by
  let f := sections ψ x
  rw [norm_sq_eq_re_inner (𝕜 := ℂ), L2.inner_def,
    ← integral_re (L2.integrable_inner (𝕜 := ℂ) f f)]
  apply integral_congr_ae
  filter_upwards [coe_sections ψ x hx] with y hy
  rw [inner_self_eq_norm_sq, hy]

private theorem measurable_fiber_eLpNorm {f : Spatial × Spatial → ℂ}
    (hf : Measurable f) : Measurable fun x => eLpNorm (fun y => f (x, y)) 2 volume := by
  have hg (x : Spatial) : AEStronglyMeasurable (fun y => f (x, y)) volume :=
    (hf.comp (measurable_prodMk_left (x := x))).aestronglyMeasurable
  simp_rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top (hg _)]
  exact (hf.enorm.pow_const (2 : ℝ≥0∞).toReal).lintegral_prod_right'.pow_const _

private theorem measurable_edist_sections (ψ : Joint) (v : Remote) :
    Measurable fun x => edist (sections ψ x) v := by
  classical
  have hψ := (Lp.stronglyMeasurable ψ).measurable
  have good : MeasurableSet {x | MemLp (fun y => ψ (x, y)) 2 volume} :=
    measurableSet_lt (measurable_fiber_eLpNorm hψ) measurable_const
  have hdiff : Measurable (fun z : Spatial × Spatial => ψ z - v z.2) :=
    hψ.sub ((Lp.stronglyMeasurable v).measurable.comp measurable_snd)
  have he (x : Spatial) : edist (sections ψ x) v =
      if MemLp (fun y => ψ (x, y)) 2 volume then eLpNorm (fun y => ψ (x, y) - v y) 2 volume
      else edist (0 : Remote) v := by
    by_cases hx : MemLp (fun y => ψ (x, y)) 2 volume
    · simp only [hx, ite_true, sections, dite_eq_left]
      nth_rw 1 [← Lp.toLp_coeFn v (Lp.memLp v)]
      exact Lp.edist_toLp_toLp _ _ hx (Lp.memLp v)
    · simp [hx, sections]
  simp_rw [he]
  exact Measurable.ite good (measurable_fiber_eLpNorm hdiff) measurable_const

/-- The remote sections are strongly measurable in the retained coordinate. -/
theorem stronglyMeasurable_sections (ψ : Joint) : StronglyMeasurable (sections ψ) := by
  let : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨ENNReal.ofNat_ne_top⟩
  let : MeasurableSpace Remote := borel Remote
  let : BorelSpace Remote := ⟨rfl⟩
  suffices h : Measurable (sections ψ) from h.stronglyMeasurable
  apply measurable_of_isOpen
  intro s hs
  choose r hr hsub using fun z : s => Metric.isOpen_iff.mp hs z z.2
  let balls (z : s) := Metric.ball (z : Remote) (r z)
  obtain ⟨t, ht, htcover⟩ := TopologicalSpace.isOpen_iUnion_countable balls
    (fun _ => Metric.isOpen_ball)
  have hcover : ⋃ z, balls z = s := by
    apply subset_antisymm (iUnion_subset hsub)
    intro z hz
    exact mem_iUnion.mpr ⟨⟨z, hz⟩, Metric.mem_ball_self (hr ⟨z, hz⟩)⟩
  rw [← hcover, ← htcover, preimage_iUnion₂]
  apply MeasurableSet.biUnion ht
  intro z _
  exact measurableSet_lt (by simpa only [← dist_edist] using
    (measurable_edist_sections ψ z).ennreal_toReal) measurable_const

end FoliationQM.JointL2Sections
