module

public import FoliationQM.TranslationDensityRigidity
public import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# Null directions of the spatial translation Fisher form

For v13 Remark 5.2(b), the directional Fisher information of a translated
spatial profile is the integral of the squared directional score against
the density. On an open portion of the slice its kernel is detected by
the actual directional derivative. A positive integrable density on the
whole slice admits no nonzero null direction when its Fisher entries are finite.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.TranslationFisherDefiniteness

open MeasureTheory Set LorentzCoordinates FisherNormalization

/-- The spatial Fisher quadratic form in one translation direction. -/
def directional (ρ : Spatial → ℝ) (μ : Measure Spatial) (v : Spatial) : ℝ :=
  ∫ x, ρ x * score ρ x v ^ 2 ∂μ

variable {ρ : Spatial → ℝ} {μ : Measure Spatial} {v : Spatial} {U : Set Spatial}

/-- For a nonnegative slice density, the directional Fisher form is nonnegative. -/
theorem directional_nonneg (hp : ∀ᵐ x ∂μ, 0 ≤ ρ x) (v : Spatial) : 0 ≤ directional ρ μ v :=
  integral_nonneg_of_ae (hp.mono fun x hx => mul_nonneg hx (sq_nonneg (score ρ x v)))

/-- A finite directional Fisher form vanishes exactly when its directional
score vanishes almost everywhere for a positive density. -/
theorem directional_zero_iff_ae (hp : ∀ᵐ x ∂μ, 0 < ρ x)
    (hi : Integrable (fun x => ρ x * score ρ x v ^ 2) μ) :
    directional ρ μ v = 0 ↔ ∀ᵐ x ∂μ, score ρ x v = 0 := by
  have hn := hp.mono fun x hx => mul_nonneg hx.le (sq_nonneg (score ρ x v))
  rw [directional, integral_eq_zero_iff_of_nonneg_ae hn hi]
  constructor
  · intro hz
    filter_upwards [hp, hz] with x hx hzero
    change ρ x * score ρ x v ^ 2 = 0 at hzero
    exact (sq_eq_zero_iff).mp ((mul_eq_zero.mp hzero).resolve_left hx.ne')
  · intro hs
    filter_upwards [hs] with x hx
    simp [hx]

/-- On an open region with positive C¹ density, every zero-information
direction annihilates the actual score at every point of that region. -/
theorem directional_zero_iff_on (hU : IsOpen U) (hr : ∀ x ∈ U, ContDiffAt ℝ 1 ρ x)
    (hp : ∀ x ∈ U, 0 < ρ x) (hi : IntegrableOn (fun x => ρ x * score ρ x v ^ 2) U) :
    directional ρ (volume.restrict U) v = 0 ↔ ∀ x ∈ U, score ρ x v = 0 := by
  have hp' := (ae_restrict_mem (μ := volume) hU.measurableSet).mono hp
  rw [directional_zero_iff_ae hp' hi]
  constructor
  · intro hs
    have hc : ContinuousOn (fun x => score ρ x v) U := by
      intro x hx
      have hd := (((hr x hx).log (hp x hx).ne').fderiv_right (m := 0) (by norm_num)).continuousAt
      exact (hd.clm_apply (g := fun _ => v) continuousAt_const).continuousWithinAt
    have hz : EqOn (fun x => score ρ x v) 0 U :=
      Measure.eqOn_open_of_ae_eq hs hU hc continuousOn_const
    exact fun _ hx => hz hx
  · exact fun hs => (ae_restrict_mem hU.measurableSet).mono hs

/-- A finite direction has strictly positive Fisher information on an open
region precisely when its directional score is nonzero somewhere there. -/
theorem directional_pos_iff_on (hU : IsOpen U) (hr : ∀ x ∈ U, ContDiffAt ℝ 1 ρ x)
    (hp : ∀ x ∈ U, 0 < ρ x) (hi : IntegrableOn (fun x => ρ x * score ρ x v ^ 2) U) :
    0 < directional ρ (volume.restrict U) v ↔ ∃ x ∈ U, score ρ x v ≠ 0 := by
  have hn := directional_nonneg ((ae_restrict_mem (μ := volume) hU.measurableSet).mono
    fun x hx => (hp x hx).le) v
  constructor
  · intro hpos
    by_contra! hz
    exact hpos.ne' ((directional_zero_iff_on hU hr hp hi).2 hz)
  · rintro ⟨x, hx, hs⟩
    exact hn.lt_of_ne fun hz => hs ((directional_zero_iff_on hU hr hp hi).1 hz.symm x hx)

/-- Equivalently, regional positive information detects actual infinitesimal
variation of the unnormalized spatial density along the direction. -/
theorem directional_pos_iff_density_variation (hU : IsOpen U) (hr : ∀ x ∈ U, ContDiffAt ℝ 1 ρ x)
    (hp : ∀ x ∈ U, 0 < ρ x) (hi : IntegrableOn (fun x => ρ x * score ρ x v ^ 2) U) :
    0 < directional ρ (volume.restrict U) v ↔ ∃ x ∈ U, fderiv ℝ ρ x v ≠ 0 := by
  rw [directional_pos_iff_on hU hr hp hi]
  apply exists_congr
  intro x
  apply and_congr_right
  intro hx
  rw [score_eq (hr x hx).differentiableAt_one (hp x hx), div_ne_zero_iff]
  simp [(hp x hx).ne']

/-- Positive C¹ densities with finite mass on all of three-dimensional
space have strictly positive finite Fisher information in every nonzero
translation direction whose squared score is integrable. -/
theorem directional_pos_of_ne_zero (hr : ContDiff ℝ 1 ρ) (hp : ∀ x, 0 < ρ x) (hm : Integrable ρ)
    (hi : Integrable (fun x => ρ x * score ρ x v ^ 2)) (hv : v ≠ 0) :
    0 < directional ρ volume v := by
  have hn := directional_nonneg (μ := volume) (Filter.Eventually.of_forall fun x => (hp x).le) v
  refine hn.lt_of_ne fun hz => hv ?_
  have hU : directional ρ (volume.restrict univ) v = 0 := by simpa using hz.symm
  have hs := (directional_zero_iff_on isOpen_univ (fun _ _ => hr.contDiffAt)
    (fun x _ => hp x) (by simpa only [IntegrableOn, Measure.restrict_univ] using hi)).mp hU
  exact TranslationDensityRigidity.direction_eq_zero_of_score_zero
    (hr.differentiable (by norm_num)) hp hm (fun x => hs x (mem_univ x))

end FoliationQM.TranslationFisherDefiniteness
