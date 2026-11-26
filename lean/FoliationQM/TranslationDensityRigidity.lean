module

public import FoliationQM.FisherNormalization
public import FoliationQM.LorentzCoordinates
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Translation rigidity of a finite spatial density

A nonzero translation strictly increases a bounded test function in a coordinate
where the displacement is nonzero. An everywhere-positive integrable density
invariant under that translation would assign different integrals to a function
and its translate. Applying this fact along lines detects every nonzero
direction of the spatial translation score.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.TranslationDensityRigidity

open MeasureTheory LorentzCoordinates FisherNormalization

/-- A positive, continuous, integrable density on all of space has only the zero period. -/
theorem period_eq_zero {ρ : Spatial → ℝ} {v : Spatial} (hρ : Continuous ρ)
    (hpos : ∀ x, 0 < ρ x) (hi : Integrable ρ) (hperiod : ∀ x, ρ (x + v) = ρ x) : v = 0 := by
  classical
  funext i
  change v i = 0
  by_contra hvi
  let A (x : Spatial) := Real.arctan (v i * x i)
  let F (x : Spatial) := ρ x * A x
  have hA : Continuous A := Real.continuous_arctan.comp (continuous_const.mul (continuous_apply i))
  have hF : Continuous F := hρ.mul hA
  have hFi : Integrable F := hi.mul_bdd hA.aestronglyMeasurable (c := Real.pi/2)
    (ae_of_all _ fun x => by
      rw [Real.norm_eq_abs]
      exact abs_le.mpr ⟨(Real.arctan_mem_Ioo _).1.le, (Real.arctan_mem_Ioo _).2.le⟩)
  have hinc (x : Spatial) : 0 < F (x + v) - F x := by
    change 0 < ρ (x + v) * A (x + v) - ρ x * A x
    rw [hperiod]
    apply sub_pos.mpr
    apply mul_lt_mul_of_pos_left _ (hpos x)
    apply Real.arctan_strictMono
    change v i * x i < v i * (x i + v i)
    nlinarith [sq_pos_of_ne_zero hvi]
  have hposInt : 0 < ∫ x, (F (x + v) - F x) := integral_pos_of_integrable_nonneg_nonzero
    ((hF.comp (continuous_id.add continuous_const)).sub hF) ((hFi.comp_add_right v).sub hFi)
    (fun x => (hinc x).le) (hinc 0).ne'
  rw [integral_sub (hFi.comp_add_right v) hFi, integral_add_right_eq_self, sub_self] at hposInt
  exact (lt_irrefl 0) hposInt

/-- If the directional score vanishes everywhere, the density is constant on
each affine line in that direction. -/
theorem line_invariant_of_score_zero {ρ : Spatial → ℝ} {v : Spatial} (hρ : Differentiable ℝ ρ)
    (hpos : ∀ x, 0 < ρ x) (hzero : ∀ x, score ρ x v = 0) (x : Spatial) (t : ℝ) :
    ρ (x + t • v) = ρ x := by
  have hd (y : Spatial) : fderiv ℝ ρ y v = 0 := by
    have h := hzero y
    rw [score_eq (hρ y) (hpos y) v, div_eq_zero_iff] at h
    exact h.resolve_right (hpos y).ne'
  have hline (s : ℝ) : HasDerivAt (fun u : ℝ => ρ (x + u • v)) 0 s := by
    have hpath : HasDerivAt (fun u : ℝ => x + u • v) v s := by
      simpa using ((hasDerivAt_id s).smul_const v).const_add x
    simpa only [Function.comp_def, hd] using
      (hρ (x + s • v)).hasFDerivAt.comp_hasDerivAt s hpath
  simpa using is_const_of_deriv_eq_zero (fun s => (hline s).differentiableAt)
    (fun s => (hline s).deriv) t 0

/-- Under finite mass, a pointwise zero spatial translation score forces its direction to vanish. -/
theorem direction_eq_zero_of_score_zero {ρ : Spatial → ℝ} {v : Spatial}
    (hρ : Differentiable ℝ ρ) (hpos : ∀ x, 0 < ρ x) (hi : Integrable ρ)
    (hzero : ∀ x, score ρ x v = 0) : v = 0 := by
  apply period_eq_zero hρ.continuous hpos hi
  intro x
  simpa using line_invariant_of_score_zero hρ hpos hzero x 1

end FoliationQM.TranslationDensityRigidity
