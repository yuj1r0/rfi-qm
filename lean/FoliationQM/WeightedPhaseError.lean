module

public import Mathlib.Analysis.Normed.Lp.ProdLp
public import Mathlib.Tactic

/-!
# The exact weighted phase error and its vector-field bound

The continuous linear map `(x,v) ↦ (x,Tv)` into the genuine L¹ product
space has norm exactly `‖x‖ + T‖v‖` for nonnegative `T`. For positive
`T` it is a continuous linear equivalence. Separate position and velocity
bounds for an acceleration field yield the coefficient
`max (T Lx) (1/T + Lv)` from v13, with an additive force contribution
`T A`. This is a vector-field estimate; it does not assume differentiability
of the scalar norm at a zero error.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.WeightedPhaseError

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The weighted position-velocity representation in the genuine L¹ product normed space. -/
def phaseMap (T : ℝ) : (E × E) →L[ℝ] WithLp 1 (E × E) :=
  (WithLp.prodContinuousLinearEquiv 1 ℝ E E).symm.toContinuousLinearMap.comp
    ((ContinuousLinearMap.fst ℝ E E).prod (T • ContinuousLinearMap.snd ℝ E E))

/-- The weighted phase representation keeps position and scales velocity by the time horizon. -/
theorem phaseMap_apply (T : ℝ) (z : E × E) :
    phaseMap T z = WithLp.toLp 1 (z.1, T • z.2) := rfl

/-- Nonzero weighting makes the phase representation a continuous linear equivalence. -/
def phaseEquiv (T : ℝ) (hT : T ≠ 0) : (E × E) ≃L[ℝ] WithLp 1 (E × E) where
  toLinearEquiv := ((LinearEquiv.refl ℝ E).prodCongr
    (LinearEquiv.smulOfNeZero ℝ E T hT)).trans (WithLp.linearEquiv 1 ℝ (E × E)).symm
  continuous_toFun := (phaseMap (E := E) T).continuous
  continuous_invFun := by
    change Continuous (fun z : WithLp 1 (E × E) => (z.fst, T⁻¹ • z.snd))
    have hc := (WithLp.prodContinuousLinearEquiv 1 ℝ E E).continuous
    exact hc.fst.prodMk (hc.snd.const_smul T⁻¹)

/-- The continuous linear equivalence is the same weighted map used in the estimates. -/
theorem phaseEquiv_apply (T : ℝ) (hT : T ≠ 0) (z : E × E) :
    phaseEquiv T hT z = phaseMap T z := rfl

/-- The genuine L¹ product norm is exactly the source weighted position-plus-velocity error. -/
theorem phaseMap_norm {T : ℝ} (hT : 0 ≤ T) (x v : E) :
    ‖phaseMap T (x, v)‖ = ‖x‖ + T * ‖v‖ := by
  rw [phaseMap_apply, WithLp.prod_norm_eq_of_L1]
  simp only [WithLp.toLp_fst, WithLp.toLp_snd, norm_smul, Real.norm_eq_abs, abs_of_nonneg hT]

/-- Differences in the weighted phase space give exactly the source difference error. -/
theorem phaseMap_sub_norm {T : ℝ} (hT : 0 ≤ T) (z w : E × E) :
    ‖phaseMap T z - phaseMap T w‖ = ‖z.1 - w.1‖ + T * ‖z.2 - w.2‖ := by
  rw [← map_sub]
  exact phaseMap_norm hT _ _

/-- A positive-weight phase norm vanishes precisely when both original errors vanish. -/
theorem phaseMap_norm_eq_zero_iff {T : ℝ} (hT : 0 < T) (z : E × E) :
    ‖phaseMap T z‖ = 0 ↔ z = 0 := by
  rw [norm_eq_zero]
  exact (phaseEquiv T hT.ne').map_eq_zero_iff

/-- The exact weighted phase-space growth coefficient from the separate position and velocity controls. -/
def rate (T Lx Lv : ℝ) : ℝ := max (T * Lx) (1 / T + Lv)

/-- Nonnegative Lipschitz controls give a nonnegative weighted growth coefficient. -/
theorem coefficient_nonneg {T Lx Lv : ℝ} (hT : 0 < T) (hLx : 0 ≤ Lx) (hLv : 0 ≤ Lv) :
    0 ≤ rate T Lx Lv := by
  have hx : 0 ≤ T * Lx := mul_nonneg hT.le hLx
  have hv : 0 ≤ 1 / T + Lv := add_nonneg (one_div_nonneg.mpr hT.le) hLv
  dsimp only [rate]
  exact le_trans (le_min hx hv) min_le_max

/-- Separate position and velocity contributions are bounded by the exact maximum coefficient in the weighted norm. -/
theorem weighted_coefficients_le {T Lx Lv dx dv : ℝ} (hT : 0 < T)
    (hx : 0 ≤ dx) (hv : 0 ≤ dv) :
    dv + T * (Lx * dx + Lv * dv) ≤ rate T Lx Lv * (dx + T * dv) := by
  have hxp := mul_le_mul_of_nonneg_right (le_max_left (T * Lx) (1 / T + Lv)) hx
  have hvp := mul_le_mul_of_nonneg_right (le_max_right (T * Lx) (1 / T + Lv))
    (mul_nonneg hT.le hv)
  have he : (1 / T + Lv) * (T * dv) = dv + T * Lv * dv := by
    field_simp
  rw [he] at hvp
  dsimp only [rate]
  nlinarith

/-- An actual acceleration-input norm bound yields the weighted phase-vector bound, including the precise additive forcing term. -/
theorem weighted_error_le_source {T Lx Lv A : ℝ} (hT : 0 < T) (dx dv a : E)
    (ha : ‖a‖ ≤ Lx * ‖dx‖ + Lv * ‖dv‖ + A) :
    ‖phaseMap T (dv, a)‖ ≤ rate T Lx Lv * ‖phaseMap T (dx, dv)‖ + T * A := by
  rw [phaseMap_norm hT.le, phaseMap_norm hT.le]
  calc
    ‖dv‖ + T * ‖a‖ ≤ ‖dv‖ + T * (Lx * ‖dx‖ + Lv * ‖dv‖ + A) := by gcongr
    _ = (‖dv‖ + T * (Lx * ‖dx‖ + Lv * ‖dv‖)) + T * A := by ring
    _ ≤ rate T Lx Lv * (‖dx‖ + T * ‖dv‖) + T * A :=
      add_le_add (weighted_coefficients_le hT (norm_nonneg dx) (norm_nonneg dv)) le_rfl

/-- Separate genuine position and velocity controls for the acceleration field imply the weighted difference bound for the perturbed phase vector field. -/
theorem field_difference_bound {T Lx Lv A : ℝ} (hT : 0 < T)
    (G : E → E → E) (x v y w f : E)
    (hGx : ‖G x v - G y v‖ ≤ Lx * ‖x - y‖)
    (hGv : ‖G y v - G y w‖ ≤ Lv * ‖v - w‖) (hf : ‖f‖ ≤ A) :
    ‖phaseMap T (v - w, G x v + f - G y w)‖ ≤
      rate T Lx Lv * ‖phaseMap T (x - y, v - w)‖ + T * A := by
  apply weighted_error_le_source hT
  have he : G x v + f - G y w = (G x v - G y v) + (G y v - G y w) + f := by abel
  rw [he]
  exact (norm_add_le _ _).trans
    (add_le_add ((norm_add_le _ _).trans (add_le_add hGx hGv)) hf)

end FoliationQM.WeightedPhaseError
