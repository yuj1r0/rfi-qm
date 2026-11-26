module
public import Mathlib.LinearAlgebra.BilinearForm.Basic
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Tactic

/-!
# Signed metric normalization and orthogonal residuals

Source scope: the actual Lorentz-tetrad bridge underlying v13
`prop:takabayasi`. These are explicit bilinear algebra operations used in
the later local construction. A sign has square one; normalization requires
strict positivity of the signed square before division by its square root.
The orthogonal residual is computed from the actual metric, not supplied
as an orthogonality premise. No positive-definite inner product or smooth
orthonormal frame is assumed.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.SignedMetricProjection

variable {V : Type*} [AddCommGroup V] [Module ℝ V]
  (g : LinearMap.BilinForm ℝ V)

/-- The positive-scale normalization factor on the domain of a positive signed metric square. -/
def scale (ε : ℝ) (v : V) : ℝ := (Real.sqrt (ε * g v v))⁻¹

/-- Explicit signed normalization of an actual vector, with domain hypotheses retained in all normalization conclusions. -/
def normalize (ε : ℝ) (v : V) : V := scale g ε v • v

/-- The actual metric orthogonal residual along a signed unit vector, as a linear operation on the original vector space. -/
def residual (ε : ℝ) (e : V) : V →ₗ[ℝ] V :=
  LinearMap.id - (g e).smulRight (ε • e)

/-- The linear residual has exactly the explicit signed metric projection formula. -/
theorem residual_apply (ε : ℝ) (e v : V) :
    residual g ε e v = v - (ε * g e v) • e := by
  simp only [residual, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.smulRight_apply,
    smul_smul, mul_comm]

/-- Normalization uses a strictly positive scalar when the actual signed metric square is positive. -/
theorem scale_pos {ε : ℝ} {v : V} (hv : 0 < ε * g v v) : 0 < scale g ε v :=
  inv_pos.mpr (Real.sqrt_pos.mpr hv)

/-- The normalization scalar cannot vanish on the actual positive signed-square domain. -/
theorem scale_ne_zero {ε : ℝ} {v : V} (hv : 0 < ε * g v v) : scale g ε v ≠ 0 :=
  ne_of_gt (scale_pos g hv)

/-- The square of the normalization scalar cancels exactly the positive signed metric square. -/
theorem scale_sq_mul {ε : ℝ} {v : V} (hv : 0 < ε * g v v) :
    (scale g ε v) ^ 2 * (ε * g v v) = 1 := by
  rw [scale, inv_pow, Real.sq_sqrt hv.le]
  exact inv_mul_cancel₀ hv.ne'

/-- Signed normalization gives the requested metric square, using the actual positive denominator and the independent sign law. -/
theorem metric_normalize {ε : ℝ} {v : V} (hε : ε ^ 2 = 1) (hv : 0 < ε * g v v) :
    g (normalize g ε v) (normalize g ε v) = ε := by
  have hs := scale_sq_mul g hv
  change g (scale g ε v • v) (scale g ε v • v) = ε
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
  rcases sq_eq_one_iff.mp hε with rfl | rfl
  · nlinarith only [hs]
  · nlinarith only [hs]

/-- An already signed unit vector is unchanged by the explicit normalization. -/
theorem normalize_of_metric {ε : ℝ} {v : V} (hε : ε ^ 2 = 1) (hv : g v v = ε) :
    normalize g ε v = v := by
  simp only [normalize, scale, hv, ← pow_two, hε, Real.sqrt_one, inv_one, one_smul]

/-- Pairing a normalized vector in the first metric argument multiplies the original pairing by the actual normalization factor. -/
theorem metric_normalize_left (ε : ℝ) (v w : V) :
    g (normalize g ε v) w = scale g ε v * g v w := by
  simp [normalize]

/-- Pairing a normalized vector in the second metric argument multiplies the original pairing by its actual normalization factor. -/
theorem metric_normalize_right (ε : ℝ) (v w : V) :
    g v (normalize g ε w) = scale g ε w * g v w := by
  simp [normalize]

/-- Normalization preserves a zero metric pairing in the first argument without any hidden denominator assumption. -/
theorem normalize_orthogonal_left (ε : ℝ) (v w : V) (h : g v w = 0) :
    g (normalize g ε v) w = 0 := by
  rw [metric_normalize_left, h, mul_zero]

/-- Normalization preserves a zero metric pairing in the second argument. -/
theorem normalize_orthogonal_right (ε : ℝ) (v w : V) (h : g v w = 0) :
    g v (normalize g ε w) = 0 := by
  rw [metric_normalize_right, h, mul_zero]

/-- The residual is orthogonal to the actual signed unit vector by bilinearity and the sign-square law. -/
theorem metric_residual {ε : ℝ} {e : V} (hε : ε ^ 2 = 1) (he : g e e = ε) (v : V) :
    g e (residual g ε e v) = 0 := by
  rw [residual_apply]
  simp only [map_sub, map_smul, smul_eq_mul, he]
  calc
    _ = (1 - ε ^ 2) * g e v := by ring
    _ = 0 := by rw [hε]; ring

/-- A vector already orthogonal to the distinguished vector is unchanged by the actual residual operation. -/
theorem residual_of_orthogonal (ε : ℝ) (e v : V) (h : g e v = 0) :
    residual g ε e v = v := by
  rw [residual_apply, h, mul_zero, zero_smul, sub_zero]

/-- Orthogonal residual projection is idempotent when its distinguished vector has the stated signed unit square. -/
theorem residual_idempotent {ε : ℝ} {e : V} (hε : ε ^ 2 = 1) (he : g e e = ε) (v : V) :
    residual g ε e (residual g ε e v) = residual g ε e v :=
  residual_of_orthogonal g ε e _ (metric_residual g hε he v)

/-- A residual preserves orthogonality to any vector orthogonal to both the original vector and the removed direction. -/
theorem residual_orthogonal_left (ε : ℝ) (e v w : V)
    (hwv : g w v = 0) (hwe : g w e = 0) :
    g w (residual g ε e v) = 0 := by
  rw [residual_apply]
  simp [hwv, hwe]

/-- A symmetric metric evaluates two orthogonal residuals by the original pairing minus the exact signed projection contribution. -/
theorem metric_residual_pair {ε : ℝ} {e : V} (hε : ε ^ 2 = 1)
    (he : g e e = ε) (hg : g.IsSymm) (v w : V) :
    g (residual g ε e v) (residual g ε e w) = g v w - ε * g e v * g e w := by
  rw [residual_apply, residual_apply]
  simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
  have hzero : g e v - ε * g e v * ε = 0 := by
    calc
      _ = (1 - ε ^ 2) * g e v := by ring
      _ = 0 := by rw [hε]; ring
  rw [he, hg.eq v e, hzero, mul_zero, sub_zero]

/-- The residual metric square is exactly the original square minus the signed squared metric component. -/
theorem metric_residual_sq {ε : ℝ} {e : V} (hε : ε ^ 2 = 1)
    (he : g e e = ε) (hg : g.IsSymm) (v : V) :
    g (residual g ε e v) (residual g ε e v) = g v v - ε * (g e v) ^ 2 := by
  rw [metric_residual_pair g hε he hg]
  ring

/-- The original vector is the sum of its explicit orthogonal residual and signed metric component. -/
theorem residual_decomposition (ε : ℝ) (e v : V) :
    v = residual g ε e v + (ε * g e v) • e := by
  rw [residual_apply, sub_add_cancel]

end FoliationQM.SignedMetricProjection
