module
public import FoliationQM.LorentzMatrixGroup
public import Mathlib.Tactic.NoncommRing

/-!
# Independent real Lorentz Cayley algebra

Source scope: the intrinsic Lorentz target underlying v13
`prop:takabayasi` and `eq:tetrad_rotor_map`. The two rational matrix maps
are defined on the actual ambient real four-by-four matrices. Their
unit-denominator domains are explicit. Matrix multiplication and genuine
nonsingular inverses prove both roundtrips, without any Spin image or
covering assumption.

The literal metric-skew equation characterizes the Cayley coordinates
of metric-preserving matrices on these domains. Its determinant identity
proves properness of the reconstructed matrix. Future orientation is a
separate open component condition; no smooth atlas or Spin compatibility
is defined or assumed in these algebraic statements.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.LorentzCayleyAlgebra
open LorentzMatrixGroup

/-- The actual infinitesimal Minkowski metric-skew equation in the fixed source signature. -/
def IsEtaSkew (X : Mat4) : Prop := X.transpose * eta + eta * X = 0

/-- The actual real-matrix Cayley reconstruction, used only with an explicit unit denominator in inverse claims. -/
def cayley (X : Mat4) : Mat4 := (1 + X) * (1 - X)⁻¹

/-- The actual inverse Cayley coordinate formula, used only with an explicit unit denominator in inverse claims. -/
def inverseCayley (M : Mat4) : Mat4 := (M - 1) * (M + 1)⁻¹

private theorem inverse_mul {A : Mat4} (h : IsUnit A) : A⁻¹ * A = 1 :=
  Matrix.nonsing_inv_mul A ((Matrix.isUnit_iff_isUnit_det A).mp h)

private theorem mul_inverse {A : Mat4} (h : IsUnit A) : A * A⁻¹ = 1 :=
  Matrix.mul_nonsing_inv A ((Matrix.isUnit_iff_isUnit_det A).mp h)

private theorem isUnit_inverse {A : Mat4} (h : IsUnit A) : IsUnit A⁻¹ :=
  Matrix.isUnit_nonsing_inv_iff.mpr h

private theorem isUnit_transpose {A : Mat4} (h : IsUnit A) : IsUnit A.transpose := by
  apply (Matrix.isUnit_iff_isUnit_det _).mpr
  rw [Matrix.det_transpose]
  exact (Matrix.isUnit_iff_isUnit_det _).mp h

private theorem isUnit_two : IsUnit ((1 : Mat4) + 1) := by
  have h := IsUnit.map (algebraMap ℝ Mat4)
    (isUnit_iff_ne_zero.mpr (by norm_num : (2 : ℝ) ≠ 0))
  rw [Algebra.algebraMap_eq_smul_one] at h
  simpa only [two_smul] using h

/-- The actual Cayley denominator is a unit exactly when its real determinant is nonzero. -/
theorem cayley_domain_iff (X : Mat4) : IsUnit (1 - X) ↔ (1 - X).det ≠ 0 := by
  rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]

/-- The actual inverse Cayley denominator is a unit exactly when its real determinant is nonzero. -/
theorem inverseCayley_domain_iff (M : Mat4) : IsUnit (M + 1) ↔ (M + 1).det ≠ 0 := by
  rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]

/-- Multiplying the actual Cayley reconstruction by its genuine denominator gives its numerator. -/
theorem cayley_mul_denominator (X : Mat4) (hX : IsUnit (1 - X)) :
    cayley X * (1 - X) = 1 + X := by
  rw [cayley, mul_assoc, inverse_mul hX, mul_one]

/-- Multiplying the actual inverse Cayley coordinates by their genuine denominator gives their numerator. -/
theorem inverseCayley_mul_denominator (M : Mat4) (hM : IsUnit (M + 1)) :
    inverseCayley M * (M + 1) = M - 1 := by
  rw [inverseCayley, mul_assoc, inverse_mul hM, mul_one]

/-- The sum of a reconstructed Cayley matrix and identity has the exact twice-identity denominator product. -/
theorem cayley_add_one_mul (X : Mat4) (hX : IsUnit (1 - X)) :
    (cayley X + 1) * (1 - X) = 1 + 1 := by
  rw [add_mul, cayley_mul_denominator X hX]
  noncomm_ring

/-- The difference of a reconstructed Cayley matrix and identity has the exact twice-coordinate denominator product. -/
theorem cayley_sub_one_mul (X : Mat4) (hX : IsUnit (1 - X)) :
    (cayley X - 1) * (1 - X) = X + X := by
  rw [sub_mul, cayley_mul_denominator X hX]
  noncomm_ring

/-- Identity minus the inverse Cayley coordinates has the exact twice-identity denominator product. -/
theorem one_sub_inverseCayley_mul (M : Mat4) (hM : IsUnit (M + 1)) :
    (1 - inverseCayley M) * (M + 1) = 1 + 1 := by
  rw [sub_mul, inverseCayley_mul_denominator M hM]
  noncomm_ring

/-- Identity plus the inverse Cayley coordinates has the exact twice-original-matrix denominator product. -/
theorem one_add_inverseCayley_mul (M : Mat4) (hM : IsUnit (M + 1)) :
    (1 + inverseCayley M) * (M + 1) = M + M := by
  rw [add_mul, inverseCayley_mul_denominator M hM]
  noncomm_ring

/-- Every actual Cayley reconstruction on its unit domain belongs to the inverse formula's unit domain. -/
theorem isUnit_cayley_add_one (X : Mat4) (hX : IsUnit (1 - X)) :
    IsUnit (cayley X + 1) := by
  have he : cayley X + 1 = (1 + 1) * (1 - X)⁻¹ := by
    calc
      cayley X + 1 = ((cayley X + 1) * (1 - X)) * (1 - X)⁻¹ := by
        rw [mul_assoc, mul_inverse hX, mul_one]
      _ = (1 + 1) * (1 - X)⁻¹ := by rw [cayley_add_one_mul X hX]
  rw [he]
  exact isUnit_two.mul (isUnit_inverse hX)

/-- Every actual inverse Cayley coordinate on its unit domain belongs to the reconstruction formula's unit domain. -/
theorem isUnit_one_sub_inverseCayley (M : Mat4) (hM : IsUnit (M + 1)) :
    IsUnit (1 - inverseCayley M) := by
  have he : 1 - inverseCayley M = (1 + 1) * (M + 1)⁻¹ := by
    calc
      1 - inverseCayley M = ((1 - inverseCayley M) * (M + 1)) * (M + 1)⁻¹ := by
        rw [mul_assoc, mul_inverse hM, mul_one]
      _ = (1 + 1) * (M + 1)⁻¹ := by rw [one_sub_inverseCayley_mul M hM]
  rw [he]
  exact isUnit_two.mul (isUnit_inverse hM)

/-- Genuine inverse Cayley coordinates recover every original matrix parameter on the explicit unit-denominator domain. -/
theorem inverseCayley_cayley (X : Mat4) (hX : IsUnit (1 - X)) :
    inverseCayley (cayley X) = X := by
  apply (isUnit_cayley_add_one X hX).mul_right_cancel
  rw [inverseCayley_mul_denominator _ (isUnit_cayley_add_one X hX)]
  apply hX.mul_right_cancel
  rw [cayley_sub_one_mul X hX, mul_assoc, cayley_add_one_mul X hX]
  noncomm_ring

/-- Genuine Cayley reconstruction recovers every original matrix on the explicit inverse unit-denominator domain. -/
theorem cayley_inverseCayley (M : Mat4) (hM : IsUnit (M + 1)) :
    cayley (inverseCayley M) = M := by
  apply (isUnit_one_sub_inverseCayley M hM).mul_right_cancel
  rw [cayley_mul_denominator _ (isUnit_one_sub_inverseCayley M hM)]
  apply hM.mul_right_cancel
  rw [one_add_inverseCayley_mul M hM, mul_assoc, one_sub_inverseCayley_mul M hM]
  noncomm_ring

/-- The origin reconstructs the actual identity Lorentz matrix. -/
theorem cayley_zero : cayley (0 : Mat4) = 1 := by simp [cayley]

/-- The identity matrix has zero inverse Cayley coordinates. -/
theorem inverseCayley_one : inverseCayley (1 : Mat4) = 0 := by simp [inverseCayley]

/-- The zero actual matrix satisfies the independent infinitesimal Minkowski skew equation. -/
theorem isEtaSkew_zero : IsEtaSkew (0 : Mat4) := by simp [IsEtaSkew]

/-- The actual metric-skew equation cancels the cross terms in the two quadratic numerator and denominator metric products. -/
theorem metric_numerator_eq_denominator (X : Mat4) (hX : IsEtaSkew X) :
    (1 + X).transpose * eta * (1 + X) = (1 - X).transpose * eta * (1 - X) := by
  have hs := hX
  change X.transpose * eta + eta * X = 0 at hs
  simp only [Matrix.transpose_add, Matrix.transpose_sub, Matrix.transpose_one]
  calc
    (1 + X.transpose) * eta * (1 + X) =
        eta + (X.transpose * eta + eta * X) + X.transpose * eta * X := by noncomm_ring
    _ = eta - (X.transpose * eta + eta * X) + X.transpose * eta * X := by rw [hs]; simp
    _ = (1 - X.transpose) * eta * (1 - X) := by noncomm_ring

/-- A genuinely metric-skew parameter reconstructs an actual metric-preserving matrix whenever its explicit Cayley denominator is a unit. -/
theorem cayley_metric (X : Mat4) (hskew : IsEtaSkew X) (hX : IsUnit (1 - X)) :
    (cayley X).transpose * eta * cayley X = eta := by
  apply (isUnit_transpose hX).mul_left_cancel
  apply hX.mul_right_cancel
  calc
    ((1 - X).transpose * ((cayley X).transpose * eta * cayley X)) * (1 - X) =
        (cayley X * (1 - X)).transpose * eta * (cayley X * (1 - X)) := by
          rw [Matrix.transpose_mul]
          noncomm_ring
    _ = (1 + X).transpose * eta * (1 + X) := by rw [cayley_mul_denominator X hX]
    _ = ((1 - X).transpose * eta) * (1 - X) := metric_numerator_eq_denominator X hskew

/-- Every independently metric-preserving matrix has genuinely metric-skew inverse Cayley coordinates on the explicit inverse denominator domain. -/
theorem inverseCayley_isEtaSkew (M : Mat4)
    (hmetric : M.transpose * eta * M = eta) (hM : IsUnit (M + 1)) :
    IsEtaSkew (inverseCayley M) := by
  change (inverseCayley M).transpose * eta + eta * inverseCayley M = 0
  apply (isUnit_transpose hM).mul_left_cancel
  apply hM.mul_right_cancel
  simp only [mul_zero, zero_mul]
  calc
    ((M + 1).transpose * ((inverseCayley M).transpose * eta + eta * inverseCayley M)) * (M + 1) =
        (inverseCayley M * (M + 1)).transpose * eta * (M + 1) +
          (M + 1).transpose * eta * (inverseCayley M * (M + 1)) := by
            rw [Matrix.transpose_mul]
            noncomm_ring
    _ = (M - 1).transpose * eta * (M + 1) + (M + 1).transpose * eta * (M - 1) := by
      rw [inverseCayley_mul_denominator M hM]
    _ = (M.transpose * eta * M - eta) + (M.transpose * eta * M - eta) := by
      simp only [Matrix.transpose_sub, Matrix.transpose_add, Matrix.transpose_one]
      noncomm_ring
    _ = 0 := by rw [hmetric]; simp

/-- On the actual Cayley domain, independent metric preservation is equivalent to the literal infinitesimal metric-skew equation. -/
theorem cayley_metric_iff (X : Mat4) (hX : IsUnit (1 - X)) :
    (cayley X).transpose * eta * cayley X = eta ↔ IsEtaSkew X := by
  constructor
  · intro h
    have hs := inverseCayley_isEtaSkew (cayley X) h (isUnit_cayley_add_one X hX)
    rw [inverseCayley_cayley X hX] at hs
    exact hs
  · intro hs
    exact cayley_metric X hs hX

/-- Literal metric skewness forces equal actual determinants for identity plus and identity minus the parameter. -/
theorem det_one_add_eq_one_sub (X : Mat4) (hX : IsEtaSkew X) :
    (1 + X).det = (1 - X).det := by
  have hs : X.transpose * eta = -(eta * X) := eq_neg_of_add_eq_zero_left hX
  have he : (1 + X).transpose * eta = eta * (1 - X) := by
    rw [Matrix.transpose_add, Matrix.transpose_one, add_mul, one_mul, hs]
    noncomm_ring
  have hd := congrArg Matrix.det he
  rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_mul, eta_det] at hd
  linarith

/-- A metric-skew parameter on the Cayley denominator domain has a unit numerator as a derived determinant consequence. -/
theorem isUnit_one_add (X : Mat4) (hskew : IsEtaSkew X) (hX : IsUnit (1 - X)) :
    IsUnit (1 + X) := by
  apply (Matrix.isUnit_iff_isUnit_det _).mpr
  rw [det_one_add_eq_one_sub X hskew]
  exact (Matrix.isUnit_iff_isUnit_det _).mp hX

/-- The Cayley reconstruction has actual determinant one on its metric-skew unit-denominator domain. -/
theorem cayley_det (X : Mat4) (hskew : IsEtaSkew X) (hX : IsUnit (1 - X)) :
    (cayley X).det = 1 := by
  rw [cayley, Matrix.det_mul, det_one_add_eq_one_sub X hskew, Matrix.det_nonsing_inv,
    Ring.inverse_eq_inv]
  exact mul_inv_cancel₀ ((cayley_domain_iff X).mp hX)

/-- The actual metric-skew Cayley reconstruction is a unit, derived from metric preservation rather than assumed as an input. -/
theorem cayley_isUnit (X : Mat4) (hskew : IsEtaSkew X) (hX : IsUnit (1 - X)) :
    IsUnit (cayley X) := isUnit_of_metric _ (cayley_metric X hskew hX)

end FoliationQM.LorentzCayleyAlgebra
