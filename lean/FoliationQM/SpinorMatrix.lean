module
public import FoliationQM.SpinorRegularity
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Tactic.Ring

/-!
# Concrete real-linear spinor matrix model

Sources: the regular-domain polar reconstruction in v13 `prop:takabayasi`,
`eq:takabayasi_polar`, and `eq:scalar_pseudoscalar_bilinears`.
A four-component Dirac spinor is encoded as an actual complex two-by-two
matrix. The inverse, real linearity, determinant, and invariant density are
proved directly from the existing Dirac representation. In particular the
pseudoscalar sign is the established minus-i bilinear convention.

This file constructs a concrete coordinate equivalence. It does not assume
or assert a classification of the spin group, a Lorentz lift, or a global
choice of polar phase. Matrix continuity uses the existing operator norm.
-/

@[expose] public section
noncomputable section
open scoped Matrix.Norms.Operator
namespace FoliationQM.SpinorMatrix
open DiracMatrices DiracAdjoint

/-- The actual complex two-by-two matrix space for the spinor coordinate model. -/
abbrev Mat2 := Matrix (Fin 2) (Fin 2) ℂ

/-- Encode the four Dirac components as a concrete complex two-by-two matrix. -/
def toMatrix (psi : Spinor) : Mat2 :=
  !![psi 0 + psi 2, -star (psi 1 - psi 3);
     psi 1 + psi 3, star (psi 0 - psi 2)]

/-- Recover the four Dirac components by the explicit conjugate half-sum inverse. -/
def ofMatrix (M : Mat2) : Spinor :=
  ![(M 0 0 + star (M 1 1)) / 2,
    (M 1 0 - star (M 0 1)) / 2,
    (M 0 0 - star (M 1 1)) / 2,
    (M 1 0 + star (M 0 1)) / 2]

/-- The explicit inverse recovers every actual four-component spinor. -/
theorem ofMatrix_toMatrix (psi : Spinor) : ofMatrix (toMatrix psi) = psi := by
  ext i
  fin_cases i <;> simp [ofMatrix, toMatrix] <;> ring

/-- Encoding the explicit inverse recovers every complex two-by-two matrix. -/
theorem toMatrix_ofMatrix (M : Mat2) : toMatrix (ofMatrix M) = M := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ofMatrix, toMatrix] <;> ring

/-- The fixed source rest spinor is encoded by the actual identity matrix. -/
theorem toMatrix_restSpinor : toMatrix restSpinor = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [toMatrix, restSpinor, Matrix.one_apply]

/-- The concrete spinor matrix encoding preserves addition. -/
theorem toMatrix_add (psi chi : Spinor) : toMatrix (psi + chi) = toMatrix psi + toMatrix chi := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [toMatrix] <;> ring

/-- The concrete spinor matrix encoding preserves real scalar multiplication. -/
theorem toMatrix_real_smul (r : ℝ) (psi : Spinor) :
    toMatrix (r • psi) = r • toMatrix psi := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [toMatrix, smul_add, smul_sub]

/-- The concrete encoding and inverse form a real-linear equivalence. -/
def linearEquiv : Spinor ≃ₗ[ℝ] Mat2 where
  toFun := toMatrix
  invFun := ofMatrix
  left_inv := ofMatrix_toMatrix
  right_inv := toMatrix_ofMatrix
  map_add' := toMatrix_add
  map_smul' := toMatrix_real_smul

/-- The finite-dimensional real-linear spinor matrix equivalence is continuous in both directions. -/
def continuousLinearEquiv : Spinor ≃L[ℝ] Mat2 := linearEquiv.toContinuousLinearEquiv

/-- The continuous real-linear equivalence evaluates to the explicit matrix encoding. -/
theorem continuousLinearEquiv_apply (psi : Spinor) :
    continuousLinearEquiv psi = toMatrix psi := rfl

/-- The inverse continuous real-linear equivalence evaluates to the explicit spinor reconstruction. -/
theorem continuousLinearEquiv_symm_apply (M : Mat2) :
    continuousLinearEquiv.symm M = ofMatrix M := rfl

/-- The actual determinant is the scalar invariant plus i times the established real pseudoscalar invariant. -/
theorem det_toMatrix (psi : Spinor) :
    Matrix.det (toMatrix psi) =
      (SpinorRegularity.scalar psi : ℂ) + Complex.I * (SpinorRegularity.pseudoscalar psi : ℂ) := by
  rw [SpinorRegularity.scalar_as_complex, SpinorRegularity.pseudoscalar_as_complex]
  simp [toMatrix, Matrix.det_fin_two, bilinear, gamma, gamma5_explicit,
    Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  ring_nf
  simp
  ring

/-- The real part of the matrix determinant is the actual scalar spinor invariant. -/
theorem det_toMatrix_re (psi : Spinor) :
    (Matrix.det (toMatrix psi)).re = SpinorRegularity.scalar psi := by
  simp [det_toMatrix]

/-- The imaginary part of the matrix determinant is the actual signed pseudoscalar invariant. -/
theorem det_toMatrix_im (psi : Spinor) :
    (Matrix.det (toMatrix psi)).im = SpinorRegularity.pseudoscalar psi := by
  simp [det_toMatrix]

/-- The matrix determinant vanishes exactly when both actual invariant bilinears vanish. -/
theorem det_eq_zero_iff (psi : Spinor) :
    Matrix.det (toMatrix psi) = 0 ↔
      SpinorRegularity.scalar psi = 0 ∧ SpinorRegularity.pseudoscalar psi = 0 := by
  constructor
  · intro h
    constructor
    · have hr := congrArg Complex.re h
      simpa [det_toMatrix_re] using hr
    · have hi := congrArg Complex.im h
      simpa [det_toMatrix_im] using hi
  · rintro ⟨hs, hp⟩
    simp [det_toMatrix, hs, hp]

/-- Nonzero determinant is equivalent to the source strict invariant regularity domain. -/
theorem det_ne_zero_iff_regular (psi : Spinor) :
    Matrix.det (toMatrix psi) ≠ 0 ↔ SpinorRegularity.Regular psi := by
  change ¬ Matrix.det (toMatrix psi) = 0 ↔ SpinorRegularity.Regular psi
  rw [det_eq_zero_iff, SpinorRegularity.regular_iff_invariants_nonzero]
  tauto

/-- The complex norm of the actual determinant is exactly the source invariant density. -/
theorem norm_det_toMatrix (psi : Spinor) :
    ‖Matrix.det (toMatrix psi)‖ = SpinorRegularity.invariantDensity psi := by
  rw [Complex.norm_def]
  simp [Complex.normSq_apply, det_toMatrix_re, det_toMatrix_im, SpinorRegularity.invariantDensity, pow_two]

/-- The concrete matrix encoding distinguishes every pair of actual Dirac spinors. -/
theorem toMatrix_injective : Function.Injective toMatrix := linearEquiv.injective

/-- Every complex two-by-two matrix is the encoding of an actual Dirac spinor. -/
theorem toMatrix_surjective : Function.Surjective toMatrix := linearEquiv.surjective

/-- Nonzero determinant is exactly strict positivity of the actual invariant density. -/
theorem det_ne_zero_iff_invariantDensity_pos (psi : Spinor) :
    Matrix.det (toMatrix psi) ≠ 0 ↔ 0 < SpinorRegularity.invariantDensity psi :=
  det_ne_zero_iff_regular psi

end FoliationQM.SpinorMatrix
