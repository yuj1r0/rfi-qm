module

public import FoliationQM.ScalarRestKinetic

/-!
# Neutralized derivatives on the chirally twisted scalar line

For v13 `eq:spinor_quadratic_exact` and `thm:dirac_lift`, a real chiral
angle twists an arbitrary complex multiple of the rest spinor. Its jet
contains both the complex scalar derivative and the half-angle derivative.
The two directions are Dirac-orthogonal and have opposite signed squares.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.TwistedScalarJet
open DiracMatrices DiracAdjoint ChiralMatrix ChiralNeutralization PolarSpinorBilinears
open ScalarRestKinetic SpinorRegularity
open scoped ComplexConjugate

/-- Apply the chiral matrix at the full angle to the scalar rest-spinor line. -/
def value (β : ℝ) (z : ℂ) : Spinor := (chiral β).mulVec (embed z)

/-- The twisted jet with complex scalar derivative dz and real full-angle derivative b. -/
def jet (β : ℝ) (z dz : ℂ) (b : ℝ) : Spinor :=
  (chiral β).mulVec (embed dz + (Complex.I * (b : ℂ) / 2 * z) • gamma5.mulVec restSpinor)

/-- Zero chiral angle gives the original scalar embedding. -/
theorem value_zero (z : ℂ) : value 0 z = embed z := by simp [value, chiral_zero]

private theorem bilinear_embed_self (z : ℂ) (M : Mat) :
    bilinear (embed z) M (embed z) = (Complex.normSq z : ℂ) * bilinear restSpinor M restSpinor := by
  rw [embed, bilinear_smul_left, bilinear_smul_right, Complex.star_def,
    Complex.normSq_eq_conj_mul_self]
  ring

/-- The real scalar and pseudoscalar invariants resolve the original density at the full angle. -/
theorem scalar_pseudoscalar_value (β : ℝ) (z : ℂ) :
    scalar (value β z) = Complex.normSq z * Real.cos β ∧
      pseudoscalar (value β z) = Complex.normSq z * Real.sin β := by
  constructor
  · simp only [scalar, value, bilinear_mulVec_both, chiral_diracAdjoint, mul_one,
      chiral_squared, bilinear_embed_self, bilinear_add_matrix, bilinear_smul_matrix,
      rest_scalar, rest_pseudoscalar, mul_one, mul_zero, add_zero, ← Complex.ofReal_mul,
      Complex.ofReal_re]
    exact mul_comm _ _
  · have hc : -Complex.I * bilinear (value β z) gamma5 (value β z) =
        ((Complex.normSq z * Real.sin β : ℝ) : ℂ) := by
      simp only [value, bilinear_mulVec_both, chiral_diracAdjoint, chiral_gamma5_sandwich,
        bilinear_embed_self, bilinear_add_matrix, bilinear_smul_matrix, rest_scalar,
        rest_pseudoscalar, mul_one, mul_zero, zero_add, Complex.ofReal_mul]
      linear_combination (norm := ring) -(Complex.normSq z : ℂ) * (Real.sin β : ℂ) * Complex.I_mul_I
    exact congrArg Complex.re hc

/-- The full chiral twist preserves the invariant density even when the scalar field vanishes. -/
theorem invariantDensity_value (β : ℝ) (z : ℂ) :
    invariantDensity (value β z) = Complex.normSq z := by
  obtain ⟨hs, ht⟩ := scalar_pseudoscalar_value β z
  rw [invariantDensity, hs, ht, mul_pow, mul_pow, ← mul_add, Real.cos_sq_add_sin_sq,
    mul_one, Real.sqrt_sq (Complex.normSq_nonneg z)]

/-- The twisted spinor lies in the strict polar domain precisely at nonzero scalar values. -/
theorem regular_value_iff (β : ℝ) (z : ℂ) : Regular (value β z) ↔ z ≠ 0 := by
  rw [Regular, invariantDensity_value, Complex.normSq_pos]

/-- The two rest directions have Dirac Gram matrix diag(1,−1). -/
theorem bilinear_rest_chiral (u a v b : ℂ) :
    bilinear (embed u + a • gamma5.mulVec restSpinor) 1 (embed v + b • gamma5.mulVec restSpinor) =
      conj u * v - conj a * b := by
  have addL (x y w : Spinor) : bilinear (x+y) 1 w = bilinear x 1 w + bilinear y 1 w := by
    simp [bilinear, add_dotProduct]
  have addR (w x y : Spinor) : bilinear w 1 (x+y) = bilinear w 1 x + bilinear w 1 y := by
    simp [bilinear, Matrix.mulVec_add, dotProduct_add]
  have hR : bilinear restSpinor 1 (gamma5.mulVec restSpinor) = 0 := by
    rw [← bilinear_mul_matrix, one_mul, rest_pseudoscalar]
  have hL : bilinear (gamma5.mulVec restSpinor) 1 restSpinor = 0 := by
    rw [bilinear_mulVec_left, diracAdjoint_gamma5, mul_one, bilinear_neg_matrix, rest_pseudoscalar, neg_zero]
  have hG : bilinear (gamma5.mulVec restSpinor) 1 (gamma5.mulVec restSpinor) = -1 := by
    rw [bilinear_mulVec_both, diracAdjoint_gamma5, mul_one, neg_mul, gamma5_sq, bilinear_neg_matrix, rest_scalar]
  simp only [embed, addL, addR, bilinear_smul_left, bilinear_smul_right, Complex.star_def,
    rest_scalar, hL, hR, hG, mul_zero, zero_add, add_zero, mul_one]
  ring

/-- The full complex neutralized jet square keeps the scalar kinetic term and the negative chiral term. -/
theorem jet_square (β : ℝ) (z dz : ℂ) (b : ℝ) :
    bilinear (jet β z dz b) (neutralizer β) (jet β z dz b) =
      ((Complex.normSq dz - (b^2 / 4) * Complex.normSq z : ℝ) : ℂ) := by
  rw [jet, bilinear_mulVec_both, chiral_diracAdjoint, chiral_neutralizer_chiral,
    bilinear_rest_chiral, ← Complex.normSq_eq_conj_mul_self, ← Complex.normSq_eq_conj_mul_self,
    ← Complex.ofReal_sub]
  have htwo : Complex.normSq (2 : ℂ) = 4 := by norm_num [Complex.normSq_apply]
  simp only [Complex.normSq_mul, Complex.normSq_div, Complex.normSq_I, Complex.normSq_ofReal, one_mul, htwo]
  ring_nf

end FoliationQM.TwistedScalarJet
