module

public import FoliationQM.MassiveSpinKinetic
public import FoliationQM.ActionVariation

/-!
# Scalar Klein–Gordon density on the complex rest-spinor line

For v13 `thm:dirac_lift` (iii) and `eq:coupled_action`, take a scalar
field times the constant normalized rest spinor. Its neutralized
quadratic kinetic term at zero chiral angle is exactly the scalar
Klein–Gordon kinetic term. Subtracting the scalar mass density gives
the full massive action density, including at zeros of the field.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.ScalarRestKinetic

open DiracMatrices DiracAdjoint SpinorRegularity NeutralizedSpinorKinetic
open DiracFieldDensity ActionVariation PolarSecondDifferential
open scoped ComplexConjugate

/-- Embed the complex scalar as a multiple of the normalized rest spinor. -/
def embed (z : ℂ) : Spinor := z • restSpinor

/-- The corresponding spacetime field in the complex rest-spinor line. -/
def lift (z : Covector → ℂ) (x : Covector) : Spinor := embed (z x)

/-- Restricting the Dirac scalar pairing to this line gives the usual Hermitian pairing. -/
theorem bilinear_embed (z w : ℂ) : bilinear (embed z) 1 (embed w) = conj z * w := by
  simp only [embed, bilinear_smul_left, bilinear_smul_right, rest_scalar, mul_one,
    Complex.star_def]
  exact mul_comm _ _

/-- The scalar and pseudoscalar invariants of an embedded scalar. -/
theorem scalar_pseudoscalar_embed (z : ℂ) :
    scalar (embed z) = Complex.normSq z ∧ pseudoscalar (embed z) = 0 := by
  constructor
  · simp only [scalar, bilinear_embed, ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re]
  · simp only [pseudoscalar, embed, bilinear_smul_left, bilinear_smul_right,
      rest_pseudoscalar, mul_zero, Complex.zero_re]

/-- The actual invariant spinor density is the scalar Born density. -/
theorem invariantDensity_embed (z : ℂ) : invariantDensity (embed z) = Complex.normSq z := by
  rw [invariantDensity, (scalar_pseudoscalar_embed z).1, (scalar_pseudoscalar_embed z).2]
  simpa using Real.sqrt_sq (Complex.normSq_nonneg z)

/-- The regular polar chart of a rest-line spinor is available exactly away from a scalar zero. -/
theorem regular_embed_iff (z : ℂ) : Regular (embed z) ↔ z ≠ 0 := by
  rw [Regular, invariantDensity_embed, Complex.normSq_pos]

/-- Smooth scalar fields produce smooth embedded fields at the same order. -/
theorem contDiffAt_lift {n : WithTop ℕ∞} {z : Covector → ℂ} {x : Covector}
    (hz : ContDiffAt ℝ n z x) : ContDiffAt ℝ n (lift z) x :=
  hz.smul contDiffAt_const

/-- Every genuine Fréchet derivative of the lifted field is the embedded scalar derivative. -/
theorem fderiv_lift_apply {z : Covector → ℂ} {x : Covector} (hz : DifferentiableAt ℝ z x)
    (v : Covector) : fderiv ℝ (lift z) x v = embed (fderiv ℝ z x v) := by
  change fderiv ℝ (fun y => z y • restSpinor) x v = _
  rw [(hz.hasFDerivAt.smul_const restSpinor).fderiv, ContinuousLinearMap.smulRight_apply]
  rfl

/-- Exact complex identity for all four derivatives in the supplied directions. -/
theorem fieldKinetic_lift (hbar : ℝ) {z : Covector → ℂ} {x : Covector}
    (hz : DifferentiableAt ℝ z x) (e : Fin 4 → Covector) :
    fieldKinetic hbar 0 (lift z) x e =
      (hbar : ℂ)^2 * kineticPairing (fun μ => directionalDerivative z (e μ) x)
        (fun μ => directionalDerivative z (e μ) x) := by
  simp only [fieldKinetic, kinetic, ChiralNeutralization.neutralizer, mul_zero,
    ChiralMatrix.chiral_zero, fderiv_lift_apply hz, bilinear_embed]
  congr 1
  simp [RealLorentzFrame.sign, Fin.sum_univ_four, kineticPairing, directionalDerivative]
  ring

/-- The mass-completed real contraction is the scalar Klein–Gordon field pairing.
The differentiable field may take the value zero at the evaluation point. -/
theorem completed_eq_pairing (p : MassiveParameters) {z : Covector → ℂ} {x : Covector}
    (hz : DifferentiableAt ℝ z x) :
    MassiveSpinKinetic.density p 0 (lift z) x =
      (fieldPairing p z z coordinateDirections x).re := by
  simp only [MassiveSpinKinetic.density, fieldKineticRe, fieldKinetic_lift p.hbar hz,
    lift, invariantDensity_embed, fieldPairing, pairing, Complex.sub_re]
  congr 1
  rw [show (p.m : ℂ)^2 * (p.c : ℂ)^2 * conj (z x) * z x =
      ((p.m^2 * p.c^2 : ℝ) : ℂ) * (conj (z x) * z x) by push_cast; ring,
    ← Complex.normSq_eq_conj_mul_self, ← Complex.ofReal_mul, Complex.ofReal_re]
  ring

end FoliationQM.ScalarRestKinetic
