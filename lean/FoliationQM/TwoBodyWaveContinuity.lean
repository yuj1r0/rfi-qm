module

public import FoliationQM.TwoBodySchrodingerResidual
public import FoliationQM.TwoBodyMarginalContinuity
public import FoliationQM.HilbertFiberObservables

/-!
# Two-particle probability continuity directly from the complex wave

For v13 `eq:2p_continuity`, the imaginary part of the Schrödinger
residual multiplied by the conjugate wave gives the local balance of
Born density and the two particle currents. The derivation applies to
general complex waves, including at their zeros. Integrating the result
under the spatial regularity conditions gives `eq:marginal_continuity`.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.TwoBodyWaveContinuity

open TwoBodyCoordinates TwoBodyActionDensity TwoBodySchrodingerResidual LorentzCoordinates
  MeasureTheory MarginalParameterIntegral ObserverGaussianFisher
open scoped BigOperators ComplexConjugate

/-- Joint Born density of an arbitrary complex wave. -/
def born (ψ : Point → ℂ) (p : Point) : ℝ := ‖ψ p‖ ^ 2

/-- Scalar component of the probability current in the chosen particle direction. -/
def flux (h m : ℝ) (v : Point) (ψ : Point → ℂ) (p : Point) : ℝ :=
  (h / m) * (star (ψ p) * D v ψ p).im

variable {ψ : Point → ℂ} {p : Point}

/-- The squared-modulus derivative is twice the real part of the directional overlap. -/
theorem born_derivative (hψ : DifferentiableAt ℝ ψ p) (v : Point) :
    D v (born ψ) p = 2 * (star (ψ p) * D v ψ p).re := by
  change fderiv ℝ (HilbertFiberObservables.density ψ) p v = _
  rw [HilbertFiberObservables.density_fderiv ψ hψ v, RCLike.inner_apply']
  rfl

/-- First differentiability of a current component follows from local C² wave regularity. -/
theorem differentiableAt_flux (h m : ℝ) (v : Point) (hψ : ContDiffAt ℝ 2 ψ p) :
    DifferentiableAt ℝ (flux h m v ψ) p := by
  have hd : DifferentiableAt ℝ (D v ψ) p :=
    PolarRegularity.differentiableAt_directionalDerivative_of_contDiffAt_two hψ v
  have hc := Complex.conjCLE.toContinuousLinearMap.differentiableAt.comp p
    (hψ.differentiableAt (by norm_num))
  exact (Complex.imCLM.differentiableAt.comp p (hc.mul hd)).const_mul _

/-- The derivative square in the diagonal spatial current derivative is real,
leaving only the imaginary overlap with the wave's second derivative. -/
theorem flux_derivative (h m : ℝ) (v : Point) (hψ : ContDiffAt ℝ 2 ψ p) :
    D v (flux h m v ψ) p = (h / m) * (star (ψ p) * D v (D v ψ) p).im := by
  let d := D v ψ
  have hf := (hψ.differentiableAt (by norm_num)).hasFDerivAt
  have hc := Complex.conjCLE.toContinuousLinearMap.hasFDerivAt.comp p hf
  have hd : DifferentiableAt ℝ d p :=
    PolarRegularity.differentiableAt_directionalDerivative_of_contDiffAt_two hψ v
  have he := (Complex.imCLM.hasFDerivAt.comp p (hc.fun_mul hd.hasFDerivAt)).const_mul (h / m)
  change HasFDerivAt (flux h m v ψ) _ p at he
  change fderiv ℝ (flux h m v ψ) p v = _
  rw [he.fderiv]
  change (h / m) * (conj (ψ p) * (fderiv ℝ d p v) + d p * conj (d p)).im = _
  rw [mul_comm (d p), ← Complex.normSq_eq_conj_mul_self, Complex.add_im, Complex.ofReal_im, add_zero]
  rfl

/-- Time derivative plus the two spatial divergences of the actual scalar-wave currents. -/
def localBalance (h m₁ m₂ : ℝ) (ψ : Point → ℂ) : Point → ℝ :=
  TwoBodyMarginalContinuity.residual (born ψ) (fun i => flux h m₁ (leftAxis i) ψ)
    (fun i => flux h m₂ (rightAxis i) ψ)

private theorem coefficient (h m a : ℝ) : h ^ 2 / (2 * m) * a = (h / 2) * ((h / m) * a) := by
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- Off shell, the imaginary projection of the wave residual is half Planck's
constant times the probability balance. The real external potential contributes zero. -/
theorem residual_identity (h m₁ m₂ : ℝ) (V : Point → ℝ) (hψ : ContDiffAt ℝ 2 ψ p) :
    (star (ψ p) * schrodinger h m₁ m₂ V ψ p).im = (h / 2) * localBalance h m₁ m₂ ψ p := by
  have he : star (ψ p) * schrodinger h m₁ m₂ V ψ p =
      Complex.I * ((h : ℂ) * (star (ψ p) * Dt ψ p)) +
        (∑ j, ((h ^ 2 / (2 * mass m₁ m₂ j) : ℝ) : ℂ) *
          (star (ψ p) * D (axis j) (D (axis j) ψ) p)) -
        (V p : ℂ) * (star (ψ p) * ψ p) := by
    simp only [schrodinger, mul_sub, mul_add, Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]
  rw [he]
  have hreal : (star (ψ p) * ψ p).im = 0 := by
    rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_im]
  simp only [Complex.sub_im, Complex.add_im, Complex.I_mul_im, Complex.re_ofReal_mul,
    Complex.im_sum, Complex.im_ofReal_mul, hreal, mul_zero, sub_zero]
  simp only [Fintype.sum_sum_type, mass, axis, Sum.elim_inl, Sum.elim_inr, coefficient,
    ← Finset.mul_sum, localBalance,
    TwoBodyMarginalContinuity.residual, Dt, D₁, D₂, born_derivative (hψ.differentiableAt (by norm_num)),
    flux_derivative h m₁ _ hψ, flux_derivative h m₂ _ hψ]
  ring

/-- A C² complex wave satisfying the Schrödinger PDE conserves probability at
each point, including its nodes. -/
theorem continuity_of_schrodinger {h : ℝ} (hh : h ≠ 0) (m₁ m₂ : ℝ) (V : Point → ℝ)
    (hψ : ContDiffAt ℝ 2 ψ p) (hEq : schrodinger h m₁ m₂ V ψ p = 0) :
    localBalance h m₁ m₂ ψ p = 0 := by
  have he := (residual_identity h m₁ m₂ V hψ).symm
  rw [hEq, mul_zero, Complex.zero_im] at he
  exact (mul_eq_zero.mp he).resolve_left (div_ne_zero hh (by norm_num))

/-- Under local differentiation bounds and integrable remote flux and derivative,
the Schrödinger PDE gives the retained marginal continuity equation. -/
theorem marginal_of_schrodinger {h : ℝ} (hh : h ≠ 0) (m₁ m₂ : ℝ) (V : Point → ℝ) {b : Base}
    (hq : RegularAt (fun s y => born ψ (s,y)) b)
    (hj : ∀ i, RegularAt (fun s y => flux h m₁ (leftAxis i) ψ (s,y)) b)
    (hψ : ∀ y, ContDiffAt ℝ 2 ψ (b,y))
    (hi : ∀ i, Integrable (fun y => flux h m₂ (rightAxis i) ψ (b,y)))
    (hd : ∀ i, Integrable (fun y => fderiv ℝ (fun z => flux h m₂ (rightAxis i) ψ (b,z)) y (axes i)))
    (hEq : ∀ᵐ y, schrodinger h m₁ m₂ V ψ (b,y) = 0) :
    fderiv ℝ (fun s => ∫ y, born ψ (s,y)) b baseTime +
      (∑ i, fderiv ℝ (fun s => ∫ y, flux h m₁ (leftAxis i) ψ (s,y)) b (baseAxis i)) = 0 :=
  TwoBodyMarginalContinuity.of_joint hq hj
    (fun y => ((hψ y).norm_sq ℂ).differentiableAt (by norm_num))
    (fun i y => differentiableAt_flux h m₁ (leftAxis i) (hψ y))
    (fun i y => differentiableAt_flux h m₂ (rightAxis i) (hψ y))
    hi hd (hEq.mono fun y hy => continuity_of_schrodinger hh m₁ m₂ V (hψ y) hy)

end FoliationQM.TwoBodyWaveContinuity
