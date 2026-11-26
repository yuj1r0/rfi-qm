module
public import FoliationQM.DiracActionSupport
public import FoliationQM.DiracResidualPairing
public import FoliationQM.DiracCurrent

/-!
# The first Dirac variation as residual pairing plus divergence

For v13 `thm:dirac_lift`, the derivative of the symmetric Dirac density
splits pointwise into the physical residual and a flux term. Differentiating
the test and field entries of the actual gamma contraction gives the full
directional derivative of the flux. The sign and coefficients follow from
the original iℏc/2 kinetic term and −mc² mass term.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.DiracVariationFlux
open DiracMatrices DiracAdjoint DiracResidualPairing DiracPolarizedDensity
open DiracFieldDensity DiracEquation DiracActionSupport

/-- The real μ-component of the variational flux, ordered with the test in the
Dirac-adjoint slot and the original field in the right slot. -/
def flux (hbar c : ℝ) (ψ η : Covector → Spinor) (μ : Fin 4) (x : Covector) : ℝ :=
  hbar * c * (bilinear (η x) (gamma μ) (ψ x)).im

/-- The imaginary gamma contraction can also be evaluated by a real residual pairing. -/
theorem flux_eq_pair (hbar c : ℝ) (ψ η : Covector → Spinor) (μ : Fin 4) (x : Covector) :
    flux hbar c ψ η μ x = hbar * c * pair (Complex.I • η x) ((gamma μ).mulVec (ψ x)) := by
  simp [flux, pair, bilinear_smul_left, bilinear_gamma_right, Complex.mul_re]

private def gammaAction (μ : Fin 4) : Spinor →L[ℝ] Spinor :=
  ((Matrix.toLin' (gamma μ)).restrictScalars ℝ).toContinuousLinearMap

/-- The flux inherits the differentiability order of the two actual spinor fields. -/
theorem contDiffAt_flux (hbar c : ℝ) (ψ η : Covector → Spinor) (μ : Fin 4)
    {n : WithTop ℕ∞} {x : Covector} (hψ : ContDiffAt ℝ n ψ x) (hη : ContDiffAt ℝ n η x) :
    ContDiffAt ℝ n (flux hbar c ψ η μ) x := by
  have hγ := (gammaAction μ).contDiff.contDiffAt.comp x hψ
  have hp := (pairCLM.contDiff.contDiffAt.comp x (hη.const_smul Complex.I)).clm_apply hγ
  simp_rw [show flux hbar c ψ η μ = fun y =>
    hbar * c * pair (Complex.I • η y) ((gamma μ).mulVec (ψ y)) from funext (flux_eq_pair hbar c ψ η μ)]
  have hconst : ContDiffAt ℝ n (fun _ : Covector => hbar * c) x := contDiffAt_const
  exact hconst.mul hp

/-- The derivative of the flux in any actual spacetime direction includes the
derivative of each of its two spinors. -/
theorem fderiv_flux_apply (hbar c : ℝ) (ψ η : Covector → Spinor) (μ : Fin 4) (x v : Covector)
    (hψ : DifferentiableAt ℝ ψ x) (hη : DifferentiableAt ℝ η x) :
    fderiv ℝ (flux hbar c ψ η μ) x v =
      hbar * c * ((bilinear (fderiv ℝ η x v) (gamma μ) (ψ x)).im +
        (bilinear (η x) (gamma μ) (fderiv ℝ ψ x v)).im) := by
  let b := fun y => bilinear (η y) (gamma μ) (ψ y)
  have hb : DifferentiableAt ℝ b x := DiracCurrent.differentiableAt_bilinear hη hψ (gamma μ)
  have H := (Complex.imCLM.hasFDerivAt.comp x hb.hasFDerivAt).const_mul (hbar * c)
  have E := congrArg (fun L : Covector →L[ℝ] ℝ => L v) H.fderiv
  change fderiv ℝ (flux hbar c ψ η μ) x v = hbar * c * (fderiv ℝ b x v).im at E
  rw [E, show fderiv ℝ b x v = _ from DiracCurrent.fderiv_bilinear_apply hη hψ (gamma μ) v,
    Complex.add_im]

/-- Exact real algebra at independent jets, with the source residual normalized as iℏγ·∂ − mc. -/
theorem jet_split (hbar c m : ℝ) (ψ : Spinor) (dψ : Fin 4 → Spinor) (η : Spinor) (dη : Fin 4 → Spinor) :
    2 * (mixed hbar c m η dη ψ dψ).re =
      2 * c * pair η (diracJet hbar m c ψ dψ) +
        ∑ μ, hbar * c * ((bilinear (dη μ) (gamma μ) ψ).im + (bilinear η (gamma μ) (dψ μ)).im) := by
  have hK : Complex.I * (hbar : ℂ) * (c : ℂ) / 2 = ((hbar * c / 2 : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  have hM : (m : ℂ) * (c : ℂ) ^ 2 = ((m * c ^ 2 : ℝ) : ℂ) := by push_cast; rfl
  rw [mixed, hK, hM, pair_diracJet]
  simp only [mul_assoc, Complex.sub_re, Complex.re_ofReal_mul, Complex.I_mul_re, Complex.im_sum,
    Complex.sub_im, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, pair]
  ring

/-- The true first density equals twice c times the physical residual pairing
plus the divergence of the actual four flux components. -/
theorem first_eq_residual_add_div (hbar c m : ℝ) (ψ η : Covector → Spinor) (x : Covector)
    (hψ : DifferentiableAt ℝ ψ x) (hη : DifferentiableAt ℝ η x) :
    first hbar c m ψ η x = 2 * c * pair (η x) (diracField hbar m c ψ x) +
      ∑ μ, fderiv ℝ (flux hbar c ψ η μ) x (coordinateDirections μ) := by
  simp only [fderiv_flux_apply hbar c ψ η _ x _ hψ hη]
  exact jet_split hbar c m (ψ x) (fun μ => fderiv ℝ ψ x (coordinateDirections μ))
    (η x) (fun μ => fderiv ℝ η x (coordinateDirections μ))

end FoliationQM.DiracVariationFlux
