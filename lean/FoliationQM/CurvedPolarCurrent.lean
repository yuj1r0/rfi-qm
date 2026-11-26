module

public import FoliationQM.CurvedWaveDivergence
public import FoliationQM.CurvedGradientCovariance

/-!
# Actual divergence of the curved polar phase current

The density-weighted phase gradient has coordinate volume flux
`R² μ g⁻¹ dS`. Its divergence is differentiated as an actual field.
The product rule gives the amplitude-gradient term and the phase wave
operator appearing in the imaginary part of the curved Klein–Gordon
equation. A spacetime-constant mass rescales this to the velocity current.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.CurvedPolarCurrent

open LorentzMatrixGroup RNCCoordinateConnection RNCVolumeDensity CurvedWaveDivergence
  CurvedGradientCovariance
open scoped Matrix.Norms.Operator Topology BigOperators

/-- The actual coordinate volume flux of the density-weighted phase gradient. -/
def currentFlux (g : Covector → Mat4) (R S : Covector → ℝ) (x : Covector) (i : Fin 4) : ℝ :=
  R x ^ 2 * flux g S x i

/-- The coordinate metric divergence of the phase current uses actual Fréchet derivatives of its flux. -/
def currentDivergence (g : Covector → Mat4) (R S : Covector → ℝ) (x : Covector) : ℝ :=
  (volumeFactor (g x))⁻¹ * ∑ i, fderiv ℝ (fun y => currentFlux g R S y i) x (axis i)

/-- Contraction against the phase flux is the volume times the inverse-metric gradient pairing. -/
theorem flux_pairing (g : Covector → Mat4) (R S : Covector → ℝ) (x : Covector) :
    (∑ i, fderiv ℝ R x (axis i) * flux g S x i) =
      volumeFactor (g x) * pairing g R S x := by
  simp only [flux, coefficient, smul_eq_mul, pairing, RNCHalfDensityJet.form_apply, components,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

variable {g : Covector → Mat4} {R S : Covector → ℝ} {x : Covector}

/-- The current flux is differentiable under first-order amplitude and second-order phase regularity. -/
theorem currentFlux_differentiable (hg : DifferentiableAt ℝ g x) (hd : (g x).det < 0)
    (hR : DifferentiableAt ℝ R x) (hS : ContDiffAt ℝ 2 S x) (i : Fin 4) :
    DifferentiableAt ℝ (fun y => currentFlux g R S y i) x :=
  (hR.pow 2).mul (hasFDerivAt_flux (coefficient_differentiable hg hd) hS i).differentiableAt

/-- Differentiating each densitized current component gives its two literal product-rule terms. -/
theorem currentFlux_derivative (hg : DifferentiableAt ℝ g x) (hd : (g x).det < 0)
    (hR : DifferentiableAt ℝ R x) (hS : ContDiffAt ℝ 2 S x) (i : Fin 4) (v : Covector) :
    fderiv ℝ (fun y => currentFlux g R S y i) x v =
      (2 * R x * fderiv ℝ R x v) * flux g S x i +
        R x ^ 2 * fderiv ℝ (fun y => flux g S y i) x v := by
  have hflux := (hasFDerivAt_flux (coefficient_differentiable hg hd) hS i).differentiableAt
  have H := ((hR.hasFDerivAt.pow 2).mul hflux.hasFDerivAt).fderiv
  change fderiv ℝ (fun y => R y ^ 2 * flux g S y i) x = _ at H
  change fderiv ℝ (fun y => R y ^ 2 * flux g S y i) x v = _
  rw [H]
  simp only [add_apply, smul_apply, smul_eq_mul, Nat.reduceSub, pow_one, two_smul]
  ring

/-- The actual current divergence is the curved polar continuity expression. No symmetry or positive-amplitude premise is needed. -/
theorem currentDivergence_eq (hg : DifferentiableAt ℝ g x) (hd : (g x).det < 0)
    (hR : DifferentiableAt ℝ R x) (hS : ContDiffAt ℝ 2 S x) :
    currentDivergence g R S x =
      2 * R x * pairing g R S x + R x ^ 2 * wave g S x := by
  have hμ : volumeFactor (g x) ≠ 0 := (Real.sqrt_pos.2 (neg_pos.mpr hd)).ne'
  have hf : (∑ i, (2 * R x * fderiv ℝ R x (axis i)) * flux g S x i) =
      (2 * R x) * (volumeFactor (g x) * pairing g R S x) := by
    rw [← flux_pairing, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  simp only [currentDivergence, currentFlux_derivative hg hd hR hS, Finset.sum_add_distrib,
    ← Finset.mul_sum, hf, wave, smul_eq_mul]
  field_simp [hμ]

/-- A constant multiple of the actual densitized phase flux has the same multiple of its divergence. -/
theorem scaled_currentDivergence (a : ℝ) (hg : DifferentiableAt ℝ g x) (hd : (g x).det < 0)
    (hR : DifferentiableAt ℝ R x) (hS : ContDiffAt ℝ 2 S x) :
    (volumeFactor (g x))⁻¹ * ∑ i,
      fderiv ℝ (fun y => a * currentFlux g R S y i) x (axis i) = a * currentDivergence g R S x := by
  have he (i : Fin 4) :=
    ((currentFlux_differentiable hg hd hR hS i).hasFDerivAt.const_mul a).fderiv
  simp only [he, smul_apply, smul_eq_mul, currentDivergence,
    ← Finset.mul_sum]
  ring

/-- The volume flux for `R² w`, where the phase velocity is `w = −g⁻¹dS/M` for constant bare mass. -/
def velocityCurrentFlux (M : ℝ) (g : Covector → Mat4) (R S : Covector → ℝ)
    (x : Covector) (i : Fin 4) : ℝ :=
  -(1 / M) * currentFlux g R S x i

/-- The scaled flux is literally the metric volume times `R²` times the raised phase velocity. -/
theorem velocityCurrentFlux_eq (M : ℝ) (g : Covector → Mat4) (R S : Covector → ℝ)
    (x : Covector) (i : Fin 4) :
    velocityCurrentFlux M g R S x i = volumeFactor (g x) *
      (R x ^ 2 * (-((g x)⁻¹.mulVec (components S x) i) / M)) := by
  have he : flux g S x i = volumeFactor (g x) *
      ((g x)⁻¹.mulVec (components S x) i) := by
    simp only [flux, coefficient, smul_eq_mul, Matrix.mulVec, dotProduct, components,
      Finset.mul_sum, mul_assoc]
  rw [velocityCurrentFlux, currentFlux, he]
  ring

/-- Differentiating the constant-mass velocity current preserves the exact phase-current scaling. -/
theorem velocityCurrentDivergence_eq (M : ℝ) (hg : DifferentiableAt ℝ g x) (hd : (g x).det < 0)
    (hR : DifferentiableAt ℝ R x) (hS : ContDiffAt ℝ 2 S x) :
    (volumeFactor (g x))⁻¹ * ∑ i,
      fderiv ℝ (fun y => velocityCurrentFlux M g R S y i) x (axis i) =
        -(1 / M) * (2 * R x * pairing g R S x + R x ^ 2 * wave g S x) := by
  unfold velocityCurrentFlux
  rw [scaled_currentDivergence _ hg hd hR hS, currentDivergence_eq hg hd hR hS]

end FoliationQM.CurvedPolarCurrent
