module

public import FoliationQM.CurvedFluxGreen
public import Mathlib.Analysis.Calculus.FDeriv.Star

/-!
# Green's identities with the boundary divergence retained

In coordinates the first Green identity for the curved scalar action splits
the derivative of a weighted boundary flux into the kinetic pairing and the
wave term. Subtracting the conjugate identity with exchanged fields gives
the second Green identity for a symmetric metric. These pointwise identities
apply to real and complex fields.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.CurvedGreenBoundary

open LorentzMatrixGroup RNCCoordinateConnection RNCVolumeDensity CurvedWaveDivergence CurvedFluxGreen
open scoped Matrix.Norms.Operator

variable {K : Type*} [RCLike K] {g : Covector → Mat4} {u f : Covector → K} {x : Covector}

/-- The boundary flux pairs the conjugated test field with the densitized gradient of the background. -/
def boundaryFlux (g : Covector → Mat4) (u f : Covector → K) (x : Covector) (i : Fin 4) : K :=
  star (u x) * flux g f x i

/-- The boundary term is the actual coordinate divergence of the test-field flux. -/
def boundaryDivergence (g : Covector → Mat4) (u f : Covector → K) (x : Covector) : K :=
  ∑ i, fderiv ℝ (fun y => boundaryFlux g u f y i) x (axis i)

/-- The directional product rule separates the differentiated test field from the differentiated flux. -/
theorem boundaryFlux_partial (hg : DifferentiableAt ℝ g x) (hdet : (g x).det < 0)
    (hu : DifferentiableAt ℝ u x) (hf : ContDiffAt ℝ 2 f x) (i : Fin 4) :
    fderiv ℝ (fun y => boundaryFlux g u f y i) x (axis i) =
      star (fderiv ℝ u x (axis i)) * flux g f x i +
      star (u x) * fderiv ℝ (fun y => flux g f y i) x (axis i) := by
  have hflux := (hasFDerivAt_flux (coefficient_differentiable hg hdet) hf i).differentiableAt
  change fderiv ℝ (fun y => star (u y) * flux g f y i) x (axis i) = _
  rw [fderiv_fun_mul hu.star hflux, fderiv_star]
  simp only [add_apply, smul_apply, smul_eq_mul, ContinuousLinearMap.comp_apply]
  change star (u x) * _ + _ * star _ = _
  ring

/-- The local first Green identity retains the full boundary divergence before integration. -/
theorem first_green (hg : DifferentiableAt ℝ g x) (hdet : (g x).det < 0)
    (hu : DifferentiableAt ℝ u x) (hf : ContDiffAt ℝ 2 f x) :
    boundaryDivergence g u f x = volumeFactor (g x) • kinetic g u f x +
      volumeFactor (g x) • (star (u x) * wave g f x) := by
  simp only [boundaryDivergence, boundaryFlux_partial hg hdet hu hf, Finset.sum_add_distrib]
  rw [kinetic_flux, wave_flux hdet]

/-- A symmetric inverse metric makes the kinetic form Hermitian for real or complex fields. -/
theorem kinetic_hermitian (hs : (g x).IsSymm) (u f : Covector → K) :
    star (kinetic g f u x) = kinetic g u f x := by
  simp only [kinetic, star_sum, star_smul, star_trivial, star_mul, star_star]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by rw [hs.inv.apply i j]

/-- The local second Green identity equals the difference of the two boundary divergences. -/
theorem second_green (hg : DifferentiableAt ℝ g x) (hdet : (g x).det < 0) (hs : (g x).IsSymm)
    (hu : ContDiffAt ℝ 2 u x) (hf : ContDiffAt ℝ 2 f x) :
    boundaryDivergence g u f x - star (boundaryDivergence g f u x) =
      volumeFactor (g x) • (star (u x) * wave g f x - star (wave g u x) * f x) := by
  rw [first_green hg hdet (hu.differentiableAt (by decide)) hf,
    first_green hg hdet (hf.differentiableAt (by decide)) hu]
  simp only [star_add, star_smul, star_trivial, star_mul, star_star, kinetic_hermitian hs, smul_sub]
  abel

open MeasureTheory

/-- On a measurable region the integrated first Green identity keeps the boundary
divergence integral when the second-order and kinetic terms are integrable. -/
theorem integral_first_green {s : Set Covector} (hs : MeasurableSet s)
    (hg : ∀ x ∈ s, DifferentiableAt ℝ g x) (hdet : ∀ x ∈ s, (g x).det < 0)
    (hu : ∀ x ∈ s, DifferentiableAt ℝ u x) (hf : ∀ x ∈ s, ContDiffAt ℝ 2 f x)
    (hk : IntegrableOn (fun x => volumeFactor (g x) • kinetic g u f x) s)
    (hw : IntegrableOn (fun x => volumeFactor (g x) • (star (u x) * wave g f x)) s) :
    (∫ x in s, boundaryDivergence g u f x) =
      (∫ x in s, volumeFactor (g x) • kinetic g u f x) +
      ∫ x in s, volumeFactor (g x) • (star (u x) * wave g f x) := by
  rw [← integral_add hk hw]
  exact integral_congr_ae <| (ae_restrict_mem hs).mono fun x hx =>
    first_green (hg x hx) (hdet x hx) (hu x hx) (hf x hx)

end FoliationQM.CurvedGreenBoundary
