module
public import FoliationQM.DiracDensity
public import FoliationQM.RealLorentzFrame

/-!
# The symmetrized Dirac density of actual differentiable fields

Source: v13 `eq:dirac_lagrangian_sym`. The specified Lagrangian is an input.
The jet supplied to its actual spinor bilinears consists of actual real
Frechet derivatives in four specified directions. In flat real four-space,
these directions are the coordinate basis. The Dirac-adjoint row derivative
is the actual derivative of the row field, not an independent assignment.
No Euler--Lagrange equation or integrated stationary-action equivalence is
claimed by defining and identifying this local field density.
-/

@[expose] public section
noncomputable section
open scoped Matrix.Norms.Operator
namespace FoliationQM.DiracFieldDensity
open DiracMatrices DiracAdjoint MatrixDifferential DiracDensity
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The actual symmetrized Dirac density evaluated on Frechet derivatives in four specified directions. -/
def fieldDensity (hbar c m : ℝ) (psi : E → Spinor) (x : E) (directions : Fin 4 → E) : ℂ :=
  density hbar c m (psi x) (fun mu => fderiv ℝ psi x (directions mu))

/-- The real value of the actual field density. -/
def fieldDensityRe (hbar c m : ℝ) (psi : E → Spinor) (x : E) (directions : Fin 4 → E) : ℝ :=
  (fieldDensity hbar c m psi x directions).re

/-- The field density uses exactly the actual field derivatives as its first jet. -/
theorem fieldDensity_eq_density (hbar c m : ℝ) (psi : E → Spinor)
    (x : E) (directions : Fin 4 → E) :
    fieldDensity hbar c m psi x directions =
      density hbar c m (psi x) (fun mu => fderiv ℝ psi x (directions mu)) := rfl

/-- The real part faithfully represents the actual complex field density. -/
theorem fieldDensity_eq_ofReal (hbar c m : ℝ) (psi : E → Spinor)
    (x : E) (directions : Fin 4 → E) :
    fieldDensity hbar c m psi x directions = (fieldDensityRe hbar c m psi x directions : ℂ) := by
  simpa only [fieldDensity, fieldDensityRe, densityRe] using
    density_eq_ofReal hbar c m (psi x) (fun mu => fderiv ℝ psi x (directions mu))

/-- The actual field density equals the source symmetrized formula with the genuine derivative of the Dirac-adjoint row. -/
theorem fieldDensity_eq_row (hbar c m : ℝ) {psi : E → Spinor} {x : E}
    (hpsi : DifferentiableAt ℝ psi x) (directions : Fin 4 → E) :
    fieldDensity hbar c m psi x directions =
      (Complex.I * (hbar : ℂ) * (c : ℂ) / 2) *
        ∑ mu, (dotProduct (spinorAdjoint (psi x)) ((gamma mu).mulVec (fderiv ℝ psi x (directions mu))) -
          dotProduct (fderiv ℝ (fun y => spinorAdjoint (psi y)) x (directions mu))
            ((gamma mu).mulVec (psi x))) -
      ((m : ℂ) * (c : ℂ)^2) * dotProduct (spinorAdjoint (psi x)) (psi x) := by
  rw [fieldDensity, density_eq_row]
  simp only [fderiv_spinorAdjoint_apply hpsi]

/-- A differentiable real rescaling equal to one at the point changes only a real amplitude-gradient part of the actual derivative and leaves the field density unchanged. -/
theorem fieldDensity_rescale_at (hbar c m : ℝ) {psi : E → Spinor} {f : E → ℝ} {x : E}
    (hpsi : DifferentiableAt ℝ psi x) (hf : DifferentiableAt ℝ f x)
    (hfx : f x = 1) (directions : Fin 4 → E) :
    fieldDensity hbar c m (fun y => f y • psi y) x directions =
      fieldDensity hbar c m psi x directions := by
  have hd (mu : Fin 4) : fderiv ℝ (fun y => f y • psi y) x (directions mu) =
      fderiv ℝ psi x (directions mu) + (fderiv ℝ f x (directions mu)) • psi x := by
    have h := congrArg (fun T : E →L[ℝ] Spinor => T (directions mu))
      (hf.hasFDerivAt.smul hpsi.hasFDerivAt).fderiv
    simpa [hfx] using! h
  simp only [fieldDensity, hfx, one_smul, hd]
  exact density_add_real_amplitude hbar c m (psi x)
    (fun mu => fderiv ℝ psi x (directions mu)) (fun mu => fderiv ℝ f x (directions mu))

/-- The actual four-dimensional coordinate directions. -/
def coordinateDirections (mu : Fin 4) : Covector := Pi.single mu 1

/-- The actual flat-coordinate Dirac field density. -/
def coordinateDensity (hbar c m : ℝ) (psi : Covector → Spinor) (x : Covector) : ℂ :=
  fieldDensity hbar c m psi x coordinateDirections

/-- The coordinate density uses actual partial derivatives in the coordinate basis. -/
theorem coordinateDensity_eq (hbar c m : ℝ) (psi : Covector → Spinor) (x : Covector) :
    coordinateDensity hbar c m psi x =
      density hbar c m (psi x) (fun mu => fderiv ℝ psi x (Pi.single mu 1)) := rfl

end FoliationQM.DiracFieldDensity
