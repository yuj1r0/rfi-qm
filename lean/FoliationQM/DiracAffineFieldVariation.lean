module
public import FoliationQM.DiracPolarizedDensity
public import FoliationQM.DiracFieldDensity

/-!
# Varying the actual symmetrized Dirac field density

For v13 `thm:dirac_lift` and `eq:dirac_lagrangian_sym`, vary a spinor field
along a real affine line. The spatial derivatives are the actual Fréchet
derivatives of the varied field. The exact quadratic expansion gives its
first variation without any assumption of strict spinor regularity.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.DiracAffineFieldVariation
open DiracMatrices DiracFieldDensity DiracPolarizedDensity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- An affine variation of a spinor field with real parameter. -/
def affine (ψ η : E → Spinor) (t : ℝ) (x : E) : Spinor := ψ x + t • η x

/-- Its spatial first jet is the same affine variation of the two spatial first jets. -/
theorem fderiv_affine_apply (ψ η : E → Spinor) (x v : E)
    (hψ : DifferentiableAt ℝ ψ x) (hη : DifferentiableAt ℝ η x) (t : ℝ) :
    fderiv ℝ (affine ψ η t) x v = fderiv ℝ ψ x v + t • fderiv ℝ η x v := by
  have H := hψ.hasFDerivAt.add (hη.hasFDerivAt.const_smul t)
  exact congrArg (fun L : E →L[ℝ] Spinor => L v) H.fderiv

/-- Coefficient of the real variation parameter, with both the field and its spatial jet varied. -/
def firstDensity (hbar c m : ℝ) (ψ η : E → Spinor) (x : E) (v : Fin 4 → E) : ℝ :=
  2 * (mixed hbar c m (η x) (fun μ => fderiv ℝ η x (v μ))
    (ψ x) (fun μ => fderiv ℝ ψ x (v μ))).re

/-- The symmetrized field density is exactly quadratic along the affine variation. -/
theorem density_affine (hbar c m t : ℝ) (ψ η : E → Spinor) (x : E) (v : Fin 4 → E)
    (hψ : DifferentiableAt ℝ ψ x) (hη : DifferentiableAt ℝ η x) :
    fieldDensityRe hbar c m (affine ψ η t) x v =
      fieldDensityRe hbar c m ψ x v + t * firstDensity hbar c m ψ η x v +
        t ^ 2 * fieldDensityRe hbar c m η x v := by
  change DiracDensity.densityRe hbar c m (ψ x + t • η x)
    (fun μ => fderiv ℝ (affine ψ η t) x (v μ)) = _
  simp only [fderiv_affine_apply ψ η x _ hψ hη t]
  exact densityRe_affine hbar c m t (ψ x) _ (η x) _

/-- Actual parameter derivative at any point of the affine line. -/
theorem hasDerivAt_density_affine (hbar c m t : ℝ) (ψ η : E → Spinor)
    (x : E) (v : Fin 4 → E) (hψ : DifferentiableAt ℝ ψ x) (hη : DifferentiableAt ℝ η x) :
    HasDerivAt (fun s => fieldDensityRe hbar c m (affine ψ η s) x v)
      (firstDensity hbar c m ψ η x v + 2 * t * fieldDensityRe hbar c m η x v) t := by
  simp_rw [density_affine _ _ _ _ _ _ _ _ hψ hη]
  simp only [pow_two]
  convert ((hasDerivAt_const t (fieldDensityRe hbar c m ψ x v)).add
      ((hasDerivAt_id t).mul_const (firstDensity hbar c m ψ η x v))).add
      (((hasDerivAt_id t).mul (hasDerivAt_id t)).mul_const (fieldDensityRe hbar c m η x v)) using 1
  · ext s
    simp only [Pi.add_apply, Pi.mul_apply, id_eq]
  · simp only [id_eq, mul_one, one_mul, zero_add]
    ring

/-- The first variation at the original field. -/
theorem hasDerivAt_density_zero (hbar c m : ℝ) (ψ η : E → Spinor)
    (x : E) (v : Fin 4 → E) (hψ : DifferentiableAt ℝ ψ x) (hη : DifferentiableAt ℝ η x) :
    HasDerivAt (fun t => fieldDensityRe hbar c m (affine ψ η t) x v)
      (firstDensity hbar c m ψ η x v) 0 := by
  simpa using hasDerivAt_density_affine hbar c m 0 ψ η x v hψ hη

end FoliationQM.DiracAffineFieldVariation
