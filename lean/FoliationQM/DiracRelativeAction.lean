module
public import FoliationQM.DiracActionSupport

/-!
# The relative Dirac action on an open flat domain

For v13 `thm:dirac_lift`, a compact interior change has a finite integrated
action increment even if the background density is not integrable on the
whole domain. For affine changes its exact quadratic expansion integrates
term by term. If the ordinary action is finite the two actions have the
same first variation.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.DiracRelativeAction
open MeasureTheory DiracMatrices DiracActionSupport DiracAffineFieldVariation
open DiracFieldDensity

variable (hbar c m : ℝ)

/-- Ordinary action of the stipulated symmetric real density, with Lebesgue measure. -/
def action (ψ : Covector → Spinor) (U : Set Covector) : ℝ :=
  ∫ x in U, dens hbar c m ψ x

/-- The actual change in the density is integrated before taking any separate action integrals. -/
def relativeAction (ψ φ : Covector → Spinor) (U : Set Covector) : ℝ :=
  ∫ x in U, dens hbar c m φ x - dens hbar c m ψ x

/-- For two integrable densities the relative action is their ordinary action difference. -/
theorem relative_eq_action_sub {ψ φ : Covector → Spinor} {U : Set Covector}
    (hψ : IntegrableOn (dens hbar c m ψ) U) (hφ : IntegrableOn (dens hbar c m φ) U) :
    relativeAction hbar c m ψ φ U = action hbar c m φ U - action hbar c m ψ U :=
  integral_sub hφ hψ

/-- The initial relative action vanishes regardless of the behavior of the background at infinity. -/
theorem relative_self (ψ : Covector → Spinor) (U : Set Covector) :
    relativeAction hbar c m ψ ψ U = 0 := by simp [relativeAction]

variable {ψ η : Covector → Spinor} {U : Set Covector}
  (hU : IsOpen U) (hψ : ∀ x ∈ U, ContDiffAt ℝ 1 ψ x)
  (hη : ContDiff ℝ 1 η) (hc : HasCompactSupport η) (hs : tsupport η ⊆ U)

include hU hψ hη hc hs in
/-- Exact integrated expansion for a compact interior affine variation. -/
theorem relative_affine (t : ℝ) :
    relativeAction hbar c m ψ (affine ψ η t) U =
      t * (∫ x in U, first hbar c m ψ η x) + t ^ 2 * action hbar c m η U := by
  have H (x : Covector) (hx : x ∈ U) :
      dens hbar c m (affine ψ η t) x - dens hbar c m ψ x =
        t * first hbar c m ψ η x + t ^ 2 * dens hbar c m η x := by
    change fieldDensityRe _ _ _ _ x _ - _ = _
    rw [density_affine hbar c m t ψ η x coordinateDirections
      ((hψ x hx).differentiableAt (by norm_num)) (hη.differentiable (by norm_num) x)]
    change dens hbar c m ψ x + t * first hbar c m ψ η x + t ^ 2 * dens hbar c m η x - dens hbar c m ψ x = _
    ring
  unfold relativeAction action
  rw [setIntegral_congr_fun hU.measurableSet H,
    integral_add ((integrableOn_first hbar c m hψ (fun x _ => hη.contDiffAt (x := x)) hc hs).const_mul t)
      ((integrableOn_testDensity hbar c m (fun x _ => hη.contDiffAt (x := x)) hc hs).const_mul (t^2)),
    integral_const_mul, integral_const_mul]

include hU hψ hη hc hs in
/-- The derivative of the integrated relative action is the integral of the actual first variation. -/
theorem hasDerivAt_relative_affine :
    HasDerivAt (fun t => relativeAction hbar c m ψ (affine ψ η t) U)
      (∫ x in U, first hbar c m ψ η x) 0 := by
  simp_rw [relative_affine hbar c m hU hψ hη hc hs]
  convert ((hasDerivAt_id (0 : ℝ)).mul_const (∫ x in U, first hbar c m ψ η x)).add
    (((hasDerivAt_id (0 : ℝ)).mul (hasDerivAt_id 0)).mul_const (action hbar c m η U)) using 1
  · ext t
    simp [pow_two, Pi.mul_apply]
  · simp

end FoliationQM.DiracRelativeAction
