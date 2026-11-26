module
public import FoliationQM.DiracCurrent
public import FoliationQM.DiracRelativeAction

/-!
# Value of the symmetric Dirac action on a solution

For v13 `eq:dirac_lagrangian_sym` and `thm:dirac_lift`, contracting the
Dirac equation and its derived adjoint identifies both halves of the kinetic
density with half the mass term. The action of a solution is consequently
well defined even on an unbounded open domain.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.DiracOnShellDensity
open DiracMatrices DiracDensity DiracEquation DiracCurrent MeasureTheory
open DiracActionSupport DiracRelativeAction

variable (hbar c m : ℝ)

/-- A jet satisfying the Dirac equation has zero symmetric complex density. -/
theorem density_eq_zero_of_jetEquation (ψ : Spinor) (jet : Fin 4 → Spinor)
    (h : jetEquation hbar m c ψ jet) : density hbar c m ψ jet = 0 := by
  have hr := jetEquation_right_bilinear hbar m c ψ jet h
  have hl := jetEquation_left_bilinear hbar m c ψ jet h
  rw [Complex.ofReal_mul] at hr hl
  simp only [density, directionalPair, Finset.sum_sub_distrib]
  linear_combination (c : ℂ) / 2 * hr + (c : ℂ) / 2 * hl

variable {U : Set Covector} {ψ : Covector → Spinor}

/-- The actual real density vanishes at each point satisfying the field equation. -/
theorem dens_eq_zero {x : Covector} (he : diracField hbar m c ψ x = 0) :
    dens hbar c m ψ x = 0 := by
  change (density hbar c m (ψ x) _).re = 0
  rw [density_eq_zero_of_jetEquation hbar c m _ _ ((diracField_eq_zero_iff ..).mp he)]
  rfl

/-- The ordinary action density is integrable on any measurable domain of a solution. -/
theorem integrableOn_dens (hU : MeasurableSet U) (he : ∀ x ∈ U, diracField hbar m c ψ x = 0) :
    IntegrableOn (dens hbar c m ψ) U :=
  integrableOn_zero.congr_fun (fun x hx => (dens_eq_zero hbar c m (he x hx)).symm) hU

/-- The ordinary action itself vanishes on every domain of a solution. -/
theorem action_eq_zero (he : ∀ x ∈ U, diracField hbar m c ψ x = 0) :
    action hbar c m ψ U = 0 :=
  setIntegral_eq_zero_of_forall_eq_zero (fun x hx => dens_eq_zero hbar c m (he x hx))

end FoliationQM.DiracOnShellDensity
