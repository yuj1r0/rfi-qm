module
public import FoliationQM.DiracCurveAction
public import FoliationQM.DiracFluxSupport
public import FoliationQM.DiracResidualField

/-!
# The integrated first variation as the tested flat Dirac operator

For v13 `thm:dirac_lift`, integration by parts eliminates the divergence
of the compact interior variation flux. The coefficient of the genuine
residual is twice the speed parameter. No boundary regularity or global
integrability of the background is used for the relative-action formula.
-/

@[expose] public section
noncomputable section
open scoped ContDiff
namespace FoliationQM.DiracActionIntegrationByParts
open MeasureTheory DiracMatrices DiracActionSupport DiracFieldDensity DiracVariationFlux
open DiracResidualField DiracInteriorVariation DiracCurveJetCalculus DiracRelativeAction
open DiracAffineFieldVariation (affine)

variable (hbar c m : ℝ) {U : Set Covector} {ψ η : Covector → Spinor}

/-- A compact interior variation integrates to precisely the tested Dirac residual.
All terms in the integration by parts are integrable for the stated local C¹ fields. -/
theorem integral_first (hU : IsOpen U) (hψ : ∀ x ∈ U, ContDiffAt ℝ 1 ψ x)
    (hη : ContDiff ℝ 1 η) (hc : HasCompactSupport η) (hs : tsupport η ⊆ U) :
    (∫ x in U, first hbar c m ψ η x) = (2*c) * ∫ x in U, tested hbar m c ψ η x := by
  let F (μ : Fin 4) (x : Covector) :=
    fderiv ℝ (flux hbar c ψ η μ) x (coordinateDirections μ)
  have hηU : ∀ x ∈ U, ContDiffAt ℝ 1 η x := fun x _ => hη.contDiffAt
  have hi (μ : Fin 4) : IntegrableOn (F μ) U :=
    (DiracFluxSupport.integrable_flux_deriv hbar c hψ hηU hc hs μ).integrableOn
  have hz (μ : Fin 4) : ∫ x in U, F μ x = 0 :=
    DiracFluxSupport.integral_flux_deriv_zero hbar c hψ hηU hc hs μ
  have hdiv : (∫ x in U, ∑ μ, F μ x) = 0 := by
    rw [integral_finsetSum _ (fun μ _ => hi μ)]
    exact Finset.sum_eq_zero (fun μ _ => hz μ)
  have hp := integrableOn_tested hbar m c hψ hη.continuous.continuousOn hc hs
  calc
    _ = ∫ x in U, (2*c) * tested hbar m c ψ η x + ∑ μ, F μ x := by
      apply setIntegral_congr_fun hU.measurableSet
      intro x hx
      exact first_eq_residual_add_div hbar c m ψ η x
        ((hψ x hx).differentiableAt (by norm_num)) (hη.differentiable (by norm_num) x)
    _ = _ := by rw [integral_add (hp.const_mul _) (integrable_finsetSum _ (fun μ _ => hi μ)),
                    integral_const_mul, hdiv, add_zero]

/-- Affine relative-action derivative for every compact interior C¹ test. -/
theorem hasDerivAt_relative_affine (hU : IsOpen U) (hψ : ∀ x ∈ U, ContDiffAt ℝ 1 ψ x)
    (hη : ContDiff ℝ 1 η) (hc : HasCompactSupport η) (hs : tsupport η ⊆ U) :
    HasDerivAt (fun t => relativeAction hbar c m ψ (affine ψ η t) U)
      ((2*c) * ∫ x in U, tested hbar m c ψ η x) 0 := by
  rw [← integral_first hbar c m hU hψ hη hc hs]
  exact DiracRelativeAction.hasDerivAt_relative_affine hbar c m hU hψ hη hc hs

/-- The same identity for the actual velocity of any smooth compact interior family. -/
theorem integral_velocity (V : Variation U ψ) (hU : IsOpen U) :
    (∫ x in U, first hbar c m ψ (velocity V.family 0) x) =
      (2*c) * ∫ x in U, tested hbar m c ψ (velocity V.family 0) x := by
  have hψ : ∀ x ∈ U, ContDiffAt ℝ 1 ψ x := by
    intro x hx
    rw [← slice_zero V]
    exact (contDiffAt_slice (V.smooth 0 V.zero_mem x hx)).of_le (by simp)
  exact integral_first hbar c m hU hψ ((velocity_contDiff V V.zero_mem).of_le (by simp))
    (velocity_compact V V.zero_mem) ((velocity_tsupport V V.zero_mem).trans V.interior)

/-- Relative action for any admissible smooth family gives the residual tested by its initial velocity. -/
theorem hasDerivAt_relative (V : Variation U ψ) (hU : IsOpen U) :
    HasDerivAt (fun t => relativeAction hbar c m ψ (slice V.family t) U)
      ((2*c) * ∫ x in U, tested hbar m c ψ (velocity V.family 0) x) 0 := by
  rw [← integral_velocity hbar c m V hU]
  exact DiracCurveAction.hasDerivAt_relative hbar c m V hU

/-- Ordinary action has the same tested-residual derivative when the background density is integrable. -/
theorem hasDerivAt_action (V : Variation U ψ) (hU : IsOpen U) (hbase : IntegrableOn (dens hbar c m ψ) U) :
    HasDerivAt (fun t => action hbar c m (slice V.family t) U)
      ((2*c) * ∫ x in U, tested hbar m c ψ (velocity V.family 0) x) 0 := by
  rw [← integral_velocity hbar c m V hU]
  exact DiracCurveAction.hasDerivAt_action hbar c m V hU hbase

end FoliationQM.DiracActionIntegrationByParts
