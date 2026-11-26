module

public import FoliationQM.CurvedClockNormalization
public import FoliationQM.CurvedNormalizedOperator
public import FoliationQM.CurvedKGEulerLagrange

/-!
# The normalized covariant master action on a clock chart

The complex operator expression carries a boundary divergence before
integration by parts. Expressing the action scale using ℓC and the clock
phase gives exactly the two sides of the v13 master equation on each
positive-density coordinate region with the specified boundary conditions.
-/

@[expose] public section
noncomputable section
open scoped Matrix.Norms.Operator
namespace FoliationQM.CurvedMasterEquivalence

open MeasureTheory LorentzMatrixGroup RNCVolumeDensity CurvedPolarAction CurvedClockNormalization
open CurvedNormalizedOperator CurvedGreenBoundary

/-- Integral of the master wave operator paired with the conjugate field. -/
def operatorAction (p : MassiveParameters) (g : Covector → Mat4) (ψ : Covector → ℂ)
    (U : Set Covector) : ℂ :=
  ∫ x in U, volumeFactor (g x) • (star (ψ x) * masterOp p g ψ x)

/-- The complex integral of the normalized first-order action is the normalized real KG action viewed in ℂ. -/
theorem normalized_integral (p : MassiveParameters) (g : Covector → Mat4) (ψ : Covector → ℂ) (U : Set Covector) :
    (∫ x in U, (volumeFactor (g x) / (p.m ^ 2 * p.c ^ 2)) • (kgDensity p g ψ x : ℂ)) =
      ((kgAction p g ψ U / (p.m ^ 2 * p.c ^ 2) : ℝ) : ℂ) := by
  calc
    _ = ∫ x in U, ((volumeFactor (g x) * kgDensity p g ψ x / (p.m ^ 2 * p.c ^ 2) : ℝ) : ℂ) := by
      apply integral_congr_ae
      filter_upwards with x
      simp only [Complex.real_smul, Complex.ofReal_div, Complex.ofReal_mul]
      ring
    _ = _ := by rw [integral_complex_ofReal, integral_div]; rfl

/-- The operator action, including its actual boundary correction, is the normalized clock action on a positive C² chart. -/
theorem clock_operator_action (p : MassiveParameters) {g : Covector → Mat4} {ρ τ : Covector → ℝ}
    {U : Set Covector} (hU : MeasurableSet U) (hg : ∀ x ∈ U, DifferentiableAt ℝ g x)
    (hd : ∀ x ∈ U, (g x).det < 0) (hs : ∀ x ∈ U, (g x).IsSymm)
    (hρ : ∀ x ∈ U, ContDiffAt ℝ 2 ρ x) (hτ : ∀ x ∈ U, ContDiffAt ℝ 2 τ x)
    (hp : ∀ x ∈ U, 0 < ρ x)
    (hA : IntegrableOn (fun x => (volumeFactor (g x) / (p.m ^ 2 * p.c ^ 2)) •
      (kgDensity p g (ActionDensity.actionField p ρ (clockPhase p τ)) x : ℂ)) U)
    (hB : IntegrableOn (boundaryDivergence g (ActionDensity.actionField p ρ (clockPhase p τ))
      (ActionDensity.actionField p ρ (clockPhase p τ))) U) :
    operatorAction p g (ActionDensity.actionField p ρ (clockPhase p τ)) U +
      p.ellC ^ 2 • ∫ x in U, boundaryDivergence g (ActionDensity.actionField p ρ (clockPhase p τ))
        (ActionDensity.actionField p ρ (clockPhase p τ)) x =
      (normalizedClockAction p g ρ τ U : ℂ) := by
  have hψ (x) (hx : x ∈ U) : ContDiffAt ℝ 2 (ActionDensity.actionField p ρ (clockPhase p τ)) x :=
    PolarRegularity.contDiffAt_actionField p (hρ x hx) (contDiffAt_const.mul (hτ x hx)) (hp x hx)
  rw [operatorAction, integral_boundary p hU hg hd hs hψ hA hB, sub_add_cancel, normalized_integral,
    kg_action_normalized p g hU (fun x hx => (hρ x hx).differentiableAt (by decide))
      (fun x hx => (hτ x hx).differentiableAt (by decide)) hp]

/-- When the integrated boundary divergence vanishes, the complex operator action is exactly the normalized finite first-order action. -/
theorem operator_eq_normalized (p : MassiveParameters) {g : Covector → Mat4} {ψ : Covector → ℂ}
    {U : Set Covector} (hU : MeasurableSet U) (hg : ∀ x ∈ U, DifferentiableAt ℝ g x)
    (hd : ∀ x ∈ U, (g x).det < 0) (hs : ∀ x ∈ U, (g x).IsSymm)
    (hψ : ∀ x ∈ U, ContDiffAt ℝ 2 ψ x)
    (hA : IntegrableOn (fun x => (volumeFactor (g x) / (p.m ^ 2 * p.c ^ 2)) • (kgDensity p g ψ x : ℂ)) U)
    (hB : IntegrableOn (boundaryDivergence g ψ ψ) U) (hz : ∫ x in U, boundaryDivergence g ψ ψ x = 0) :
    operatorAction p g ψ U = ((kgAction p g ψ U / (p.m ^ 2 * p.c ^ 2) : ℝ) : ℂ) := by
  rw [operatorAction, integral_boundary p hU hg hd hs hψ hA hB, hz, smul_zero, sub_zero, normalized_integral]

end FoliationQM.CurvedMasterEquivalence
