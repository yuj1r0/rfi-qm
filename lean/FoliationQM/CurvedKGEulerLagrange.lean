module

public import FoliationQM.CurvedKGRelativeVariation

/-!
# Euler–Lagrange equivalence for the curved Klein–Gordon action

Independent real directions in the complex scalar field test both real
components. The derivative of the actual action pairs the test with the
wave residual. Compact interior tests determine this residual at every
point of the open Lorentz patch. The relative action also covers fields
whose absolute action is infinite.
-/

@[expose] public section
noncomputable section
open scoped Matrix.Norms.Operator ContDiff
namespace FoliationQM.CurvedKGEulerLagrange

open MeasureTheory LorentzMatrixGroup RNCVolumeDensity CurvedPolarAction CurvedWeakEquation
open CurvedKGFirstVariation CurvedKGTestResidual CurvedKGRelativeVariation

/-- Stationarity under every smooth complex compact interior perturbation of the relative action. -/
def RelativeStationary (p : MassiveParameters) (g : Covector → Mat4) (ψ : Covector → ℂ) (U : Set Covector) : Prop :=
  ∀ η : Covector → ℂ, ContDiff ℝ ∞ η → HasCompactSupport η → tsupport η ⊆ U →
    HasDerivAt (relativeAction p g ψ η U) 0 0

/-- Stationarity of the absolute action also requires finiteness of the background integral. -/
def Stationary (p : MassiveParameters) (g : Covector → Mat4) (ψ : Covector → ℂ) (U : Set Covector) : Prop :=
  IntegrableOn (fun x => volumeFactor (g x) * kgDensity p g ψ x) U ∧
  ∀ η : Covector → ℂ, ContDiff ℝ ∞ η → HasCompactSupport η → tsupport η ⊆ U →
    HasDerivAt (fun t => kgAction p g (perturb ψ η t) U) 0 0

variable {g : Covector → Mat4} {U : Set Covector} {ψ : Covector → ℂ}

/-- Vanishing of the weighted compact tests of the unnormalized residual is equivalent to the pointwise normalized curved KG equation. -/
theorem operator_iff_tests (p : MassiveParameters) (hU : IsOpen U)
    (hg : ∀ x ∈ U, ContDiffAt ℝ 2 g x) (hd : ∀ x ∈ U, (g x).det < 0)
    (hψ : ∀ x ∈ U, ContDiffAt ℝ 2 ψ x) :
    (∀ x ∈ U, kgOperator p g ψ x = 0) ↔
    ∀ η : Covector → ℂ, ContDiff ℝ ∞ η → HasCompactSupport η → tsupport η ⊆ U →
      testIntegral U g η (residual p g ψ) = 0 := by
  exact (forall₂_congr fun x _ => (residual_zero_iff p g ψ x).symm).trans <| zero_iff_tests hU
    (fun x hx => (hg x hx).continuousAt.continuousWithinAt) hd
    (fun x hx => (residual_continuousAt p (hg x hx) (hd x hx) (hψ x hx)).continuousWithinAt)

/-- The derivative of the actual relative action is minus twice the real test integral of the curved field residual. -/
theorem relative_derivative (p : MassiveParameters) (hU : IsOpen U)
    (hg : ∀ x ∈ U, ContDiffAt ℝ 2 g x) (hsym : ∀ x ∈ U, (g x).IsSymm)
    (hd : ∀ x ∈ U, (g x).det < 0) (hψ : ∀ x ∈ U, ContDiffAt ℝ 2 ψ x)
    {η : Covector → ℂ} (hη : ContDiff ℝ 2 η) (hc : HasCompactSupport η) (hs : tsupport η ⊆ U) :
    HasDerivAt (relativeAction p g ψ η U) (-(2 * testIntegral U g η (residual p g ψ))) 0 := by
  have he := hasDerivAt_relative p hU hg hsym hd hψ hη hc hs
  rw [integral_cross_re p (hη.of_le (by decide)) hc hs hg hd hψ, mul_neg] at he
  exact he

/-- The curved action is relatively stationary exactly at the pointwise solutions of the curved Klein–Gordon equation. -/
theorem relative_stationary_iff (p : MassiveParameters) (hU : IsOpen U)
    (hg : ∀ x ∈ U, ContDiffAt ℝ 2 g x) (hsym : ∀ x ∈ U, (g x).IsSymm)
    (hd : ∀ x ∈ U, (g x).det < 0) (hψ : ∀ x ∈ U, ContDiffAt ℝ 2 ψ x) :
    RelativeStationary p g ψ U ↔ ∀ x ∈ U, kgOperator p g ψ x = 0 := by
  rw [operator_iff_tests p hU hg hd hψ]
  constructor
  · intro hv η hη hc hs
    have he := (relative_derivative p hU hg hsym hd hψ (hη.of_le (by simp)) hc hs).unique (hv η hη hc hs)
    linarith
  · intro ht η hη hc hs
    simpa only [ht η hη hc hs, mul_zero, neg_zero] using
      relative_derivative p hU hg hsym hd hψ (hη.of_le (by simp)) hc hs

/-- For finite backgrounds the stationary points of the absolute action are exactly the pointwise curved Klein–Gordon solutions. -/
theorem stationary_iff (p : MassiveParameters) (hU : IsOpen U)
    (hg : ∀ x ∈ U, ContDiffAt ℝ 2 g x) (hsym : ∀ x ∈ U, (g x).IsSymm)
    (hd : ∀ x ∈ U, (g x).det < 0) (hψ : ∀ x ∈ U, ContDiffAt ℝ 2 ψ x) :
    Stationary p g ψ U ↔ IntegrableOn (fun x => volumeFactor (g x) * kgDensity p g ψ x) U ∧
      ∀ x ∈ U, kgOperator p g ψ x = 0 := by
  unfold Stationary
  apply and_congr_right
  intro hfin
  rw [operator_iff_tests p hU hg hd hψ]
  constructor
  · intro hv η hη hc hs
    have he := (hasDerivAt_absolute p hU hg hsym hd hψ (hη.of_le (by simp)) hc hs hfin).unique (hv η hη hc hs)
    rw [integral_cross_re p (hη.of_le (by simp)) hc hs hg hd hψ] at he
    linarith
  · intro ht η hη hc hs
    have he := hasDerivAt_absolute p hU hg hsym hd hψ (hη.of_le (by simp)) hc hs hfin
    simpa only [integral_cross_re p (hη.of_le (by simp)) hc hs hg hd hψ, ht η hη hc hs,
      neg_zero, mul_zero] using he

end FoliationQM.CurvedKGEulerLagrange
