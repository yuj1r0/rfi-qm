module
public import FoliationQM.TwistedScalarAction

/-!
# Exact action dependence on the chiral amplitude

For the scalar-limit clause of v13 `thm:dirac_lift`, scaling an actual
angle by k changes the massive action by a term of order k². A compact
change admits the same law for its relative action even when the separate
background actions do not have integrable densities.
-/

@[expose] public section
noncomputable section
open scoped Topology ContDiff
namespace FoliationQM.ScaledChiralAction
open DiracFieldDensity MeasureTheory Filter TwistedScalarAction TwistedScalarDensity

variable (p : MassiveParameters) {β : Covector → ℝ} {z w : Covector → ℂ} {U : Set Covector}

/-- The difference of the two angle corrections, with the background scalar first. -/
def correctionDiff (p : MassiveParameters) (β : Covector → ℝ) (z w : Covector → ℂ) (x : Covector) : ℝ :=
  potential p β x * (Complex.normSq (w x) - Complex.normSq (z x))

/-- The true massive density increment splits before integration. -/
theorem increment_eq {x : Covector} (hb : DifferentiableAt ℝ β x) (hz : DifferentiableAt ℝ z x)
    (hw : DifferentiableAt ℝ w x) :
    density p β w x - density p β z x =
      RelativeAction.relativeDensity p z w coordinateDirections x - correctionDiff p β z w x := by
  rw [density_eq_pairing p hb hw, density_eq_pairing p hb hz]
  unfold RelativeAction.relativeDensity correctionDiff
  ring

/-- Compact interior changes give integrable chiral correction differences. -/
theorem integrable_correctionDiff {K : Set Covector} (hK : IsCompact K) (hi : K ⊆ U)
    (hb : ∀ x ∈ U, ContDiffAt ℝ 1 β x) (hz : ContinuousOn z U) (hw : ContinuousOn w U)
    (he : ∀ x ∉ K, w x = z x) : IntegrableOn (correctionDiff p β z w) U := by
  apply DiracActionSupport.integrableOn_of_compact_support hK hi
  · intro x hx
    exact ((continuousAt_potential p (hb x hx)).continuousWithinAt).mul
      ((Complex.continuous_normSq.continuousAt.comp_continuousWithinAt (hw x hx)).sub
        (Complex.continuous_normSq.continuousAt.comp_continuousWithinAt (hz x hx)))
  · intro x hx
    simp [correctionDiff, he x hx]

/-- The integrated increment is the ordinary scalar increment less the signed correction difference. -/
theorem relative_eq (hU : MeasurableSet U) (hb : ∀ x ∈ U, DifferentiableAt ℝ β x)
    (hz : ∀ x ∈ U, DifferentiableAt ℝ z x) (hw : ∀ x ∈ U, DifferentiableAt ℝ w x)
    (hr : IntegrableOn (RelativeAction.relativeDensity p z w coordinateDirections) U)
    (hc : IntegrableOn (correctionDiff p β z w) U) :
    TwistedScalarAction.relativeAction p β z w U =
      RelativeAction.relativeAction p z w coordinateDirections U - ∫ x in U, correctionDiff p β z w x := by
  rw [RelativeAction.relativeAction, ← integral_sub hr hc]
  exact setIntegral_congr_fun hU fun x hx => increment_eq p (hb x hx) (hz x hx) (hw x hx)

/-- A finite scalar action and finite integrated chiral correction give an exact quadratic
law for every real scaling parameter. -/
theorem action_scale (k : ℝ) (hU : MeasurableSet U) (hb : ∀ x ∈ U, DifferentiableAt ℝ β x)
    (hz : ∀ x ∈ U, DifferentiableAt ℝ z x) (hs : IntegrableOn (scalarDensity p z) U)
    (hc : IntegrableOn (correction p β z) U) :
    action p (fun y => k * β y) z U = scalarAction p z U - k^2 * ∫ x in U, correction p β z x := by
  have he (x : Covector) (hx : x ∈ U) : correction p (fun y => k * β y) z x = k^2 * correction p β z x := by
    rw [correction, potential_scale p k (hb x hx), correction, mul_assoc]
  have hi := IntegrableOn.congr_fun (s := U) (hc.const_mul (k^2)) (fun x hx => (he x hx).symm) hU
  rw [action_eq p hU (fun x hx => (hb x hx).const_mul k) hz hs hi, setIntegral_congr_fun hU he, integral_const_mul]

/-- The relative action for a fixed pair obeys the same exact quadratic law. -/
theorem relative_scale (k : ℝ) (hU : MeasurableSet U) (hb : ∀ x ∈ U, DifferentiableAt ℝ β x)
    (hz : ∀ x ∈ U, DifferentiableAt ℝ z x) (hw : ∀ x ∈ U, DifferentiableAt ℝ w x)
    (hr : IntegrableOn (RelativeAction.relativeDensity p z w coordinateDirections) U)
    (hc : IntegrableOn (correctionDiff p β z w) U) :
    TwistedScalarAction.relativeAction p (fun y => k * β y) z w U =
      RelativeAction.relativeAction p z w coordinateDirections U - k^2 * ∫ x in U, correctionDiff p β z w x := by
  have he (x : Covector) (hx : x ∈ U) :
      correctionDiff p (fun y => k * β y) z w x = k^2 * correctionDiff p β z w x := by
    rw [correctionDiff, potential_scale p k (hb x hx), correctionDiff, mul_assoc]
  have hi := IntegrableOn.congr_fun (s := U) (hc.const_mul (k^2)) (fun x hx => (he x hx).symm) hU
  rw [relative_eq p hU (fun x hx => (hb x hx).const_mul k) hz hw hr hi,
    setIntegral_congr_fun hU he, integral_const_mul]

/-- Relative actions converge to the genuine scalar action increment as the common chiral
amplitude tends to zero, without separate integrability of either background action. -/
theorem tendsto_relative (hU : MeasurableSet U) (hb : ∀ x ∈ U, DifferentiableAt ℝ β x)
    (hz : ∀ x ∈ U, DifferentiableAt ℝ z x) (hw : ∀ x ∈ U, DifferentiableAt ℝ w x)
    (hr : IntegrableOn (RelativeAction.relativeDensity p z w coordinateDirections) U)
    (hc : IntegrableOn (correctionDiff p β z w) U) :
    Tendsto (fun k : ℝ => TwistedScalarAction.relativeAction p (fun y => k * β y) z w U) (𝓝 0)
      (𝓝 (RelativeAction.relativeAction p z w coordinateDirections U)) := by
  simp_rw [relative_scale p _ hU hb hz hw hr hc]
  simpa using (tendsto_const_nhds (x := RelativeAction.relativeAction p z w coordinateDirections U)).sub
    (((tendsto_id (x := 𝓝 (0 : ℝ))).pow 2).mul_const (∫ x in U, correctionDiff p β z w x))

end FoliationQM.ScaledChiralAction
