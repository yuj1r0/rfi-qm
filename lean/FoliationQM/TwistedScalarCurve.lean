module
public import FoliationQM.TwistedScalarCurveData
public import FoliationQM.TwistedScalarVariation

/-!
# The twisted scalar residual along general smooth variations

For v13 `thm:dirac_lift`, integration by parts in the scalar term and
differentiation of the chiral correction give the tested forced
Klein–Gordon equation for any jointly smooth compact interior family.
-/

@[expose] public section
noncomputable section
open scoped Topology ContDiff ComplexConjugate
namespace FoliationQM.TwistedScalarCurve
open MeasureTheory DiracFieldDensity SmoothActionDensity FlatIntegrationByParts TwistedScalarAction
open TwistedScalarDensity TwistedScalarVariation

variable {U : Set Covector} {β : Covector → ℝ} {z : Covector → ℂ}

/-- The relative-action derivative along each compact interior smooth family is minus
twice the real pairing of its true velocity with the forced Klein–Gordon residual. -/
theorem hasDerivAt_curve (p : MassiveParameters) (V : Variation U z) (hU : IsOpen U)
    (hb : ∀ x ∈ U, ContDiffAt ℝ 1 β x) :
    HasDerivAt (fun t => relativeAction p β z (slice V.family t) U)
      (-2 * ∫ x in U, (conj (velocity V.family 0 x) * force p β z x).re) 0 := by
  let η := velocity V.family 0
  have hs : ∀ x ∈ U, ContDiffAt ℝ 2 z x := fun _ hx => (base_smooth V hx).of_le (by simp)
  have hi := (OpenIntegrationByParts.integrable_test_kgOperator p
    ((velocity_smooth V V.zero_mem).of_le (by simp)) hs (velocity_compact V V.zero_mem)
    ((velocity_tsupport V V.zero_mem).trans V.interior) coordinateDirections).re
  simp only [RCLike.re_eq_complex_re] at hi
  have hi' : IntegrableOn (fun x => (conj (η x) * ((potential p β x : ℂ)*z x)).re) U := by
    have hiP := integrableOn_testPotential p hb (fun _ hx => (base_smooth V hx).continuousAt.continuousWithinAt)
      (velocity_smooth V V.zero_mem).continuous (velocity_compact V V.zero_mem) ((velocity_tsupport V V.zero_mem).trans V.interior)
    apply hiP.congr_fun _ hU.measurableSet
    intro x _
    simp only [η, testPotential, mul_left_comm (conj _), Complex.re_ofReal_mul]
  have he : (fun t => relativeAction p β z (slice V.family t) U) =ᶠ[𝓝 0]
      (fun t => RelativeAction.relativeAction p z (slice V.family t) coordinateDirections U -
        ∫ x in U, ScaledChiralAction.correctionDiff p β z (slice V.family t) x) :=
    Filter.mem_of_superset (V.params_open.mem_nhds V.zero_mem) (fun _ ht => relative_eq_curve p V hU hb ht)
  have hkg := RelativeActionVariation.hasDerivAt_relativeAction_curve_eq_kg p hU V.params_open V.zero_mem V.smooth
    V.compact V.interior (fixed_initial V) coordinateDirections
  rw [slice_zero V] at hkg
  have hd := (hkg.sub (hasDerivAt_correction_curve p V hU hb)).congr_of_eventuallyEq he
  simp only [force, mul_add, Complex.add_re]
  rw [integral_add hi hi']
  convert hd using 1
  ring

/-- A finite twisted background gives integrable twisted densities at every admissible parameter. -/
theorem integrableOn_slice (p : MassiveParameters) (V : Variation U z) (hU : IsOpen U)
    (hb : ∀ x ∈ U, ContDiffAt ℝ 1 β x) (hz : IntegrableOn (density p β z) U) {t : ℝ} (ht : t ∈ V.params) :
    IntegrableOn (density p β (slice V.family t)) U := by
  have h := (TwistedScalarCurve.integrableOn_increment p V hU hb ht).add hz
  change IntegrableOn (fun x => density p β (slice V.family t) x - density p β z x + density p β z x) U at h
  simpa only [sub_add_cancel] using h

/-- On an integrable twisted background, the ordinary action has the same derivative
along the arbitrary compact variation. No separate finiteness of the untwisted action is required. -/
theorem hasDerivAt_action (p : MassiveParameters) (V : Variation U z) (hU : IsOpen U)
    (hb : ∀ x ∈ U, ContDiffAt ℝ 1 β x) (hz : IntegrableOn (density p β z) U) :
    HasDerivAt (fun t => action p β (slice V.family t) U)
      (-2 * ∫ x in U, (conj (velocity V.family 0 x) * force p β z x).re) 0 := by
  have he : (fun t => action p β (slice V.family t) U) =ᶠ[𝓝 0]
      (fun t => relativeAction p β z (slice V.family t) U + action p β z U) := by
    filter_upwards [V.params_open.mem_nhds V.zero_mem] with t ht
    rw [relative_eq_sub p hz (integrableOn_slice p V hU hb hz ht), sub_add_cancel]
  exact ((hasDerivAt_curve p V hU hb).add_const _).congr_of_eventuallyEq he

end FoliationQM.TwistedScalarCurve
