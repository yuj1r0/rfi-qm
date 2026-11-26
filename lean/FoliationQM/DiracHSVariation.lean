module
public import FoliationQM.DiracHSAction
public import FoliationQM.DiracPolarTestRealization

/-!
# First variation of the integrated Hestenes–Takabayasi action

For v13 `thm:dirac_lift` and `eq:dirac_polar_lagrangian_main`, both
directions of variation transport identify the action curves near zero.
Their derivatives use the actual parameter derivative of the decoded
quotient field, paired with the flat Dirac residual.
-/

@[expose] public section
noncomputable section
open scoped Topology ContDiff Manifold
namespace FoliationQM.DiracHSVariation
open MeasureTheory DiracMatrices DiracPolarCoordinates DiracPolarVariation
open DiracPolarVariationTransport DiracInteriorVariation DiracRegularVariations
open DiracResidualField DiracEquation

variable {U : Set Covector} {q : Covector → Q} {ψ : Covector → Spinor}

/-- An admissible spinor slice is locally C¹ on the integration domain. -/
theorem slice_c1 (V : Variation U ψ) {t : ℝ} (ht : t ∈ V.params) :
    ∀ x ∈ U, ContDiffAt ℝ 1 (DiracCurveJetCalculus.slice V.family t) x :=
  fun x hx => (DiracCurveJetCalculus.contDiffAt_slice (V.smooth t ht x hx)).of_le (by simp)

/-- The same local regularity holds for the background, by taking the zero slice. -/
theorem base_c1 (V : Variation U ψ) : ∀ x ∈ U, ContDiffAt ℝ 1 ψ x := by
  rw [← slice_zero V]
  exact slice_c1 V V.zero_mem

variable (hbar c m : ℝ) (hU : IsOpen U) (h : Represents U q ψ)

/-- The relative polar action curve agrees near zero with the spinor curve it realizes. -/
theorem relative_toSpinor (P : PolarVariation U q) :
    (fun t => DiracHSAction.relativeAction hbar c m q (slice P t) U) =ᶠ[𝓝 0]
      (fun t => DiracRelativeAction.relativeAction hbar c m ψ
        (DiracCurveJetCalculus.slice (toSpinor hU h P).family t) U) := by
  filter_upwards [P.params_open.mem_nhds P.zero_mem] with t ht
  exact DiracHSAction.relative_slice_eq hbar c m hU h P ht

/-- Along an arbitrary spinor variation, its polar lift has the original relative action germ. -/
theorem relative_lift (V : Variation U ψ) :
    (fun t => DiracHSAction.relativeAction hbar c m q (slice (DiracPolarTestRealization.lift hU h V) t) U)
      =ᶠ[𝓝 0] (fun t => DiracRelativeAction.relativeAction hbar c m ψ (DiracCurveJetCalculus.slice V.family t) U) := by
  filter_upwards [DiracPolarTestRealization.lift_germ hU h V, V.params_open.mem_nhds V.zero_mem] with t hr ht
  exact DiracHSAction.relative_eq hbar c m hU h hr (base_c1 V) (slice_c1 V ht)

/-- The ordinary polar action has the same germ as the ordinary realized action. -/
theorem action_toSpinor (P : PolarVariation U q) :
    (fun t => DiracHSAction.action hbar c m (slice P t) U) =ᶠ[𝓝 0]
      (fun t => DiracRelativeAction.action hbar c m (DiracCurveJetCalculus.slice (toSpinor hU h P).family t) U) := by
  filter_upwards [P.params_open.mem_nhds P.zero_mem] with t ht
  exact DiracHSAction.action_eq hbar c m hU (toSpinor_represents hU h P t) (slice_c1 (toSpinor hU h P).toVariation ht)

/-- The ordinary action of the polar lift agrees near zero with the original spinor action. -/
theorem action_lift (V : Variation U ψ) :
    (fun t => DiracHSAction.action hbar c m (slice (DiracPolarTestRealization.lift hU h V) t) U) =ᶠ[𝓝 0]
      (fun t => DiracRelativeAction.action hbar c m (DiracCurveJetCalculus.slice V.family t) U) := by
  filter_upwards [DiracPolarTestRealization.lift_germ hU h V, V.params_open.mem_nhds V.zero_mem] with t hr ht
  exact DiracHSAction.action_eq hbar c m hU hr (slice_c1 V ht)

/-- The velocity measured by differentiating the realized physical polar family. -/
def polarVelocity (P : PolarVariation U q) (x : Covector) : Spinor :=
  deriv (fun t => decode (P.family (t,x))) 0

/-- On U the physical parameter derivative is precisely the velocity of the lifted spinor family. -/
theorem polarVelocity_eq (P : PolarVariation U q) {x : Covector} (hx : x ∈ U) :
    polarVelocity P x = DiracCurveJetCalculus.velocity (toSpinor hU h P).family 0 x := by
  let W := toSpinor hU h P
  have hd := DiracCurveJetCalculus.hasDerivAt_slice_time
    ((W.smooth 0 W.zero_mem x hx).differentiableAt (by simp))
  have he : (fun t => decode (P.family (t,x))) =ᶠ[𝓝 0]
      (fun t => DiracCurveJetCalculus.slice W.family t x) :=
    Filter.Eventually.of_forall (fun t => (toSpinor_apply hU h P t hx).symm)
  exact (hd.congr_of_eventuallyEq he).deriv

/-- Testing the residual uses only velocities inside the domain of comparison. -/
theorem integral_polarVelocity (P : PolarVariation U q) :
    (∫ x in U, tested hbar m c ψ (polarVelocity P) x) =
      ∫ x in U, tested hbar m c ψ (DiracCurveJetCalculus.velocity (toSpinor hU h P).family 0) x := by
  apply setIntegral_congr_fun hU.measurableSet
  intro x hx
  exact congrArg (fun u => DiracResidualPairing.pair u (diracField hbar m c ψ x)) (polarVelocity_eq hU h P hx)

include hU h

/-- Relative polar-action variation is the actual Dirac residual paired with the polar velocity. -/
theorem hasDerivAt_relative (P : PolarVariation U q) :
    HasDerivAt (fun t => DiracHSAction.relativeAction hbar c m q (slice P t) U)
      ((2*c) * ∫ x in U, tested hbar m c ψ (polarVelocity P) x) 0 := by
  rw [integral_polarVelocity hbar c m hU h P]
  exact (DiracActionIntegrationByParts.hasDerivAt_relative hbar c m (toSpinor hU h P).toVariation hU)
    |>.congr_of_eventuallyEq (relative_toSpinor hbar c m hU h P)

/-- On an integrable background the ordinary polar action has the same derivative. -/
theorem hasDerivAt_action (P : PolarVariation U q) (hb : IntegrableOn (DiracHSDensity.density hbar c m q) U) :
    HasDerivAt (fun t => DiracHSAction.action hbar c m (slice P t) U)
      ((2*c) * ∫ x in U, tested hbar m c ψ (polarVelocity P) x) 0 := by
  have hfin := (DiracHSAction.integrable_iff hbar c m hU h (base_c1 (toSpinor hU h P).toVariation)).mp hb
  rw [integral_polarVelocity hbar c m hU h P]
  exact (DiracActionIntegrationByParts.hasDerivAt_action hbar c m (toSpinor hU h P).toVariation hU hfin)
    |>.congr_of_eventuallyEq (action_toSpinor hbar c m hU h P)

end FoliationQM.DiracHSVariation
