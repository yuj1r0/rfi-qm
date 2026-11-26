module
public import FoliationQM.DiracHSStationarity
public import FoliationQM.DiracStationaryExamples

/-!
# Regular polar-action examples

For v13 `thm:dirac_lift`, the physical rest wave gives a globally smooth
polar field of invariant density one and zero ordinary action. On the
positive-time half-space the time-linear example has stationary polar
action at zero speed and a nonvanishing Dirac residual everywhere.
-/

@[expose] public section
noncomputable section
open scoped Topology ContDiff Manifold
namespace FoliationQM.DiracHSExamples
open DiracMatrices DiracPolarCoordinates DiracPolarVariationTransport DiracHSStationarity
open DiracStationaryExamples DiracEquation

/-- The physical quotient field of the massive rest-plane spinor. -/
def restPolar (hbar c m : ℝ) (x : Covector) : Q := encode (DiracRestField.field hbar c m x)

/-- The rest-plane polar field represents the regular solution on any domain. -/
theorem rest_represents (hbar c m : ℝ) (U : Set Covector) :
    Represents U (restPolar hbar c m) (DiracRestField.field hbar c m) :=
  encode_represents (fun x _ => DiracRestField.regular hbar c m x)

/-- The realized rest spinor has unit invariant density everywhere. -/
theorem rest_density_one (hbar c m : ℝ) (x : Covector) :
    SpinorRegularity.invariantDensity (decode (restPolar hbar c m x)) = 1 := by
  rw [restPolar, decode_encode (DiracRestField.regular hbar c m x), DiracRestField.invariantDensity_one]

/-- The polar rest wave is globally smooth. -/
theorem smooth_restPolar (hbar c m : ℝ) (x : Covector) : ContMDiffAt 𝓘(ℝ,Covector) model ∞ (restPolar hbar c m) x :=
  contMDiffAt_encode (DiracRestField.contDiff_field hbar c m ∞).contDiffAt (DiracRestField.regular hbar c m x)

/-- The represented rest wave has finite zero ordinary action and is stationary for both actions. -/
theorem rest_stationary (hbar c m : ℝ) (hhbar : hbar ≠ 0) {U : Set Covector} (hU : IsOpen U) :
    RelativeStationary hbar c m U (restPolar hbar c m) ∧
      FiniteStationary hbar c m U (restPolar hbar c m) ∧ DiracHSAction.action hbar c m (restPolar hbar c m) U = 0 := by
  have h := rest_represents hbar c m U
  have hd : ∀ x ∈ U, ContDiffAt ℝ 1 (DiracRestField.field hbar c m) x :=
    fun _ _ => (DiracRestField.contDiff_field hbar c m 1).contDiffAt
  have he : ∀ x ∈ U, diracField hbar m c (DiracRestField.field hbar c m) x = 0 :=
    fun x _ => DiracRestField.diracField_zero hbar c m hhbar x
  exact ⟨(relative_iff_spinor hbar c m hU h).mpr (DiracStationaryAction.relative_of_equation hbar c m hU he),
    finite_of_equation hbar c m hU h hd he, action_eq_zero_of_equation hbar c m hU h hd he⟩

/-- The positive-time half-space, where the spinor time ramp is strictly regular. -/
def positiveTime : Set Covector := {x | 0 < x 0}

/-- The counterexample domain is an open and nonempty subset of spacetime. -/
theorem open_nonempty_positiveTime : IsOpen positiveTime ∧ positiveTime.Nonempty :=
  ⟨isOpen_lt continuous_const (continuous_apply 0), ⟨fun _ => 1, by change (0 : ℝ) < 1; norm_num⟩⟩

/-- At zero speed a smooth quotient field can have both stationary actions while its
realized Dirac residual is nonzero at every point of a nonempty open domain. -/
theorem zero_speed_counterexample (m : ℝ) :
    ∃ q : Covector → Q, (∀ x ∈ positiveTime, ContMDiffAt 𝓘(ℝ,Covector) model ∞ q x) ∧
      RelativeStationary 1 0 m positiveTime q ∧ FiniteStationary 1 0 m positiveTime q ∧
      ∀ x ∈ positiveTime, diracField 1 m 0 (fun y => decode (q y)) x ≠ 0 := by
  let q := fun y => encode (timeRamp y)
  obtain ⟨hU, hs, hr⟩ := regular_stationary_without_equation m
  have h : Represents positiveTime q timeRamp := encode_represents (fun x hx => (hr x hx).1)
  have hψ : ∀ x ∈ positiveTime, ContDiffAt ℝ 1 timeRamp x := fun _ _ => (contDiff_timeRamp 1).contDiffAt
  refine ⟨q, (fun x hx => (smooth_iff hU h hx).mpr (contDiff_timeRamp ∞).contDiffAt), (relative_iff_spinor 1 0 m hU h).mpr hs, ?_, ?_⟩
  · have hd (x : Covector) : DiracActionSupport.dens 1 0 m timeRamp x = 0 := densityRe_zero_speed 1 m _ _
    have hfin : MeasureTheory.IntegrableOn (DiracActionSupport.dens 1 0 m timeRamp) positiveTime :=
      MeasureTheory.integrableOn_zero.congr_fun (fun x _ => (hd x).symm) hU.measurableSet
    exact ⟨(DiracHSAction.integrable_iff 1 0 m hU h hψ).mpr hfin,
      (absolute_iff_spinor 1 0 m hU h).mpr ((DiracStationaryAction.absolute_iff_relative 1 0 m hU hfin).mpr hs)⟩
  · intro x hx
    have he : (fun y => decode (q y)) =ᶠ[𝓝 x] timeRamp :=
      Filter.mem_of_superset (hU.mem_nhds hx) (fun y hy => h y hy)
    have hres : diracField 1 m 0 (fun y => decode (q y)) x = diracField 1 m 0 timeRamp x := by
      unfold diracField
      rw [he.self_of_nhds, he.fderiv_eq]
    rw [hres]
    exact (hr x hx).2

end FoliationQM.DiracHSExamples
