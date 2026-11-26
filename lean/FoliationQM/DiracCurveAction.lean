module
public import FoliationQM.DiracRelativeAction
public import FoliationQM.DiracInteriorVariation
public import FoliationQM.OpenCompactIntegralVariation

/-!
# Differentiation of the Dirac action along actual compact interior families

For v13 `thm:dirac_lift`, joint local smoothness and a common compact
interior support justify differentiating the integral. The initial
relative density is zero. The ordinary action has the same derivative
when the background density is integrable on the domain.
-/

@[expose] public section
noncomputable section
open scoped Topology ContDiff
namespace FoliationQM.DiracCurveAction
open MeasureTheory DiracMatrices DiracCurveJetCalculus DiracActionSupport
open DiracInteriorVariation DiracRelativeAction

variable (hbar c m : ℝ) {U : Set Covector} {ψ : Covector → Spinor}
  (V : Variation U ψ)

/-- The change in the actual density is jointly continuous on the parameter neighborhood and domain. -/
theorem continuousOn_difference :
    ContinuousOn (fun q : ℝ × Covector => density hbar c m V.family q.1 q.2 - dens hbar c m ψ q.2)
      (V.params ×ˢ U) := by
  have h := continuousOn_density hbar c m V.smooth
  have ht : Continuous (fun q : ℝ × Covector => ((0 : ℝ), q.2)) :=
    continuous_const.prodMk continuous_snd
  have hm : Set.MapsTo (fun q : ℝ × Covector => ((0 : ℝ), q.2))
      (V.params ×ˢ U) (V.params ×ˢ U) := fun _ hz => ⟨V.zero_mem,hz.2⟩
  have h0 := h.comp ht.continuousOn hm
  change ContinuousOn (fun q : ℝ × Covector => density hbar c m V.family 0 q.2) (V.params ×ˢ U) at h0
  simp only [density_eq_fieldDensityRe, slice_zero] at h0
  exact h.sub h0

/-- Each density agrees with the background outside the compact carrier, including its jet terms. -/
theorem density_fixed {t : ℝ} (ht : t ∈ V.params) {x : Covector} (hx : x ∉ V.carrier) :
    density hbar c m V.family t x = dens hbar c m ψ x := by
  apply dens_eq_of_eventuallyEq
  filter_upwards [V.compact.isClosed.isOpen_compl.mem_nhds hx] with y hy
  exact V.fixed t ht y hy

/-- Every slice has an integrable density difference on the given open domain. -/
theorem integrable_difference (hU : IsOpen U) {t : ℝ} (ht : t ∈ V.params) :
    IntegrableOn (fun x => density hbar c m V.family t x - dens hbar c m ψ x) U := by
  have hz (x : Covector) : density hbar c m V.family 0 x = dens hbar c m ψ x := by
    change dens hbar c m (slice V.family 0) x = _
    rw [slice_zero V]
  apply OpenCompactIntegralVariation.integrable_of_eq_outside_compact hU
    (F := fun r x => density hbar c m V.family r x - dens hbar c m ψ x)
    (continuousOn_difference hbar c m V) V.zero_mem V.compact V.interior _ _ ht
  · intro r hr x _ hx
    rw [density_fixed hbar c m V hr hx, hz]
  · simp only [hz, sub_self]
    exact integrable_zero _ _ _

/-- The action derivative equals the integral of the polarized density with the actual velocity. -/
theorem hasDerivAt_relative (hU : IsOpen U) :
    HasDerivAt (fun t => relativeAction hbar c m ψ (slice V.family t) U)
      (∫ x in U, first hbar c m ψ (velocity V.family 0) x) 0 := by
  have H := OpenCompactIntegralVariation.hasDerivAt_integral_of_compact_support
    (F := fun t x => density hbar c m V.family t x - dens hbar c m ψ x)
    (F' := fun t x => DiracCurveJetCalculus.firstDensity hbar c m V.family t x)
    hU (V.params_open.mem_nhds V.zero_mem) (continuousOn_difference hbar c m V)
    (continuousOn_first hbar c m V.smooth) V.compact V.interior
    (fun t ht x _ hx => first_eq_zero_of_notMem_tsupport hbar c m _ _
      (fun h => hx (velocity_tsupport V ht h)))
    (fun t ht x hx => (hasDerivAt_density hbar c m (V.smooth t ht x hx)).sub_const _)
    (show IntegrableOn (fun x => density hbar c m V.family 0 x - dens hbar c m ψ x) U from by
      simp only [density_eq_fieldDensityRe, slice_zero V, dens, sub_self]
      exact integrable_zero _ _ _)
  change HasDerivAt _ (∫ x in U, first hbar c m ψ (velocity V.family 0) x) 0
  have he : DiracCurveJetCalculus.firstDensity hbar c m V.family 0 =
      first hbar c m ψ (velocity V.family 0) := by
    funext x
    rw [firstDensity_eq, slice_zero]
    rfl
  rw [← he]
  exact H.2

/-- If the background action is finite, the ordinary action has the same derivative. -/
theorem hasDerivAt_action (hU : IsOpen U) (hbase : IntegrableOn (dens hbar c m ψ) U) :
    HasDerivAt (fun t => action hbar c m (slice V.family t) U)
      (∫ x in U, first hbar c m ψ (velocity V.family 0) x) 0 := by
  have he : (fun t => action hbar c m (slice V.family t) U) =ᶠ[𝓝 0]
      (fun t => relativeAction hbar c m ψ (slice V.family t) U + action hbar c m ψ U) := by
    filter_upwards [V.params_open.mem_nhds V.zero_mem] with t ht
    have hd := integrable_difference hbar c m V hU ht
    have hφ : IntegrableOn (dens hbar c m (slice V.family t)) U := by
      have hh := hd.add hbase
      change IntegrableOn (fun x => density hbar c m V.family t x - dens hbar c m ψ x + dens hbar c m ψ x) U at hh
      change IntegrableOn (fun x => DiracFieldDensity.fieldDensityRe hbar c m (slice V.family t) x DiracFieldDensity.coordinateDirections) U
      simpa only [sub_add_cancel, density_eq_fieldDensityRe] using hh
    rw [relative_eq_action_sub hbar c m hbase hφ]
    ring
  exact ((hasDerivAt_relative hbar c m V hU).add_const _).congr_of_eventuallyEq he

end FoliationQM.DiracCurveAction
