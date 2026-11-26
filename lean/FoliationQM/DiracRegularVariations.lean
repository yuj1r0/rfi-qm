module
public import FoliationQM.DiracStationaryAction
public import FoliationQM.LocalPolarFields
public import Mathlib.Topology.Compactness.Compact

/-!
# Compact interior variations inside the regular spinor domain

For v13 `thm:dirac_lift` and `prop:takabayasi`, strict invariant
regularity on the background domain persists uniformly near parameter
zero on the compact carrier. Outside that carrier the field is fixed.
Shrinking the parameter set thus preserves the actual family and its
relative action while providing a regular variation.
-/

@[expose] public section
noncomputable section
open scoped Topology ContDiff
namespace FoliationQM.DiracRegularVariations
open Set Filter DiracMatrices SpinorRegularity DiracInteriorVariation
open DiracCurveJetCalculus DiracRelativeAction DiracStationaryAction

/-- An admissible compact interior variation taking values in the strict regular
spinor domain throughout its allowed parameter neighborhood. -/
structure RegularVariation (U : Set Covector) (ψ : Covector → Spinor) extends Variation U ψ where
  /-- Positive invariant density on the original spacetime domain and allowed parameters. -/
  regular : ∀ t ∈ params, ∀ x ∈ U, Regular (family (t, x))

variable {U : Set Covector} {ψ : Covector → Spinor}

/-- Restricting to the initial slice of a regular variation gives regularity of its background. -/
theorem initial_regular (V : RegularVariation U ψ) {x : Covector} (hx : x ∈ U) : Regular (ψ x) := by
  rw [← V.initial x]
  exact V.regular 0 V.zero_mem x hx

/-- One open parameter neighborhood works simultaneously on the entire original spatial domain.
Compactness is used only on the carrier where the family can change. -/
theorem exists_regular_params (V : Variation U ψ) (hU : IsOpen U) (hreg : ∀ x ∈ U, Regular (ψ x)) :
    ∃ p : Set ℝ, IsOpen p ∧ 0 ∈ p ∧ p ⊆ V.params ∧
      ∀ t ∈ p, ∀ x ∈ U, Regular (V.family (t, x)) := by
  let D := V.params ×ˢ U
  let N := D ∩ V.family ⁻¹' {u : Spinor | Regular u}
  have hD : IsOpen D := V.params_open.prod hU
  have hF : ContinuousOn V.family D :=
    fun z hz => (V.smooth z.1 hz.1 z.2 hz.2).continuousAt.continuousWithinAt
  have hN : IsOpen N := hF.isOpen_inter_preimage hD LocalPolarFields.regularDomain_isOpen
  have h0 : ({0} : Set ℝ) ×ˢ V.carrier ⊆ N := by
    rintro ⟨t, x⟩ ⟨ht, hx⟩
    obtain rfl : t = 0 := mem_singleton_iff.mp ht
    refine ⟨⟨V.zero_mem, V.interior hx⟩, ?_⟩
    change Regular (V.family (0, x))
    rw [V.initial x]
    exact hreg x (V.interior hx)
  obtain ⟨p, W, hp, _, hp0, hK, htube⟩ :=
    generalized_tube_lemma (isCompact_singleton (x := (0 : ℝ))) V.compact hN h0
  refine ⟨p ∩ V.params, hp.inter V.params_open, ⟨hp0 (mem_singleton _), V.zero_mem⟩,
    inter_subset_right, ?_⟩
  intro t ht x hx
  by_cases hxc : x ∈ V.carrier
  · exact (htube (show (t, x) ∈ p ×ˢ W from ⟨ht.1, hK hxc⟩)).2
  · rw [V.fixed t ht.2 x hxc]
    exact hreg x hx

variable (V : Variation U ψ) (hU : IsOpen U) (hreg : ∀ x ∈ U, Regular (ψ x))

/-- Choose a regular parameter neighborhood, keeping the original field and compact carrier. -/
def restrict : RegularVariation U ψ :=
  let h := (exists_regular_params V hU hreg).choose_spec
  { toVariation :=
      { V with
        params := (exists_regular_params V hU hreg).choose
        params_open := h.1
        zero_mem := h.2.1
        smooth := fun t ht => V.smooth t (h.2.2.1 ht)
        fixed := fun t ht => V.fixed t (h.2.2.1 ht) }
    regular := h.2.2.2 }

/-- The joint spinor field is unchanged even away from the smaller parameter set. -/
theorem restrict_family : (restrict V hU hreg).family = V.family := rfl

/-- The original compact interior carrier remains the one designated by the new variation. -/
theorem restrict_carrier : (restrict V hU hreg).carrier = V.carrier := rfl

/-- All parameters admitted by the restriction were originally admitted. -/
theorem restrict_params_subset : (restrict V hU hreg).params ⊆ V.params :=
  (exists_regular_params V hU hreg).choose_spec.2.2.1

/-- The original and restricted parameter sets have the same germ at zero. -/
theorem restrict_params_germ : ∀ᶠ t in 𝓝 (0 : ℝ), t ∈ (restrict V hU hreg).params ↔ t ∈ V.params := by
  let W := restrict V hU hreg
  filter_upwards [W.params_open.mem_nhds W.zero_mem, V.params_open.mem_nhds V.zero_mem]
    with t ht hv
  exact iff_of_true ht hv

/-- The relative action curve has exactly the same values under the restriction. -/
theorem restrict_relativeAction (hbar c m t : ℝ) :
    relativeAction hbar c m ψ (slice (restrict V hU hreg).family t) U =
      relativeAction hbar c m ψ (slice V.family t) U := rfl

variable (hbar c m : ℝ)

/-- Vanishing derivative of the actual relative action along all regular compact interior variations. -/
def RegularStationary (U : Set Covector) (ψ : Covector → Spinor) : Prop :=
  ∀ W : RegularVariation U ψ,
    HasDerivAt (fun t => relativeAction hbar c m ψ (slice W.family t) U) 0 0

/-- At a regular background, testing only regular variations detects all admissible variations. -/
theorem regularStationary_iff_relative (hU : IsOpen U) (hreg : ∀ x ∈ U, Regular (ψ x)) :
    RegularStationary hbar c m U ψ ↔ RelativeStationary hbar c m U ψ :=
  ⟨fun h V => h (restrict V hU hreg), fun h W => h W.toVariation⟩

/-- On the smooth regular domain, stationarity along regular families is equivalent to
the actual flat-coordinate Dirac equation when the speed parameter is nonzero. -/
theorem regularStationary_iff (hU : IsOpen U) (hreg : ∀ x ∈ U, Regular (ψ x))
    (hψ : ∀ x ∈ U, ContDiffAt ℝ ∞ ψ x) (hc : c ≠ 0) :
    RegularStationary hbar c m U ψ ↔ ∀ x ∈ U, DiracEquation.diracField hbar m c ψ x = 0 :=
  (regularStationary_iff_relative hbar c m hU hreg).trans (DiracStationaryAction.relative_iff hbar c m hU hψ hc)

end FoliationQM.DiracRegularVariations
