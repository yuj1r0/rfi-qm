module
public import FoliationQM.PolarSignCovering
public import Mathlib.Topology.Homotopy.Lifting

/-!
# Anchored local lifts and connected uniqueness for the actual polar covering

Sources: the concrete polar sign quotient in v13 `prop:takabayasi` and
`eq:takabayasi_polar`. All results use the proved covering of the actual
regular-spinor realization and the natural sign-quotient projection.
Continuous lifts on a preconnected domain agree if they agree at one
point. Their two pointwise sign possibilities therefore reduce to one
single global sign. A subset version only requires continuity on the
preconnected subset.

Every prescribed datum admits a continuous local section on an open
neighborhood of its image. Pulling this section back gives an anchored
local lift of a continuous regular-spinor field. Every continuous path
on the actual closed unit interval has a unique continuous lift after
its initial datum is specified. These are actual local and path lifts;
no global section or global continuous real-angle choice is asserted.
-/

@[expose] public section
noncomputable section
open scoped Matrix.Norms.Operator Topology
open Set Filter Topology unitInterval
namespace FoliationQM.PolarCoveringLifts
open PolarSignQuotient PolarDatumTopology PolarSignCovering


/-- Continuous actual polar lifts on a preconnected domain agree everywhere when they agree at one point. -/
theorem realize_lift_unique {X : Type*} [TopologicalSpace X] [PreconnectedSpace X]
    {f g : X → Datum} (hf : Continuous f) (hg : Continuous g)
    (he : realize ∘ f = realize ∘ g) (x₀ : X) (h₀ : f x₀ = g x₀) : f = g :=
  realize_isCoveringMap.eq_of_comp_eq hf hg he x₀ h₀

/-- Continuous lifts of the natural sign-quotient projection on a preconnected domain are fixed by their value at one point. -/
theorem quotient_lift_unique {X : Type*} [TopologicalSpace X] [PreconnectedSpace X]
    {f g : X → Datum} (hf : Continuous f) (hg : Continuous g)
    (he : (Quotient.mk signSetoid : Datum → PolarQuotient) ∘ f =
      (Quotient.mk signSetoid : Datum → PolarQuotient) ∘ g)
    (x₀ : X) (h₀ : f x₀ = g x₀) : f = g :=
  quotient_mk_isCoveringMap.eq_of_comp_eq hf hg he x₀ h₀

/-- Actual polar lift uniqueness also holds on a preconnected subset, with continuity required only on that subset. -/
theorem realize_lift_uniqueOn {X : Type*} [TopologicalSpace X]
    {s : Set X} (hs : IsPreconnected s) {f g : X → Datum}
    (hf : ContinuousOn f s) (hg : ContinuousOn g s)
    (he : s.EqOn (realize ∘ f) (realize ∘ g)) {x₀ : X}
    (hx₀ : x₀ ∈ s) (h₀ : f x₀ = g x₀) : s.EqOn f g :=
  realize_isCoveringMap.eqOn_of_comp_eqOn hs hf hg he hx₀ h₀

/-- The two possible pointwise signs of continuous actual polar lifts reduce to one global sign on any nonempty preconnected domain. -/
theorem realize_lifts_eq_iff {X : Type*} [TopologicalSpace X] [PreconnectedSpace X]
    {f g : X → Datum} (hf : Continuous f) (hg : Continuous g) (x₀ : X) :
    realize ∘ f = realize ∘ g ↔ f = g ∨ f = negDatum ∘ g := by
  constructor
  · intro he
    rcases (realize_eq_iff_related (f x₀) (g x₀)).mp (congrFun he x₀) with h | h
    · exact Or.inl (realize_lift_unique hf hg he x₀ h)
    · apply Or.inr
      apply realize_lift_unique hf (continuous_negDatum.comp hg) _ x₀ h
      funext x
      exact (congrFun he x).trans
        ((realize_eq_iff_related (negDatum (g x)) (g x)).mpr (Or.inr rfl)).symm
  · rintro (rfl | rfl)
    · rfl
    · funext x
      exact (realize_eq_iff_related (negDatum (g x)) (g x)).mpr (Or.inr rfl)

/-- The same single global sign classifies continuous lifts of the natural quotient map on a nonempty preconnected domain. -/
theorem quotient_lifts_eq_iff {X : Type*} [TopologicalSpace X] [PreconnectedSpace X]
    {f g : X → Datum} (hf : Continuous f) (hg : Continuous g) (x₀ : X) :
    (Quotient.mk signSetoid : Datum → PolarQuotient) ∘ f =
        (Quotient.mk signSetoid : Datum → PolarQuotient) ∘ g ↔
      f = g ∨ f = negDatum ∘ g := by
  constructor
  · intro he
    apply (realize_lifts_eq_iff hf hg x₀).mp
    funext x
    exact congrArg toRegular (congrFun he x)
  · rintro (rfl | rfl)
    · rfl
    · funext x
      exact quotient_negDatum (g x)

/-- Every prescribed actual polar datum is the value of a continuous local section over an open neighborhood of its realized spinor. -/
theorem exists_realize_local_section (d : Datum) :
    ∃ U : Set RegularSpinor, IsOpen U ∧ realize d ∈ U ∧
      ∃ s : RegularSpinor → Datum, ContinuousOn s U ∧ s (realize d) = d ∧
        ∀ q ∈ U, realize (s q) = q := by
  let h := realize_isCoveringMap.isLocalHomeomorph
  let e := h.localInverseAt d
  refine ⟨e.source, e.open_source, h.apply_self_mem_localInverseAt_source,
    e, e.continuousOn, h.localInverseAt_apply_self, ?_⟩
  intro q hq
  exact h.apply_localInverseAt_of_mem hq

/-- The natural quotient projection has a continuous local section through each prescribed representative. -/
theorem exists_quotient_local_section (d : Datum) :
    ∃ U : Set PolarQuotient, IsOpen U ∧ Quotient.mk signSetoid d ∈ U ∧
      ∃ s : PolarQuotient → Datum, ContinuousOn s U ∧
        s (Quotient.mk signSetoid d) = d ∧
        ∀ q ∈ U, Quotient.mk signSetoid (s q) = q := by
  let h := quotient_mk_isCoveringMap.isLocalHomeomorph
  let e := h.localInverseAt d
  refine ⟨e.source, e.open_source, h.apply_self_mem_localInverseAt_source,
    e, e.continuousOn, h.localInverseAt_apply_self, ?_⟩
  intro q hq
  exact h.apply_localInverseAt_of_mem hq

/-- A continuous regular-spinor field has an actual continuous local polar lift through any prescribed datum in its fiber. -/
theorem exists_local_lift {X : Type*} [TopologicalSpace X]
    (f : X → RegularSpinor) (hf : Continuous f) (x₀ : X) (d : Datum)
    (h₀ : f x₀ = realize d) :
    ∃ U : Set X, IsOpen U ∧ x₀ ∈ U ∧
      ∃ g : X → Datum, ContinuousOn g U ∧ g x₀ = d ∧
        ∀ x ∈ U, realize (g x) = f x := by
  obtain ⟨V, hV, hd, s, hs, hsd, hsec⟩ := exists_realize_local_section d
  refine ⟨f ⁻¹' V, hV.preimage hf, ?_, s ∘ f, ?_, ?_, ?_⟩
  · simpa only [Set.mem_preimage, h₀] using hd
  · exact hs.comp hf.continuousOn (fun _ hx => hx)
  · exact (congrArg s h₀).trans hsd
  · intro x hx
    exact hsec (f x) hx

/-- Every continuous regular-spinor path has a unique actual continuous polar lift after specifying its initial datum. -/
theorem existsUnique_realize_path_lift (γ : C(I, RegularSpinor))
    (d : Datum) (h₀ : γ 0 = realize d) :
    ∃! Γ : C(I, Datum), realize ∘ Γ = γ ∧ Γ 0 = d := by
  refine ⟨realize_isCoveringMap.liftPath γ d h₀, ⟨realize_isCoveringMap.liftPath_lifts γ d h₀,
    realize_isCoveringMap.liftPath_zero γ d h₀⟩, ?_⟩
  intro Γ hΓ
  exact (realize_isCoveringMap.eq_liftPath_iff' h₀).mpr hΓ

/-- Every continuous path in the natural polar sign quotient has a unique continuous representative path with prescribed initial datum. -/
theorem existsUnique_quotient_path_lift (γ : C(I, PolarQuotient))
    (d : Datum) (h₀ : γ 0 = Quotient.mk signSetoid d) :
    ∃! Γ : C(I, Datum),
      (Quotient.mk signSetoid : Datum → PolarQuotient) ∘ Γ = γ ∧ Γ 0 = d := by
  refine ⟨quotient_mk_isCoveringMap.liftPath γ d h₀, ⟨quotient_mk_isCoveringMap.liftPath_lifts γ d h₀,
    quotient_mk_isCoveringMap.liftPath_zero γ d h₀⟩, ?_⟩
  intro Γ hΓ
  exact (quotient_mk_isCoveringMap.eq_liftPath_iff' h₀).mpr hΓ

end FoliationQM.PolarCoveringLifts
