module
public import FoliationQM.RegularPolarHomeomorph
public import Mathlib.Topology.Covering.Quotient
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic.FinCases

/-!
# The actual two-sheeted polar sign covering

Sources: v13 `prop:takabayasi` and `eq:takabayasi_polar`. The natural
amplitude-matrix datum is Hausdorff by its proved coordinate embedding.
The actual two-element group acts by identity and simultaneous negation;
its orbits are the independently defined sign relation. Hausdorff
separation of every datum from its distinct negative supplies actual
disjoint sign neighborhoods.

The existing quotient projection is therefore a genuine covering map,
and the proved regular-spinor homeomorphism transfers the covering to
actual realization. Each fiber is explicitly equivalent to Fin 2, so the
covering is genuinely two-sheeted. The topologies and maps are unchanged.
No global section or global real-angle choice is asserted.
-/

@[expose] public section
noncomputable section
open scoped Matrix.Norms.Operator
open Set Filter Topology
namespace FoliationQM.PolarSignCovering
open PolarSignQuotient PolarDatumTopology RegularPolarHomeomorph

/-- The natural datum space is Hausdorff because its actual amplitude and matrix coordinates embed in a Hausdorff product. -/
instance instT2SpaceDatum : T2Space Datum := isEmbedding_coordinates.t2Space

/-- The actual two-sign action uses identity for zero and simultaneous datum negation for the other element. -/
instance signAction : AddAction (ZMod 2) Datum where
  vadd g d := if g = 0 then d else negDatum d
  zero_vadd d := by
    change (if (0 : ZMod 2) = 0 then d else negDatum d) = d
    simp
  add_vadd g h d := by
    change (if g+h=0 then d else negDatum d) =
      if g=0 then (if h=0 then d else negDatum d) else negDatum (if h=0 then d else negDatum d)
    fin_cases g <;> fin_cases h <;> first | rfl | exact (negDatum_involutive d).symm

/-- Zero in the two-element sign group acts as the actual identity. -/
theorem zero_vadd_datum (d : Datum) : (0 : ZMod 2) +ᵥ d = d := by rfl

/-- The nontrivial two-element sign acts as actual simultaneous amplitude and matrix negation. -/
theorem one_vadd_datum (d : Datum) : (1 : ZMod 2) +ᵥ d = negDatum d := by rfl

/-- Each actual sign operation is continuous in the natural datum topology. -/
instance signContinuous : ContinuousConstVAdd (ZMod 2) Datum where
  continuous_const_vadd g := by
    fin_cases g
    · exact continuous_id
    · exact continuous_negDatum

/-- The actual finite-group orbit is exactly the independently defined explicit sign relation. -/
theorem mem_orbit_iff_related (d e : Datum) :
    d ∈ AddAction.orbit (ZMod 2) e ↔ Related d e := by
  constructor
  · rintro ⟨g, hg⟩
    fin_cases g
    · exact Or.inl hg.symm
    · exact Or.inr hg.symm
  · rintro (h | h)
    · exact ⟨0, h.symm⟩
    · exact ⟨1, h.symm⟩

/-- Every datum has an actual open neighborhood disjoint from its nontrivial sign translate. -/
theorem exists_sign_disjoint_nhds (d : Datum) :
    ∃ U ∈ 𝓝 d, ∀ g : ZMod 2, ((g +ᵥ ·) '' U ∩ U).Nonempty → g = 0 := by
  obtain ⟨U, V, hU, hV, hdU, hdV, hUV⟩ := t2_separation (negDatum_ne_self d).symm
  refine ⟨U ∩ negDatum ⁻¹' V,
    (hU.inter (hV.preimage continuous_negDatum)).mem_nhds ⟨hdU, hdV⟩, ?_⟩
  intro g hg
  fin_cases g
  · rfl
  · change ((negDatum) '' (U ∩ negDatum ⁻¹' V) ∩ (U ∩ negDatum ⁻¹' V)).Nonempty at hg
    rcases hg with ⟨z, ⟨w, hw, rfl⟩, hz⟩
    exact False.elim (Set.disjoint_left.mp hUV hz.1 hw.2)

/-- The actual independent sign-quotient map is a quotient covering for the explicit free two-sign action. -/
theorem quotient_mk_isAddQuotientCoveringMap :
    IsAddQuotientCoveringMap (Quotient.mk signSetoid : Datum → PolarQuotient) (ZMod 2) where
  __ := quotient_mk_isQuotientMap
  continuous_const_vadd := continuous_const_vadd
  apply_eq_iff_mem_orbit := by
    intro d e
    exact (quotient_mk_eq_iff d e).trans (mem_orbit_iff_related d e).symm
  disjoint := exists_sign_disjoint_nhds

/-- The actual sign projection with its existing natural quotient topology is a genuine covering map. -/
theorem quotient_mk_isCoveringMap :
    IsCoveringMap (Quotient.mk signSetoid : Datum → PolarQuotient) :=
  quotient_mk_isAddQuotientCoveringMap.isCoveringMap

/-- The actual natural sign projection is a local homeomorphism. -/
theorem quotient_mk_isLocalHomeomorph :
    IsLocalHomeomorph (Quotient.mk signSetoid : Datum → PolarQuotient) :=
  quotient_mk_isCoveringMap.isLocalHomeomorph

/-- The actual regular-spinor realization is a quotient covering for the same free finite sign action. -/
theorem realize_isAddQuotientCoveringMap :
    IsAddQuotientCoveringMap realize (ZMod 2) :=
  quotient_mk_isAddQuotientCoveringMap.homeomorph_comp regularHomeomorph

/-- The actual datum realization into strict regular spinors is a genuine covering map for the natural topologies. -/
theorem realize_isCoveringMap : IsCoveringMap realize :=
  realize_isAddQuotientCoveringMap.isCoveringMap

/-- The actual datum realization into strict regular spinors is a local homeomorphism. -/
theorem realize_isLocalHomeomorph : IsLocalHomeomorph realize :=
  realize_isCoveringMap.isLocalHomeomorph


/-- Every actual sign-quotient fiber is equivalent to the two-element set, using the proved free sign action and an actual representative. -/
def quotientFiberEquiv (q : PolarQuotient) :
    ((Quotient.mk signSetoid : Datum → PolarQuotient) ⁻¹' {q}) ≃ Fin 2 :=
  (quotient_mk_isAddQuotientCoveringMap.fiberEquivAddGroup
    ⟨q.out, Quotient.out_eq q⟩).trans (ZMod.finEquiv 2).toEquiv.symm

/-- Every actual regular-spinor realization fiber is equivalent to the two-element set, based at its constructed inverse datum. -/
def realizeFiberEquiv (q : RegularSpinor) : (realize ⁻¹' {q}) ≃ Fin 2 :=
  (realize_isAddQuotientCoveringMap.fiberEquivAddGroup
    ⟨inverseDatum q, realize_inverseDatum q⟩).trans (ZMod.finEquiv 2).toEquiv.symm

/-- The actual natural sign quotient has exactly two points in every fiber. -/
theorem quotient_fiber_card (q : PolarQuotient) :
    Nat.card ((Quotient.mk signSetoid : Datum → PolarQuotient) ⁻¹' {q}) = 2 := by
  rw [Nat.card_congr (quotientFiberEquiv q)]
  simp

/-- The actual regular-spinor realization has exactly two points in every fiber. -/
theorem realize_fiber_card (q : RegularSpinor) : Nat.card (realize ⁻¹' {q}) = 2 := by
  rw [Nat.card_congr (realizeFiberEquiv q)]
  simp

end FoliationQM.PolarSignCovering
