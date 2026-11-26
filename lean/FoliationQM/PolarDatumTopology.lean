module
public import FoliationQM.PolarSignQuotient
public import FoliationQM.SpinorMatrixSmooth
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Topology.Constructions
/-!
# Natural topology on concrete polar data and their sign quotient

Source: the concrete polar quotient in v13 `prop:takabayasi` and
`eq:takabayasi_polar`. The existing datum receives the topology induced by
its actual amplitude and matrix coordinates in the product of the complex
plane and the complex matrix space. Its image is exactly nonzero amplitude
paired with determinant-one matrices. The quotient uses Mathlib's standard
coinduced quotient topology, independently of the regular-spinor target.

Coordinatewise continuity, the simultaneous sign homeomorphism, continuity
of actual spinor realization, and the continuous open quotient projection
are proved from this natural topology. Openness follows from the explicit
saturation by the identity and sign involution. No topology is transported
from regular spinors, and no smooth quotient or abstract Spin-covering
classification is assumed.
-/

@[expose] public section
noncomputable section
open scoped Matrix.Norms.Operator Topology
open Set Filter Topology
namespace FoliationQM.PolarDatumTopology
open DiracMatrices SpinorMatrix PolarSignQuotient PolarMatrixFibers

/-- The actual complex amplitude and matrix coordinates of a concrete polar datum. -/
def coordinates (d : Datum) : ℂ × Mat2 := (d.t, d.A)

/-- The natural datum topology is induced from its actual complex amplitude and operator-norm matrix coordinates. -/
instance instTopologicalSpaceDatum : TopologicalSpace Datum :=
  TopologicalSpace.induced coordinates inferInstance

/-- The actual amplitude and matrix coordinates injectively determine a concrete polar datum. -/
theorem coordinates_injective : Function.Injective coordinates := by
  intro d e h
  exact datum_ext (congrArg Prod.fst h) (congrArg Prod.snd h)

/-- The natural coordinate image is exactly the product constraint of nonzero amplitude and determinant-one matrix. -/
theorem coordinates_range : Set.range coordinates =
    {p : ℂ × Mat2 | p.1 ≠ 0 ∧ p.2.det = 1} := by
  ext p
  constructor
  · rintro ⟨d, rfl⟩
    exact ⟨d.t_ne_zero, d.det_eq_one⟩
  · intro hp
    exact ⟨⟨p.1, p.2, hp.1, hp.2⟩, rfl⟩

/-- The actual coordinate map induces the datum topology by its definition. -/
theorem isInducing_coordinates : IsInducing coordinates := .induced _

/-- The actual datum coordinate map is a topological embedding into the ambient product. -/
theorem isEmbedding_coordinates : IsEmbedding coordinates :=
  ⟨isInducing_coordinates, coordinates_injective⟩

/-- The actual paired coordinates vary continuously in the natural datum topology. -/
theorem continuous_coordinates : Continuous coordinates := isInducing_coordinates.continuous

/-- The actual complex amplitude is continuous in the natural datum topology. -/
theorem continuous_t : Continuous Datum.t := continuous_fst.comp continuous_coordinates

/-- The actual determinant-one matrix coordinate is continuous in the natural datum topology. -/
theorem continuous_A : Continuous Datum.A := continuous_snd.comp continuous_coordinates

variable {X : Type*} [TopologicalSpace X]

/-- A map into concrete polar data is continuous exactly when its actual amplitude and matrix coordinates are continuous. -/
theorem continuous_iff {f : X → Datum} :
    Continuous f ↔ Continuous (fun x => (f x).t) ∧ Continuous (fun x => (f x).A) := by
  constructor
  · intro h
    exact ⟨continuous_t.comp h, continuous_A.comp h⟩
  · rintro ⟨ht, hA⟩
    exact isInducing_coordinates.continuous_iff.mpr (ht.prodMk hA)

/-- Continuity at a point into concrete polar data is exactly continuity of its two actual coordinates at that point. -/
theorem continuousAt_iff {f : X → Datum} {x : X} :
    ContinuousAt f x ↔ ContinuousAt (fun y => (f y).t) x ∧ ContinuousAt (fun y => (f y).A) x := by
  constructor
  · intro h
    exact ⟨continuous_t.continuousAt.comp h, continuous_A.continuousAt.comp h⟩
  · rintro ⟨ht, hA⟩
    exact isInducing_coordinates.continuousAt_iff.mpr (ht.prodMk hA)

/-- Continuity within a set into concrete polar data is exactly continuity within that set of its actual coordinates. -/
theorem continuousWithinAt_iff {f : X → Datum} {s : Set X} {x : X} :
    ContinuousWithinAt f s x ↔
      ContinuousWithinAt (fun y => (f y).t) s x ∧ ContinuousWithinAt (fun y => (f y).A) s x := by
  constructor
  · intro h
    exact ⟨continuous_t.continuousAt.comp_continuousWithinAt h,
      continuous_A.continuousAt.comp_continuousWithinAt h⟩
  · rintro ⟨ht, hA⟩
    exact isInducing_coordinates.tendsto_nhds_iff.mpr (ht.prodMk hA)

/-- Continuity on a set into concrete polar data is exactly continuity on that set of its actual coordinates. -/
theorem continuousOn_iff {f : X → Datum} {s : Set X} :
    ContinuousOn f s ↔ ContinuousOn (fun y => (f y).t) s ∧ ContinuousOn (fun y => (f y).A) s := by
  constructor
  · intro h
    exact ⟨fun x hx => (continuousWithinAt_iff.mp (h x hx)).1,
      fun x hx => (continuousWithinAt_iff.mp (h x hx)).2⟩
  · rintro ⟨ht, hA⟩ x hx
    exact continuousWithinAt_iff.mpr ⟨ht x hx, hA x hx⟩

/-- The simultaneous sign transformation is continuous in the natural amplitude-matrix topology. -/
theorem continuous_negDatum : Continuous negDatum := by
  apply continuous_iff.mpr
  exact ⟨continuous_t.neg, continuous_A.neg⟩

/-- The actual simultaneous sign involution is a homeomorphism of concrete polar data. -/
def negHomeomorph : Datum ≃ₜ Datum where
  toFun := negDatum
  invFun := negDatum
  left_inv := negDatum_involutive
  right_inv := negDatum_involutive
  continuous_toFun := continuous_negDatum
  continuous_invFun := continuous_negDatum

/-- The actual regular-spinor realization is continuous from the natural datum topology. -/
theorem continuous_realize : Continuous realize := by
  have h : Continuous (fun d : Datum => parameterSpinor d.t d.A) :=
    continuousLinearEquiv.symm.continuous.comp (continuous_t.smul continuous_A)
  exact h.subtype_mk _

/-- The projection to the existing sign quotient is continuous for its standard coinduced quotient topology. -/
theorem quotient_mk_continuous :
    Continuous (Quotient.mk signSetoid : Datum → PolarQuotient) := continuous_quotient_mk'

/-- The projection is a genuine quotient map for the standard quotient topology, with no target-induced replacement. -/
theorem quotient_mk_isQuotientMap :
    IsQuotientMap (Quotient.mk signSetoid : Datum → PolarQuotient) := isQuotientMap_quotient_mk'

/-- The exact saturation of a datum set consists of that set and its inverse image under simultaneous sign reversal. -/
theorem quotient_saturation (s : Set Datum) :
    (Quotient.mk signSetoid : Datum → PolarQuotient) ⁻¹'
        ((Quotient.mk signSetoid : Datum → PolarQuotient) '' s) = s ∪ negDatum ⁻¹' s := by
  ext d
  constructor
  · rintro ⟨e, he, heq⟩
    rcases (quotient_mk_eq_iff e d).mp heq with h | h
    · exact Or.inl (h ▸ he)
    · exact Or.inr (show negDatum d ∈ s from h ▸ he)
  · rintro (hd | hd)
    · exact ⟨d, hd, rfl⟩
    · exact ⟨negDatum d, hd, quotient_negDatum d⟩

/-- The actual sign-quotient projection is open because every open set has the explicit two-sign open saturation. -/
theorem quotient_mk_isOpenMap :
    IsOpenMap (Quotient.mk signSetoid : Datum → PolarQuotient) := by
  intro s hs
  apply quotient_mk_isQuotientMap.isOpen_preimage.mp
  rw [quotient_saturation]
  exact hs.union (hs.preimage continuous_negDatum)

end FoliationQM.PolarDatumTopology
