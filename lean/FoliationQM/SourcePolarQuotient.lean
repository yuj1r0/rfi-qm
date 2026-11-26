module
public import FoliationQM.SourcePolarDatum
public import FoliationQM.RegularPolarHomeomorph
public import Mathlib.Topology.Homeomorph.Quotient
/-!
# The literal source polar sign quotient with its natural topology

Sources: v13 `prop:takabayasi` and `eq:takabayasi_polar`. The source data
are positive density, the full angle modulo four pi, and a concrete
complex determinant-one matrix. Their relation is independently defined
as equality or the literal simultaneous two-pi angle shift and matrix
negation. Its setoid laws are proved from the actual involution, before
relating it to the existing nonzero-amplitude sign quotient.

The natural coordinate homeomorphism intertwines the two explicitly
specified relations. It therefore induces a genuine homeomorphism of the
standard quotient topologies, and then a homeomorphism to all strictly
regular spinors. Exact representative fibers and the continuous open
quotient projection are proved. No relation is defined by target equality,
no target topology is transported onto the quotient, and no global real
angle or abstract Spin-group identification is assumed.
-/

@[expose] public section
noncomputable section
open scoped Matrix.Norms.Operator Topology
open Set Topology
namespace FoliationQM.SourcePolarQuotient
open SourcePolarDatum

/-- The source relation independently identifies literal equality or a simultaneous two-pi angle shift and matrix sign reversal. -/
def Related (d e : SourceDatum) : Prop := d = e ∨ d = shiftNeg e

/-- The independently defined source sign relation is reflexive. -/
theorem related_refl (d : SourceDatum) : Related d d := Or.inl rfl

/-- The source sign relation is symmetric because the literal shift and sign operation is an involution. -/
theorem related_symm {d e : SourceDatum} (h : Related d e) : Related e d := by
  rcases h with h | h
  · exact Or.inl h.symm
  · exact Or.inr (by rw [h, shiftNeg_involutive])

/-- Two successive source sign identifications again give either equality or one literal shift and sign reversal. -/
theorem related_trans {d e f : SourceDatum} (hde : Related d e) (hef : Related e f) :
    Related d f := by
  rcases hde with hde | hde <;> rcases hef with hef | hef
  · exact Or.inl (hde.trans hef)
  · exact Or.inr (hde.trans hef)
  · exact Or.inr (by rw [hde, hef])
  · exact Or.inl (by rw [hde, hef, shiftNeg_involutive])

/-- The source setoid is built from the independently defined equality-or-shift relation. -/
def signSetoid : Setoid SourceDatum where
  r := Related
  iseqv := ⟨related_refl, related_symm, related_trans⟩

/-- The actual quotient of positive density, four-pi angle and determinant-one matrix data by the literal source sign relation. -/
abbrev SourceQuotient := Quotient signSetoid

/-- The actual coordinate homeomorphism identifies the independently defined source relation with the independently defined amplitude sign relation. -/
theorem related_iff_target (d e : SourceDatum) :
    Related d e ↔ PolarSignQuotient.Related (toDatum d) (toDatum e) := by
  constructor
  · rintro (h | h)
    · exact Or.inl (congrArg toDatum h)
    · exact Or.inr ((congrArg toDatum h).trans (toDatum_shiftNeg e))
  · rintro (h | h)
    · apply Or.inl
      apply datumHomeomorph.injective
      simpa only [datumHomeomorph_apply] using h
    · apply Or.inr
      apply datumHomeomorph.injective
      simpa only [datumHomeomorph_apply, toDatum_shiftNeg] using h

/-- The natural source quotient is homeomorphic to the natural amplitude sign quotient through the actual coordinate homeomorphism. -/
def quotientHomeomorph : SourceQuotient ≃ₜ PolarSignQuotient.PolarQuotient :=
  Homeomorph.Quotient.congr datumHomeomorph related_iff_target

/-- The quotient homeomorphism sends every actual source representative to the class of its actual amplitude datum. -/
theorem quotientHomeomorph_apply_mk (d : SourceDatum) :
    quotientHomeomorph (Quotient.mk signSetoid d) =
      Quotient.mk PolarSignQuotient.signSetoid (toDatum d) := rfl

/-- The literal source sign quotient with its standard topology is homeomorphic to the actual strict regular-spinor subtype. -/
def regularHomeomorph : SourceQuotient ≃ₜ PolarSignQuotient.RegularSpinor :=
  quotientHomeomorph.trans RegularPolarHomeomorph.regularHomeomorph

/-- The regular-spinor homeomorphism realizes each source class through its actual amplitude and matrix coordinates. -/
theorem regularHomeomorph_apply_mk (d : SourceDatum) :
    regularHomeomorph (Quotient.mk signSetoid d) = PolarSignQuotient.realize (toDatum d) := rfl

/-- Two actual source representatives have the same quotient class exactly under the independently defined literal source relation. -/
theorem quotient_mk_eq_iff (d e : SourceDatum) :
    Quotient.mk signSetoid d = Quotient.mk signSetoid e ↔ Related d e := Quotient.eq

/-- The source quotient identifies the actual two-pi angle shift with simultaneous matrix negation. -/
theorem quotient_shiftNeg (d : SourceDatum) :
    Quotient.mk signSetoid (shiftNeg d) = Quotient.mk signSetoid d :=
  Quotient.sound (Or.inr rfl)

/-- Equality of the realized regular-spinor images of source representatives has exactly the proved literal source relation as its fibers. -/
theorem regularHomeomorph_mk_eq_iff (d e : SourceDatum) :
    regularHomeomorph (Quotient.mk signSetoid d) =
      regularHomeomorph (Quotient.mk signSetoid e) ↔ Related d e := by
  rw [regularHomeomorph.injective.eq_iff, quotient_mk_eq_iff]

/-- The source quotient projection is continuous for the standard coinduced quotient topology. -/
theorem quotient_mk_continuous :
    Continuous (Quotient.mk signSetoid : SourceDatum → SourceQuotient) := continuous_quotient_mk'

/-- The actual source projection is a genuine quotient map for the natural source and standard quotient topologies. -/
theorem quotient_mk_isQuotientMap :
    IsQuotientMap (Quotient.mk signSetoid : SourceDatum → SourceQuotient) :=
  isQuotientMap_quotient_mk'

/-- The exact source quotient saturation is the original set together with its inverse image under the literal shift and sign involution. -/
theorem quotient_saturation (s : Set SourceDatum) :
    (Quotient.mk signSetoid : SourceDatum → SourceQuotient) ⁻¹'
        ((Quotient.mk signSetoid : SourceDatum → SourceQuotient) '' s) = s ∪ shiftNeg ⁻¹' s := by
  ext d
  constructor
  · rintro ⟨e, he, heq⟩
    rcases (quotient_mk_eq_iff e d).mp heq with h | h
    · exact Or.inl (h ▸ he)
    · exact Or.inr (show shiftNeg d ∈ s from h ▸ he)
  · rintro (hd | hd)
    · exact ⟨d, hd, rfl⟩
    · exact ⟨shiftNeg d, hd, quotient_shiftNeg d⟩

/-- The actual source quotient projection is open by the explicit two-sign saturation and continuity of the literal shift operation. -/
theorem quotient_mk_isOpenMap :
    IsOpenMap (Quotient.mk signSetoid : SourceDatum → SourceQuotient) := by
  intro s hs
  apply quotient_mk_isQuotientMap.isOpen_preimage.mp
  rw [quotient_saturation]
  exact hs.union (hs.preimage shiftNegHomeomorph.continuous)

end FoliationQM.SourcePolarQuotient
