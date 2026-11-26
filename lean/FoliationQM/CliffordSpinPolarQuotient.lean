module
public import FoliationQM.CliffordSpinPolarRealization
public import FoliationQM.SourcePolarProductQuotient
public import Mathlib.Topology.Homeomorph.Quotient

/-!
# Natural sign quotients of literal Clifford Spin polar data

Source scope: the density-separated quotient in v13 `prop:takabayasi`
and `eq:takabayasi_polar`. Frame and source relations are independently
defined as equality or the actual simultaneous two-pi angle shift and
Clifford negative identity. Their equivalence laws use the proved literal
involutions. Both quotient spaces carry the standard coinduced quotient
topologies; neither relation nor topology is defined by spinor equality.

The exact Pauli product homeomorphisms intertwine these relations and
induce homeomorphisms to the existing matrix sign quotients. Density is
split off directly by a continuous open bijection on the actual quotient,
using only the explicit source relation. The actual regular realization
then yields homeomorphisms from the source quotient and density-times-
frame quotient to all strictly regular spinors. No manifold atlas or
global individual representative is selected here; smooth quotient and
geometric spacetime-bundle statements require their separate bridges.
-/

@[expose] public section
noncomputable section
open scoped Matrix.Norms.Operator
open Set Topology
namespace FoliationQM.CliffordSpinPolarQuotient
open CliffordSpinPolarDatum CliffordSpinPolarRealization PolarAmplitudeTopology

/-- The independently specified Clifford frame relation identifies equality or the literal two-pi angle and negative-identity action. -/
def FrameRelated (p q : FrameDatum) : Prop := p = q ∨ p = frameShift q

/-- The actual frame sign relation is an equivalence because the genuine frame sign is an involution. -/
theorem frameRelated_equivalence : Equivalence FrameRelated := by
  refine ⟨fun p => Or.inl rfl, ?_, ?_⟩
  · intro p q h
    rcases h with h | h
    · exact Or.inl h.symm
    · exact Or.inr (by rw [h, frameShift_involutive])
  · intro p q r h k
    rcases h with h | h <;> rcases k with k | k
    · exact Or.inl (h.trans k)
    · exact Or.inr (h.trans k)
    · exact Or.inr (h.trans (congrArg frameShift k))
    · exact Or.inl (by rw [h, k, frameShift_involutive])

/-- The actual Clifford frame setoid is the independently defined literal sign relation. -/
def frameSetoid : Setoid FrameDatum := ⟨FrameRelated, frameRelated_equivalence⟩

/-- The actual full-angle and Clifford Spin sign quotient with its standard quotient topology. -/
abbrev FrameQuotient := Quotient frameSetoid

/-- The independently specified Clifford source relation identifies equality or the literal density-preserving simultaneous sign. -/
def Related (d e : SourceDatum) : Prop := d = e ∨ d = shiftNeg e

/-- The actual source sign relation is an equivalence because the genuine source sign is an involution. -/
theorem related_equivalence : Equivalence Related := by
  refine ⟨fun d => Or.inl rfl, ?_, ?_⟩
  · intro d e h
    rcases h with h | h
    · exact Or.inl h.symm
    · exact Or.inr (by rw [h, shiftNeg_involutive])
  · intro d e f h k
    rcases h with h | h <;> rcases k with k | k
    · exact Or.inl (h.trans k)
    · exact Or.inr (h.trans k)
    · exact Or.inr (h.trans (congrArg shiftNeg k))
    · exact Or.inl (by rw [h, k, shiftNeg_involutive])

/-- The actual Clifford source setoid is the independently defined literal source sign relation. -/
def sourceSetoid : Setoid SourceDatum := ⟨Related, related_equivalence⟩

/-- The actual positive-density, full-angle, and Clifford Spin sign quotient with its standard quotient topology. -/
abbrev SourceQuotient := Quotient sourceSetoid

/-- Actual frame coordinate identification intertwines the independently defined Clifford and matrix sign relations in both directions. -/
theorem frameRelated_iff_matrix (p q : FrameDatum) :
    FrameRelated p q ↔ SourcePolarProductQuotient.FrameRelated
      (frameHomeomorph p) (frameHomeomorph q) := by
  change (p = q ∨ p = frameShift q) ↔
    (frameHomeomorph p = frameHomeomorph q ∨
      frameHomeomorph p = SourcePolarProductQuotient.frameShift (frameHomeomorph q))
  rw [← frameHomeomorph_frameShift]
  exact (or_congr frameHomeomorph.injective.eq_iff frameHomeomorph.injective.eq_iff).symm

/-- Actual source coordinate identification intertwines the independently defined Clifford and matrix source sign relations in both directions. -/
theorem related_iff_matrix (d e : SourceDatum) :
    Related d e ↔ SourcePolarQuotient.Related (sourceHomeomorph d) (sourceHomeomorph e) := by
  change (d = e ∨ d = shiftNeg e) ↔
    (sourceHomeomorph d = sourceHomeomorph e ∨
      sourceHomeomorph d = SourcePolarDatum.shiftNeg (sourceHomeomorph e))
  rw [← sourceHomeomorph_shiftNeg]
  exact (or_congr sourceHomeomorph.injective.eq_iff sourceHomeomorph.injective.eq_iff).symm

/-- The natural Clifford frame quotient is homeomorphic to the existing natural matrix frame quotient through the actual Pauli map. -/
def frameQuotientHomeomorph : FrameQuotient ≃ₜ SourcePolarProductQuotient.FrameQuotient :=
  Homeomorph.Quotient.congr frameHomeomorph frameRelated_iff_matrix

/-- The natural Clifford source quotient is homeomorphic to the existing natural matrix source quotient through the actual Pauli map. -/
def sourceQuotientHomeomorph : SourceQuotient ≃ₜ SourcePolarQuotient.SourceQuotient :=
  Homeomorph.Quotient.congr sourceHomeomorph related_iff_matrix

/-- The frame quotient homeomorphism sends the actual Clifford representative to the class of its exact Pauli frame. -/
theorem frameQuotientHomeomorph_mk (p : FrameDatum) :
    frameQuotientHomeomorph (Quotient.mk frameSetoid p) =
      Quotient.mk SourcePolarProductQuotient.frameSetoid (frameHomeomorph p) := rfl

/-- The inverse frame quotient homeomorphism sends a matrix representative to the class of its actual Clifford inverse coordinates. -/
theorem frameQuotientHomeomorph_symm_mk (p : SourcePolarProductQuotient.FrameDatum) :
    frameQuotientHomeomorph.symm (Quotient.mk SourcePolarProductQuotient.frameSetoid p) =
      Quotient.mk frameSetoid (frameHomeomorph.symm p) := rfl

/-- The source quotient homeomorphism sends the actual Clifford representative to the class of its exact Pauli source coordinates. -/
theorem sourceQuotientHomeomorph_mk (d : SourceDatum) :
    sourceQuotientHomeomorph (Quotient.mk sourceSetoid d) =
      Quotient.mk SourcePolarQuotient.signSetoid (sourceHomeomorph d) := rfl

/-- The inverse source quotient homeomorphism sends a matrix representative to the class of its actual Clifford inverse coordinates. -/
theorem sourceQuotientHomeomorph_symm_mk (d : SourcePolarDatum.SourceDatum) :
    sourceQuotientHomeomorph.symm (Quotient.mk SourcePolarQuotient.signSetoid d) =
      Quotient.mk sourceSetoid (sourceHomeomorph.symm d) := rfl

/-- Two actual frame representatives have the same quotient class exactly under the independently specified Clifford sign relation. -/
theorem frame_mk_eq_iff (p q : FrameDatum) :
    Quotient.mk frameSetoid p = Quotient.mk frameSetoid q ↔ FrameRelated p q := Quotient.eq''

/-- The actual Clifford frame sign preserves its quotient class. -/
theorem frame_mk_shift (p : FrameDatum) :
    Quotient.mk frameSetoid (frameShift p) = Quotient.mk frameSetoid p := Quotient.sound (Or.inr rfl)

/-- Two actual source representatives have the same quotient class exactly under the independently specified Clifford source sign relation. -/
theorem source_mk_eq_iff (d e : SourceDatum) :
    Quotient.mk sourceSetoid d = Quotient.mk sourceSetoid e ↔ Related d e := Quotient.eq''

/-- The actual Clifford source sign preserves its quotient class. -/
theorem source_mk_shift (d : SourceDatum) :
    Quotient.mk sourceSetoid (shiftNeg d) = Quotient.mk sourceSetoid d := Quotient.sound (Or.inr rfl)

/-- The actual frame projection is continuous for the standard quotient topology. -/
theorem frame_mk_continuous :
    Continuous (Quotient.mk frameSetoid : FrameDatum → FrameQuotient) := continuous_quotient_mk'

/-- The actual frame projection is a quotient map for the standard coinduced topology. -/
theorem frame_mk_isQuotientMap :
    IsQuotientMap (Quotient.mk frameSetoid : FrameDatum → FrameQuotient) :=
  isQuotientMap_quotient_mk'

/-- The actual source projection is continuous for the standard quotient topology. -/
theorem source_mk_continuous :
    Continuous (Quotient.mk sourceSetoid : SourceDatum → SourceQuotient) := continuous_quotient_mk'

/-- The actual source projection is a quotient map for the standard coinduced topology. -/
theorem source_mk_isQuotientMap :
    IsQuotientMap (Quotient.mk sourceSetoid : SourceDatum → SourceQuotient) :=
  isQuotientMap_quotient_mk'

/-- The exact Clifford frame saturation is the original set together with its actual sign inverse image. -/
theorem frame_saturation (s : Set FrameDatum) :
    (Quotient.mk frameSetoid : FrameDatum → FrameQuotient) ⁻¹'
      ((Quotient.mk frameSetoid : FrameDatum → FrameQuotient) '' s) = s ∪ frameShift ⁻¹' s := by
  ext p
  constructor
  · rintro ⟨q, hq, heq⟩
    rcases (frame_mk_eq_iff q p).mp heq with h | h
    · exact Or.inl (h ▸ hq)
    · exact Or.inr (show frameShift p ∈ s from h ▸ hq)
  · rintro (hp | hp)
    · exact ⟨p, hp, rfl⟩
    · exact ⟨frameShift p, hp, frame_mk_shift p⟩

/-- The actual Clifford frame quotient projection is open by the explicit free-sign saturation and continuity of the sign diffeomorphism. -/
theorem frame_mk_isOpenMap :
    IsOpenMap (Quotient.mk frameSetoid : FrameDatum → FrameQuotient) := by
  intro s hs
  apply frame_mk_isQuotientMap.isOpen_preimage.mp
  rw [frame_saturation]
  exact hs.union (hs.preimage (contMDiff_frameShift 0).continuous)

/-- The exact Clifford source saturation is the original set together with its actual density-preserving sign inverse image. -/
theorem source_saturation (s : Set SourceDatum) :
    (Quotient.mk sourceSetoid : SourceDatum → SourceQuotient) ⁻¹'
      ((Quotient.mk sourceSetoid : SourceDatum → SourceQuotient) '' s) = s ∪ shiftNeg ⁻¹' s := by
  ext d
  constructor
  · rintro ⟨e, he, heq⟩
    rcases (source_mk_eq_iff e d).mp heq with h | h
    · exact Or.inl (h ▸ he)
    · exact Or.inr (show shiftNeg d ∈ s from h ▸ he)
  · rintro (hd | hd)
    · exact ⟨d, hd, rfl⟩
    · exact ⟨shiftNeg d, hd, source_mk_shift d⟩

/-- The actual Clifford source quotient projection is open by the explicit sign saturation and continuity of its literal smooth sign. -/
theorem source_mk_isOpenMap :
    IsOpenMap (Quotient.mk sourceSetoid : SourceDatum → SourceQuotient) := by
  intro s hs
  apply source_mk_isQuotientMap.isOpen_preimage.mp
  rw [source_saturation]
  exact hs.union (hs.preimage (contMDiff_shiftNeg 0).continuous)

/-- Split the actual density and actual Clifford frame class directly, independently of any matrix or spinor realization. -/
def splitCoordinates (d : SourceDatum) : PositiveDensity × FrameQuotient :=
  (d.1, Quotient.mk frameSetoid d.2)

/-- The exact direct density and frame-class fibers are the independently specified Clifford source sign relation. -/
theorem splitCoordinates_eq_iff (d e : SourceDatum) :
    splitCoordinates d = splitCoordinates e ↔ Related d e := by
  rcases d with ⟨rho, p⟩
  rcases e with ⟨sigma, q⟩
  change (rho, Quotient.mk frameSetoid p) = (sigma, Quotient.mk frameSetoid q) ↔ _
  rw [Prod.mk.injEq, frame_mk_eq_iff]
  change (rho = sigma ∧ (p = q ∨ p = frameShift q)) ↔
    ((rho, p) = (sigma, q) ∨ (rho, p) = (sigma, frameShift q))
  simp only [Prod.ext_iff]
  tauto

/-- Direct density and Clifford frame-class projection is continuous in the existing natural topologies. -/
theorem continuous_splitCoordinates : Continuous splitCoordinates :=
  continuous_fst.prodMk (continuous_quotient_mk'.comp continuous_snd)

/-- Direct density and Clifford frame-class projection is open as a product of actual open maps. -/
theorem splitCoordinates_isOpenMap : IsOpenMap splitCoordinates :=
  IsOpenMap.id.prodMap frame_mk_isOpenMap

/-- The exact independent relation makes direct density separation well-defined on the actual source quotient. -/
def splitQuotient : SourceQuotient → PositiveDensity × FrameQuotient :=
  Quotient.lift splitCoordinates (fun d e h => (splitCoordinates_eq_iff d e).mpr h)

/-- Actual quotient density separation retains the original density and actual Clifford frame class. -/
theorem splitQuotient_mk (d : SourceDatum) :
    splitQuotient (Quotient.mk sourceSetoid d) = splitCoordinates d := rfl

/-- Direct density separation is continuous for the standard source quotient topology. -/
theorem continuous_splitQuotient : Continuous splitQuotient :=
  continuous_splitCoordinates.quotient_lift _

/-- The original positive density and actual Clifford frame class determine a unique source sign class. -/
theorem splitQuotient_injective : Function.Injective splitQuotient := by
  intro p q
  induction p using Quotient.inductionOn with | h d =>
    induction q using Quotient.inductionOn with | h e =>
      intro h
      exact Quotient.sound ((splitCoordinates_eq_iff d e).mp h)

/-- Every positive density and actual Clifford frame class have an actual source sign class. -/
theorem splitQuotient_surjective : Function.Surjective splitQuotient := by
  rintro ⟨rho, p⟩
  induction p using Quotient.inductionOn with | h p =>
    exact ⟨Quotient.mk sourceSetoid (rho, p), rfl⟩

/-- Direct density separation is open because its composite with the standard source projection is the actual open product projection. -/
theorem splitQuotient_isOpenMap : IsOpenMap splitQuotient :=
  .of_comp continuous_quotient_mk' Quotient.mk_surjective splitCoordinates_isOpenMap

/-- The standard actual source quotient is homeomorphic to positive density times the standard actual Clifford frame quotient through direct density separation. -/
def densityProductHomeomorph : SourceQuotient ≃ₜ PositiveDensity × FrameQuotient :=
  (Equiv.ofBijective splitQuotient ⟨splitQuotient_injective, splitQuotient_surjective⟩).toHomeomorphOfContinuousOpen
    continuous_splitQuotient splitQuotient_isOpenMap

/-- Direct density splitting sends each actual source class to its unchanged density and actual Clifford frame class. -/
theorem densityProductHomeomorph_mk (d : SourceDatum) :
    densityProductHomeomorph (Quotient.mk sourceSetoid d) =
      (d.1, Quotient.mk frameSetoid d.2) := rfl

/-- The literal Clifford source sign quotient with its standard topology is homeomorphic to the entire strict regular-spinor subtype through actual realization. -/
def regularHomeomorph : SourceQuotient ≃ₜ PolarSignQuotient.RegularSpinor :=
  sourceQuotientHomeomorph.trans SourcePolarQuotient.regularHomeomorph

/-- The actual source-quotient homeomorphism realizes each genuine Clifford source representative by the proved physical polar expression. -/
theorem regularHomeomorph_mk (d : SourceDatum) :
    regularHomeomorph (Quotient.mk sourceSetoid d) = realizeSource d := rfl

/-- Literal density times the natural Clifford frame quotient is homeomorphic to all strict regular spinors through direct density splitting and actual realization. -/
def productRegularHomeomorph : PositiveDensity × FrameQuotient ≃ₜ PolarSignQuotient.RegularSpinor :=
  densityProductHomeomorph.symm.trans regularHomeomorph

/-- The density-times-Clifford-frame realization evaluates on each frame representative to the exact actual Clifford source realization. -/
theorem productRegularHomeomorph_mk (rho : PositiveDensity) (p : FrameDatum) :
    productRegularHomeomorph (rho, Quotient.mk frameSetoid p) = realizeSource (rho, p) := by
  change regularHomeomorph (densityProductHomeomorph.symm (rho, Quotient.mk frameSetoid p)) = _
  rw [← densityProductHomeomorph_mk (rho, p), densityProductHomeomorph.symm_apply_apply,
    regularHomeomorph_mk]

/-- Actual bilinear invariant density of the genuine Clifford quotient realization is exactly its unchanged positive density coordinate. -/
theorem density_productRegularHomeomorph (p : PositiveDensity × FrameQuotient) :
    SpinorRegularity.invariantDensity (productRegularHomeomorph p).val = (p.1 : ℝ) := by
  rcases p with ⟨rho, p⟩
  induction p using Quotient.inductionOn with | h p =>
    rw [productRegularHomeomorph_mk]
    exact density_realizeSource (rho, p)

/-- The inverse genuine Clifford quotient realization recovers exactly the regular spinor's scalar-pseudoscalar invariant density. -/
theorem productRegularHomeomorph_symm_density (q : PolarSignQuotient.RegularSpinor) :
    ((productRegularHomeomorph.symm q).1 : ℝ) = SpinorRegularity.invariantDensity q.val := by
  rw [← density_productRegularHomeomorph (productRegularHomeomorph.symm q),
    productRegularHomeomorph.apply_symm_apply]

end FoliationQM.CliffordSpinPolarQuotient
