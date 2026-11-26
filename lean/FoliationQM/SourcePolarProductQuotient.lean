module
public import FoliationQM.SourcePolarQuotient
public import FoliationQM.SourcePolarRealization
/-!
# Positive density separated from the natural polar sign quotient

Source: v13 `prop:takabayasi` and its displayed positive-density product
with the chiral-angle/matrix sign quotient. The frame relation is defined
independently by equality or the literal two-pi shift and matrix negation.
The quotient carries its ordinary coinduced topology.

Splitting out density is a continuous open bijection, hence a genuine
homeomorphism. Composition with the proved actual realization identifies
this literal product with the entire strict regular-spinor domain and
recovers the source density as the invariant bilinear density. No global
representative, real angle, smooth bundle, or abstract spin classification
is inferred from these topological statements.
-/

@[expose] public section
noncomputable section
open scoped Matrix.Norms.Operator
open Topology
namespace FoliationQM.SourcePolarProductQuotient
open PolarAmplitudeTopology SourcePolarDatum
/-- The source four-pi angle and actual determinant-one matrix, with their natural product topology. -/
abbrev FrameDatum := ChiralAngleCircle.Angle × SpecialLinearMatrix
/-- The literal two-pi angle shift and matrix sign reversal, independent of positive density. -/
def frameShift (p : FrameDatum) : FrameDatum :=
  (shiftNeg ((⟨1, by norm_num⟩ : PositiveDensity), p)).2
/-- The source sign operation preserves density and acts only on the angle-matrix factor. -/
theorem shiftNeg_pair (rho : PositiveDensity) (p : FrameDatum) :
    shiftNeg (rho,p) = (rho, frameShift p) := rfl
/-- The actual angle-matrix sign operation is an involution. -/
theorem frameShift_involutive : Function.Involutive frameShift := by
  intro p
  exact congrArg Prod.snd (shiftNeg_involutive ((⟨1,by norm_num⟩ : PositiveDensity),p))
/-- The literal angle-matrix sign operation is continuous for the natural product topology. -/
theorem continuous_frameShift : Continuous frameShift :=
  continuous_snd.comp (continuous_shiftNeg.comp
    (continuous_const.prodMk continuous_id))
/-- The independent angle-matrix equivalence relation identifies equality and simultaneous sign transformation. -/
def FrameRelated (p q : FrameDatum) : Prop := p=q ∨ p=frameShift q
/-- The literal angle-matrix sign relation is reflexive, symmetric and transitive. -/
theorem frameRelated_equivalence : Equivalence FrameRelated := by
  refine ⟨fun p => Or.inl rfl, ?_, ?_⟩
  · intro p q h
    rcases h with h|h
    · exact Or.inl h.symm
    · exact Or.inr (by rw [h,frameShift_involutive])
  · intro p q r h k
    rcases h with h|h <;> rcases k with k|k
    · exact Or.inl (h.trans k)
    · exact Or.inr (h.trans k)
    · exact Or.inr (h.trans (congrArg frameShift k))
    · exact Or.inl (by rw [h,k,frameShift_involutive])
/-- The independently proved source angle-matrix sign setoid. -/
def frameSetoid : Setoid FrameDatum := ⟨FrameRelated,frameRelated_equivalence⟩
/-- The angle-matrix sign quotient with the standard quotient topology. -/
abbrev FrameQuotient := Quotient frameSetoid
/-- Two angle-matrix classes agree exactly under the independent literal sign relation. -/
theorem frame_mk_eq_iff (p q : FrameDatum) :
    Quotient.mk frameSetoid p = Quotient.mk frameSetoid q ↔ FrameRelated p q := Quotient.eq''
/-- The actual simultaneous angle-matrix sign operation preserves its quotient class. -/
theorem frame_mk_shift (p : FrameDatum) :
    Quotient.mk frameSetoid (frameShift p) = Quotient.mk frameSetoid p := Quotient.sound (Or.inr rfl)
/-- The exact angle-matrix quotient saturation is the union with its sign-transformed inverse image. -/
theorem frame_saturation (s : Set FrameDatum) :
    (Quotient.mk frameSetoid : FrameDatum → FrameQuotient) ⁻¹'
      ((Quotient.mk frameSetoid : FrameDatum → FrameQuotient) '' s) =
      s ∪ frameShift ⁻¹' s := by
  ext p
  constructor
  · rintro ⟨q,hq,heq⟩
    rcases (frame_mk_eq_iff q p).mp heq with h|h
    · exact Or.inl (h ▸ hq)
    · exact Or.inr (show frameShift p ∈ s from h ▸ hq)
  · rintro (hp|hp)
    · exact ⟨p,hp,rfl⟩
    · exact ⟨frameShift p,hp,frame_mk_shift p⟩
/-- The natural angle-matrix quotient projection is open by its explicit two-sign saturation. -/
theorem frame_mk_isOpenMap :
    IsOpenMap (Quotient.mk frameSetoid : FrameDatum → FrameQuotient) := by
  intro s hs
  apply (show IsQuotientMap (Quotient.mk frameSetoid : FrameDatum → FrameQuotient) from isQuotientMap_quotient_mk').isOpen_preimage.mp
  rw [frame_saturation]
  exact hs.union (hs.preimage continuous_frameShift)
/-- The actual product of the unchanged positive density and angle-matrix sign class. -/
def splitCoordinates (d : SourceDatum) : PositiveDensity × FrameQuotient :=
  (d.1,Quotient.mk frameSetoid d.2)
/-- Equality after separating density is exactly the independently defined full source sign relation. -/
theorem splitCoordinates_eq_iff (d e : SourceDatum) :
    splitCoordinates d = splitCoordinates e ↔ SourcePolarQuotient.Related d e := by
  rcases d with ⟨rho,p⟩
  rcases e with ⟨sigma,q⟩
  change (rho,Quotient.mk frameSetoid p)=(sigma,Quotient.mk frameSetoid q) ↔ _
  rw [Prod.mk.injEq,frame_mk_eq_iff]
  change (rho=sigma ∧ (p=q ∨ p=frameShift q)) ↔
    (rho,p)=(sigma,q) ∨ (rho,p)=shiftNeg (sigma,q)
  rw [shiftNeg_pair]
  simp only [Prod.ext_iff]
  tauto
/-- Density and angle-matrix quotient projection are jointly continuous in the natural topologies. -/
theorem continuous_splitCoordinates : Continuous splitCoordinates :=
  continuous_fst.prodMk (continuous_quotient_mk'.comp continuous_snd)
/-- The actual density and angle-matrix projection is open as a product of open maps. -/
theorem splitCoordinates_isOpenMap : IsOpenMap splitCoordinates :=
  IsOpenMap.id.prodMap frame_mk_isOpenMap
/-- Separate positive density from the full source sign quotient using the exact coordinate relation. -/
def splitQuotient : SourcePolarQuotient.SourceQuotient → PositiveDensity × FrameQuotient :=
  Quotient.lift splitCoordinates (fun d e h => (splitCoordinates_eq_iff d e).mpr h)
/-- Density splitting evaluates to the original density and angle-matrix quotient class. -/
theorem splitQuotient_mk (d : SourceDatum) :
    splitQuotient (Quotient.mk SourcePolarQuotient.signSetoid d) = splitCoordinates d := rfl
/-- The separated-density map is continuous from the existing natural source quotient. -/
theorem continuous_splitQuotient : Continuous splitQuotient :=
  continuous_splitCoordinates.quotient_lift _
/-- Separated density and angle-matrix class determine exactly one full source sign class. -/
theorem splitQuotient_injective : Function.Injective splitQuotient := by
  intro p q
  induction p using Quotient.inductionOn with | h d =>
    induction q using Quotient.inductionOn with | h e =>
      intro h
      exact Quotient.sound ((splitCoordinates_eq_iff d e).mp h)
/-- Every positive density and angle-matrix class comes from a full source sign class. -/
theorem splitQuotient_surjective : Function.Surjective splitQuotient := by
  rintro ⟨rho,p⟩
  induction p using Quotient.inductionOn with | h p =>
    exact ⟨Quotient.mk SourcePolarQuotient.signSetoid (rho,p),rfl⟩
/-- The separated-density map is open because its composite with the natural quotient projection is open. -/
theorem splitQuotient_isOpenMap : IsOpenMap splitQuotient :=
  .of_comp continuous_quotient_mk' Quotient.mk_surjective splitCoordinates_isOpenMap
/-- The natural full source sign quotient is homeomorphic to positive density times the natural angle-matrix sign quotient. -/
def densityProductHomeomorph :
    SourcePolarQuotient.SourceQuotient ≃ₜ PositiveDensity × FrameQuotient :=
  (Equiv.ofBijective splitQuotient ⟨splitQuotient_injective,splitQuotient_surjective⟩).toHomeomorphOfContinuousOpen
    continuous_splitQuotient splitQuotient_isOpenMap
/-- The density-product homeomorphism is exactly the specified density and angle-matrix projection. -/
theorem densityProductHomeomorph_mk (d : SourceDatum) :
    densityProductHomeomorph (Quotient.mk SourcePolarQuotient.signSetoid d) =
      (d.1,Quotient.mk frameSetoid d.2) := rfl
/-- The literal concrete source density times angle-matrix sign quotient is homeomorphic to all strict regular spinors. -/
def productRegularHomeomorph :
    PositiveDensity × FrameQuotient ≃ₜ PolarSignQuotient.RegularSpinor :=
  densityProductHomeomorph.symm.trans SourcePolarQuotient.regularHomeomorph
/-- The product homeomorphism realizes each representative by the actual source polar expression. -/
theorem productRegularHomeomorph_mk (rho : PositiveDensity) (p : FrameDatum) :
    productRegularHomeomorph (rho,Quotient.mk frameSetoid p) =
      SourcePolarRealization.realizeSource (rho,p) := by
  change SourcePolarQuotient.regularHomeomorph
    (densityProductHomeomorph.symm (rho,Quotient.mk frameSetoid p)) = _
  rw [← densityProductHomeomorph_mk (rho,p),densityProductHomeomorph.symm_apply_apply]
  rfl
/-- The actual bilinear invariant density of the product realization equals its unchanged positive-density coordinate. -/
theorem density_productRegularHomeomorph (p : PositiveDensity × FrameQuotient) :
    SpinorRegularity.invariantDensity (productRegularHomeomorph p).val = (p.1 : ℝ) := by
  rcases p with ⟨rho,p⟩
  induction p using Quotient.inductionOn with | h p =>
    rw [productRegularHomeomorph_mk]
    exact SourcePolarRealization.density_realizeSource (rho,p)
/-- The inverse product homeomorphism recovers exactly the actual regular-spinor invariant density. -/
theorem productRegularHomeomorph_symm_density (q : PolarSignQuotient.RegularSpinor) :
    ((productRegularHomeomorph.symm q).1 : ℝ) = SpinorRegularity.invariantDensity q.val := by
  rw [← density_productRegularHomeomorph (productRegularHomeomorph.symm q),
    productRegularHomeomorph.apply_symm_apply]
end FoliationQM.SourcePolarProductQuotient
