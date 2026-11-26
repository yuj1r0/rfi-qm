module
public import FoliationQM.SourcePolarCovering

/-!
# The actual two-sheeted angle-matrix quotient

Source: the separated positive-density presentation in v13
`prop:takabayasi`. The existing angle-matrix sign projection already has
a covering proof from actual fixed-density pullback slices. This module
retains that map and the natural quotient topology, and supplies a named
local-homeomorphism interface, exact two-element fibers, and genuine
two-sheeted evenly covered neighborhoods.

For every fixed positive density, the actual frame fiber is naturally
homeomorphic to the corresponding full source-quotient fiber. This
identifies its two points without assigning a new equivalence relation.
The natural quotient is Hausdorff and second-countable through its
fixed-density embedding into the already proved density-product
homeomorphism. No smooth quotient structure or abstract Spin covering
is assumed in these topological statements.
-/

@[expose] public section
noncomputable section
open scoped Matrix.Norms.Operator
open Set Topology
namespace FoliationQM.FrameQuotientCovering
open PolarAmplitudeTopology SourcePolarDatum SourcePolarProductQuotient

/-- The natural angle-matrix sign quotient is Hausdorff through its fixed-density embedding into the existing regular-spinor product homeomorphism. -/
instance instT2SpaceFrameQuotient : T2Space FrameQuotient := by
  let : T2Space (PositiveDensity × FrameQuotient) :=
    productRegularHomeomorph.isEmbedding.t2Space
  exact (isEmbedding_prodMkRight (⟨1, by norm_num⟩ : PositiveDensity)).t2Space

/-- The natural angle-matrix sign quotient is second-countable through the same actual fixed-density embedding. -/
instance instSecondCountableTopologyFrameQuotient : SecondCountableTopology FrameQuotient := by
  let : SecondCountableTopology (PositiveDensity × FrameQuotient) :=
    productRegularHomeomorph.secondCountableTopology
  exact (isEmbedding_prodMkRight (⟨1, by norm_num⟩ : PositiveDensity)).secondCountableTopology

/-- The existing angle-matrix sign projection is a genuine covering for its unchanged natural quotient topology. -/
theorem frame_mk_isCoveringMap :
    IsCoveringMap (Quotient.mk frameSetoid : FrameDatum → FrameQuotient) :=
  SourcePolarCovering.frame_mk_isCoveringMap

/-- The actual angle-matrix sign projection is a local homeomorphism in the existing natural topologies. -/
theorem frame_mk_isLocalHomeomorph :
    IsLocalHomeomorph (Quotient.mk frameSetoid : FrameDatum → FrameQuotient) :=
  frame_mk_isCoveringMap.isLocalHomeomorph

private theorem fixed_density_of_source_fiber (rho : PositiveDensity) (q : FrameQuotient)
    {d : SourceDatum}
    (hd : Quotient.mk SourcePolarQuotient.signSetoid d =
      densityProductHomeomorph.symm (rho, q)) : d.1 = rho := by
  have h := congrArg (fun z => (densityProductHomeomorph z).1) hd
  simpa only [densityProductHomeomorph_mk, Homeomorph.apply_symm_apply] using h

private theorem frame_class_of_source_fiber (rho : PositiveDensity) (q : FrameQuotient)
    {d : SourceDatum}
    (hd : Quotient.mk SourcePolarQuotient.signSetoid d =
      densityProductHomeomorph.symm (rho, q)) : Quotient.mk frameSetoid d.2 = q := by
  have h := congrArg (fun z => (densityProductHomeomorph z).2) hd
  simpa only [densityProductHomeomorph_mk, Homeomorph.apply_symm_apply] using h

/-- At any fixed positive density, the actual frame-sign fiber is naturally homeomorphic to the corresponding full source-sign fiber. -/
def frameFiberHomeomorph (rho : PositiveDensity) (q : FrameQuotient) :
    ((Quotient.mk frameSetoid : FrameDatum → FrameQuotient) ⁻¹' {q}) ≃ₜ
      ((Quotient.mk SourcePolarQuotient.signSetoid : SourceDatum →
        SourcePolarQuotient.SourceQuotient) ⁻¹' {densityProductHomeomorph.symm (rho, q)}) where
  toFun p := ⟨(rho, p.val), by
    apply densityProductHomeomorph.injective
    rw [densityProductHomeomorph_mk, Homeomorph.apply_symm_apply]
    change (rho, Quotient.mk frameSetoid p.val) = (rho, q)
    rw [show Quotient.mk frameSetoid p.val = q from p.property]⟩
  invFun d := ⟨d.val.2, by exact frame_class_of_source_fiber rho q d.property⟩
  left_inv _ := rfl
  right_inv d := by
    apply Subtype.ext
    exact Prod.ext (fixed_density_of_source_fiber rho q d.property).symm rfl
  continuous_toFun :=
    (continuous_const.prodMk continuous_subtype_val).subtype_mk _
  continuous_invFun :=
    (continuous_snd.comp continuous_subtype_val).subtype_mk _

/-- The actual frame-fiber homeomorphism inserts exactly the supplied positive density and leaves the angle-matrix representative unchanged. -/
theorem frameFiberHomeomorph_val (rho : PositiveDensity) (q : FrameQuotient)
    (p : ((Quotient.mk frameSetoid : FrameDatum → FrameQuotient) ⁻¹' {q})) :
    (frameFiberHomeomorph rho q p).val = (rho, p.val) := rfl

/-- Every actual angle-matrix sign fiber is explicitly equivalent to Fin 2 through the proved full source fiber at density one. -/
def frameFiberEquiv (q : FrameQuotient) :
    ((Quotient.mk frameSetoid : FrameDatum → FrameQuotient) ⁻¹' {q}) ≃ Fin 2 :=
  (frameFiberHomeomorph ⟨1, by norm_num⟩ q).toEquiv.trans
    (SourcePolarCovering.quotientFiberEquiv _)

/-- Every actual angle-matrix sign quotient fiber contains exactly two points. -/
theorem frame_fiber_card (q : FrameQuotient) :
    Nat.card ((Quotient.mk frameSetoid : FrameDatum → FrameQuotient) ⁻¹' {q}) = 2 := by
  simpa using Nat.card_congr (frameFiberEquiv q)

/-- Every angle-matrix sign class has an actual evenly covered neighborhood with the genuine discrete two-point fiber. -/
theorem frame_mk_isEvenlyCovered_two (q : FrameQuotient) :
    IsEvenlyCovered (Quotient.mk frameSetoid : FrameDatum → FrameQuotient) q (Fin 2) := by
  let := (frame_mk_isCoveringMap q).discreteTopology_fiber
  exact (frame_mk_isCoveringMap q).of_fiber_homeomorph
    (frameFiberEquiv q).toHomeomorphOfDiscrete

/-- The actual fiber through an angle-matrix representative consists exactly of that representative and its literal simultaneous sign transform. -/
theorem frame_fiber_eq_pair (p : FrameDatum) :
    (Quotient.mk frameSetoid : FrameDatum → FrameQuotient) ⁻¹'
      {Quotient.mk frameSetoid p} = {p, frameShift p} := by
  ext q
  exact frame_mk_eq_iff q p

end FoliationQM.FrameQuotientCovering
