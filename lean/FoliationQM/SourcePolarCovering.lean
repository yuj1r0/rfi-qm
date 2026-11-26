module
public import FoliationQM.PolarSignCovering
public import FoliationQM.SourcePolarProductQuotient

/-!
# Actual two-sheet coverings in the literal source polar coordinates

Sources: v13 `prop:takabayasi` and its simultaneous two-pi/matrix-sign
identification. The actual amplitude-datum sign covering is transferred
through the proved natural coordinate and quotient homeomorphisms. This
gives genuine covering maps for source realization, source quotient
projection, and the separated density/angle-matrix quotient projection.
Restricting the latter to a fixed positive density and using actual slice
homeomorphisms also proves the angle-matrix projection is a covering.

The source realization and quotient fibers are explicitly equivalent to
Fin 2; the covering neighborhoods have that actual discrete two-point
fiber. A local inverse can be chosen through any requested source datum,
and realizes each nearby spinor exactly. These are concrete polar sign
coverings, without a global representative or an identification with the
abstract Spin-to-Lorentz covering.
-/

@[expose] public section
noncomputable section
open scoped Matrix.Norms.Operator
open Topology
namespace FoliationQM.SourcePolarCovering
open PolarSignQuotient SourcePolarDatum SourcePolarRealization SourcePolarProductQuotient

/-- Actual realization from the natural literal source coordinates to regular spinors is a genuine covering map. -/
theorem realizeSource_isCoveringMap : IsCoveringMap realizeSource :=
  PolarSignCovering.realize_isCoveringMap.comp_homeomorph datumHomeomorph

/-- The literal source sign-quotient projection with its standard quotient topology is a genuine covering map. -/
theorem quotient_mk_isCoveringMap :
    IsCoveringMap (Quotient.mk SourcePolarQuotient.signSetoid : SourceDatum →
      SourcePolarQuotient.SourceQuotient) := by
  have he : SourcePolarQuotient.regularHomeomorph.symm ∘ realizeSource =
      (Quotient.mk SourcePolarQuotient.signSetoid : SourceDatum →
        SourcePolarQuotient.SourceQuotient) := by
    funext d
    change SourcePolarQuotient.regularHomeomorph.symm (realize (toDatum d)) = _
    rw [← SourcePolarQuotient.regularHomeomorph_apply_mk,
      SourcePolarQuotient.regularHomeomorph.symm_apply_apply]
  rw [← he]
  exact realizeSource_isCoveringMap.homeomorph_comp
    SourcePolarQuotient.regularHomeomorph.symm

/-- Separating unchanged positive density from the angle-matrix sign class gives an actual covering map. -/
theorem splitCoordinates_isCoveringMap : IsCoveringMap splitCoordinates :=
  quotient_mk_isCoveringMap.homeomorph_comp densityProductHomeomorph

/-- The angle-matrix sign projection is an actual covering, derived by fixing positive density and identifying the true pullback slices. -/
theorem frame_mk_isCoveringMap :
    IsCoveringMap (Quotient.mk frameSetoid : FrameDatum → FrameQuotient) := by
  let rho0 : PolarAmplitudeTopology.PositiveDensity := ⟨1, by norm_num⟩
  let S : Set (PolarAmplitudeTopology.PositiveDensity × FrameQuotient) :=
    {z | z.1 = rho0}
  let hin : FrameDatum ≃ₜ splitCoordinates ⁻¹' S :=
    { toFun := fun p => ⟨(rho0, p), rfl⟩
      invFun := fun d => d.val.2
      left_inv := fun _ => rfl
      right_inv := by
        rintro ⟨⟨rho, p⟩, h⟩
        apply Subtype.ext
        change (rho0, p) = (rho, p)
        change rho = rho0 at h
        rw [h]
      continuous_toFun := (continuous_const.prodMk continuous_id).subtype_mk _
      continuous_invFun := continuous_snd.comp continuous_subtype_val }
  let hout : S ≃ₜ FrameQuotient :=
    { toFun := fun p => p.val.2
      invFun := fun q => ⟨(rho0, q), rfl⟩
      left_inv := by
        rintro ⟨⟨rho, q⟩, h⟩
        apply Subtype.ext
        change (rho0, q) = (rho, q)
        change rho = rho0 at h
        rw [h]
      right_inv := fun _ => rfl
      continuous_toFun := continuous_snd.comp continuous_subtype_val
      continuous_invFun := (continuous_const.prodMk continuous_id).subtype_mk _ }
  exact ((splitCoordinates_isCoveringMap.restrictPreimage S).comp_homeomorph hin).homeomorph_comp hout

/-- The actual source realization is a local homeomorphism at every source datum. -/
theorem realizeSource_isLocalHomeomorph : IsLocalHomeomorph realizeSource :=
  realizeSource_isCoveringMap.isLocalHomeomorph

/-- The actual source sign projection is a local homeomorphism in the natural source and quotient topologies. -/
theorem quotient_mk_isLocalHomeomorph :
    IsLocalHomeomorph (Quotient.mk SourcePolarQuotient.signSetoid : SourceDatum →
      SourcePolarQuotient.SourceQuotient) := quotient_mk_isCoveringMap.isLocalHomeomorph

/-- The actual source-coordinate homeomorphism identifies each source realization fiber with the corresponding amplitude-datum fiber. -/
def realizeFiberHomeomorph (q : RegularSpinor) :
    (realizeSource ⁻¹' {q}) ≃ₜ (realize ⁻¹' {q}) :=
  datumHomeomorph.subtype (fun _ => Iff.rfl)

/-- Each source realization fiber is explicitly equivalent to the two-element type through its genuine datum fiber. -/
def realizeFiberEquiv (q : RegularSpinor) : (realizeSource ⁻¹' {q}) ≃ Fin 2 :=
  (realizeFiberHomeomorph q).toEquiv.trans (PolarSignCovering.realizeFiberEquiv q)

/-- Every regular spinor has exactly two literal source-coordinate representatives. -/
theorem realize_fiber_card (q : RegularSpinor) : Nat.card (realizeSource ⁻¹' {q}) = 2 := by
  simpa using Nat.card_congr (realizeFiberEquiv q)

/-- Every regular spinor has an actual evenly covered neighborhood for source realization with discrete fiber Fin 2. -/
theorem realizeSource_isEvenlyCovered_two (q : RegularSpinor) :
    IsEvenlyCovered realizeSource q (Fin 2) := by
  let := (realizeSource_isCoveringMap q).discreteTopology_fiber
  exact (realizeSource_isCoveringMap q).of_fiber_homeomorph
    (realizeFiberEquiv q).toHomeomorphOfDiscrete

/-- Every source sign-quotient fiber is explicitly equivalent to Fin 2 through the actual regular-spinor homeomorphism. -/
def quotientFiberEquiv (q : SourcePolarQuotient.SourceQuotient) :
    ((Quotient.mk SourcePolarQuotient.signSetoid : SourceDatum →
      SourcePolarQuotient.SourceQuotient) ⁻¹' {q}) ≃ Fin 2 :=
  (Equiv.subtypeEquivRight (fun d => show
    Quotient.mk SourcePolarQuotient.signSetoid d = q ↔
      realizeSource d = SourcePolarQuotient.regularHomeomorph q from
    SourcePolarQuotient.regularHomeomorph.injective.eq_iff.symm)).trans
      (realizeFiberEquiv (SourcePolarQuotient.regularHomeomorph q))

/-- Every actual source sign class has exactly two source-coordinate representatives. -/
theorem quotient_fiber_card (q : SourcePolarQuotient.SourceQuotient) :
    Nat.card ((Quotient.mk SourcePolarQuotient.signSetoid : SourceDatum →
      SourcePolarQuotient.SourceQuotient) ⁻¹' {q}) = 2 := by
  simpa using Nat.card_congr (quotientFiberEquiv q)

/-- Every actual source sign class has an evenly covered neighborhood with the genuine discrete two-point fiber. -/
theorem quotient_mk_isEvenlyCovered_two (q : SourcePolarQuotient.SourceQuotient) :
    IsEvenlyCovered (Quotient.mk SourcePolarQuotient.signSetoid : SourceDatum →
      SourcePolarQuotient.SourceQuotient) q (Fin 2) := by
  let := (quotient_mk_isCoveringMap q).discreteTopology_fiber
  exact (quotient_mk_isCoveringMap q).of_fiber_homeomorph
    (quotientFiberEquiv q).toHomeomorphOfDiscrete

/-- Every separated positive-density and angle-matrix sign class has an actual two-sheeted evenly covered neighborhood. -/
theorem splitCoordinates_isEvenlyCovered_two
    (p : PolarAmplitudeTopology.PositiveDensity × FrameQuotient) :
    IsEvenlyCovered splitCoordinates p (Fin 2) := by
  change IsEvenlyCovered (densityProductHomeomorph ∘
    (Quotient.mk SourcePolarQuotient.signSetoid : SourceDatum →
      SourcePolarQuotient.SourceQuotient)) p (Fin 2)
  simpa only [Homeomorph.apply_symm_apply] using
    (quotient_mk_isEvenlyCovered_two (densityProductHomeomorph.symm p)).homeomorph_comp
      densityProductHomeomorph

/-- An actual local inverse to source realization chosen through a prescribed source datum. -/
def localInverseAt (d : SourceDatum) : OpenPartialHomeomorph RegularSpinor SourceDatum :=
  realizeSource_isLocalHomeomorph.localInverseAt d

/-- The spinor realized by the prescribed datum belongs to the open domain of its chosen local inverse. -/
theorem realize_mem_localInverseAt_source (d : SourceDatum) :
    realizeSource d ∈ (localInverseAt d).source :=
  realizeSource_isLocalHomeomorph.apply_self_mem_localInverseAt_source

/-- The chosen local inverse returns the prescribed source representative at its realized spinor. -/
theorem localInverseAt_realize (d : SourceDatum) : localInverseAt d (realizeSource d) = d :=
  realizeSource_isLocalHomeomorph.localInverseAt_apply_self

/-- Realization of the actual local inverse returns every spinor in its open domain. -/
theorem realize_localInverseAt {d : SourceDatum} {q : RegularSpinor}
    (hq : q ∈ (localInverseAt d).source) : realizeSource (localInverseAt d q) = q :=
  realizeSource_isLocalHomeomorph.apply_localInverseAt_of_mem hq

/-- Every prescribed source representative extends to a continuous local representative of all nearby actual regular spinors. -/
theorem exists_local_lift_through (d : SourceDatum) :
    ∃ U : Set RegularSpinor, ∃ s : RegularSpinor → SourceDatum,
      IsOpen U ∧ realizeSource d ∈ U ∧ ContinuousOn s U ∧
        s (realizeSource d) = d ∧ ∀ q ∈ U, realizeSource (s q) = q := by
  refine ⟨(localInverseAt d).source, localInverseAt d, (localInverseAt d).open_source,
    realize_mem_localInverseAt_source d, (localInverseAt d).continuousOn_toFun,
    localInverseAt_realize d, ?_⟩
  intro q hq
  exact realize_localInverseAt hq

end FoliationQM.SourcePolarCovering
