module
public import FoliationQM.LorentzAtlasHomeomorphism
public import FoliationQM.ParacompactObstructionPullback

/-!
# Comparing the native class across actual Cartesian Lorentz bundles

For the geometric frame component of v13 `prop:takabayasi`, identify a
given total space equivariantly over the new base with the fiber product
of a continuous map. Its native obstruction is the pullback of the
original class. A continuous section therefore detects vanishing even
when the total space is given in different principal charts.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.ParacompactCartesianObstruction
open LorentzMatrixGroup ParacompactBundleObstruction
open GeometricPrincipalPullback ModTwoGlobalPullback

variable {X B T U ι κ : Type*} [TopologicalSpace X] [TopologicalSpace B]
  [TopologicalSpace T] [TopologicalSpace U] [LocallyPathConnectedSpace B]
  [ParacompactSpace B] [NormalSpace B] {proj : T → B}
  (A : GeometricPrincipalAtlas.Data (G := ProperFutureLorentz) proj ι)

/-- Independently charted equivariantly homeomorphic bundles over the same base
determine the same class. Neither atlas requires a supplied path presentation. -/
theorem eq_of_homeomorph {q : U → B} (C : GeometricPrincipalAtlas.Data (G := ProperFutureLorentz) q κ)
    (e : U ≃ₜ T) (hq : ∀ u, q u = proj (e u))
    (he : ∀ u g, e (C.right u g) = A.right (e u) g) :
    obstruction C = obstruction A :=
  LorentzAtlasHomeomorphism.obstruction_eq (ParacompactLorentzPresentation.hasPresentation C)
    (ParacompactLorentzPresentation.hasPresentation A) e hq he

variable [LocallyPathConnectedSpace X] {q : U → X}
  (C : GeometricPrincipalAtlas.Data (G := ProperFutureLorentz) q κ)
  (f : C(X, B)) (e : U ≃ₜ Total f proj) (hq : ∀ u, q u = projection f proj (e u))
  (he : ∀ u g, e (C.right u g) = (atlas f A).right (e u) g)

include A C f e hq he

omit [LocallyPathConnectedSpace B] [LocallyPathConnectedSpace X] in
/-- The given total space inherits a presentation from the geometric fiber product. -/
theorem hasPresentation : PresentedLorentzBundle.HasPresentation q C.right :=
  (LorentzAtlasHomeomorphism.hasPresentation_iff e hq he).mpr
    (PresentedBundlePullback.hasPresentation f (ParacompactLorentzPresentation.hasPresentation A))

/-- The inherited presentation computes the pullback class on any locally path connected new base. -/
theorem inherited :
    PresentedLorentzBundle.obstruction (hasPresentation A C f e hq he) = pull f (obstruction A) :=
  (LorentzAtlasHomeomorphism.obstruction_eq (hasPresentation A C f e hq he)
    (PresentedBundlePullback.hasPresentation f (ParacompactLorentzPresentation.hasPresentation A))
    e hq he).trans (ParacompactObstructionPullback.inherited_natural A f)

variable [ParacompactSpace X] [NormalSpace X]

/-- The native class computed from the new atlas alone is the pullback of the original class. -/
theorem natural : obstruction C = pull f (obstruction A) :=
  (eq_presented C (hasPresentation A C f e hq he)).trans (inherited A C f e hq he)

/-- A continuous section of the base map recovers the original class from the new atlas. -/
theorem section_recovery (s : C(B, X)) (hs : Function.RightInverse s f) :
    pull s (obstruction C) = obstruction A := by
  rw [natural A C f e hq he]
  exact ParacompactObstructionPullback.section_pull f s hs _

/-- For a split base map the class of the given total space vanishes exactly when the original class does. -/
theorem zero_iff_of_section (s : C(B, X)) (hs : Function.RightInverse s f) :
    obstruction C = 0 ↔ obstruction A = 0 := by
  constructor
  · intro hz
    rw [← section_recovery A C f e hq he s hs, hz, map_zero]
  · intro hz
    rw [natural A C f e hq he, hz, map_zero]

end FoliationQM.ParacompactCartesianObstruction
