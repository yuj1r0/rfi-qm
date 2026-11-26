module
public import FoliationQM.AlignedSpinPresentation
public import FoliationQM.GlobalSpinDisplacement

/-!
# Computing global displacement from supplied adapted Spin charts

For the Spin-frame component of v13 `prop:takabayasi`, an aligned
point-indexed presentation can be used directly to measure two geometric
lifts. Intersect its domains with both independent adaptations and use
their identity physical isomorphisms to compare the resulting gauges.
-/

@[expose] public section
noncomputable section
open Set
namespace FoliationQM.GlobalSpinPresentationFormula
open CliffordSpinLorentzSmooth LorentzMatrixGroup GeometricSpinObstruction SpinLiftIsomorphism
open CliffordSpinCoverRefinement RefinedGeometricPrincipalAtlas JointSpinAdaptation
open SpinAllCoverHOne SpinSignHOne SpinLiftSignDifference AlignedSpinPresentation

universe u
variable {E H EP HP : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  [NormedAddCommGroup EP] [NormedSpace ℝ EP] [TopologicalSpace HP]
  {B : Type u} [TopologicalSpace B] [ChartedSpace H B] {I : ModelWithCorners ℝ E H}
  {P ι : Type*} [TopologicalSpace P] [ChartedSpace HP P] {KP : ModelWithCorners ℝ EP HP}
  {proj : P → B} {L : GeometricPrincipalAtlas.Data (G := ProperFutureLorentz) proj ι}
  {n : WithTop ℕ∞} (LM : GeometricPrincipalSmoothAtlas.Data I lorentzModel KP L n)

/-- The global relative class of two smooth lifts supplied on the same aligned, anchored
refinement is the image of their actual transition ratio on that refinement. -/
theorem relative_ofRefined (R : Refinement (domains L) B)
    (hp : ∀ i, R.parent i = targetChart L i) (hmem : ∀ i, i ∈ R.domain i)
    (A T : GeometricSpinStructure.Lift I (restrictedAtlas L R) n) :
    GlobalSpinDisplacement.relative LM (ofRefined LM R A) (ofRefined LM R T) =
      ofCover R.domain R.covers (classOf (difference
        (transitions (restrictedSmoothAtlas LM R) A) (transitions (restrictedSmoothAtlas LM R) T))) := by
  let a := ofRefined LM R A
  let t := ofRefined LM R T
  let W : SpinHOneDirected.Cover B :=
    ⟨fun i => R.domain i ⊓ (common LM a t).domain i, fun i => ⟨hmem i, mem_common LM a t i⟩⟩
  have hW (i) : W.domain i ≤ R.domain i := inf_le_left
  have ha (i) : (W.domain i : Set B) ⊆ neighborhood LM a i := fun _ hx => hx.2.1
  have ht (i) : (W.domain i : Set B) ⊆ neighborhood LM t i := fun _ hx => hx.2.2
  let S := narrower R W hW
  let M := restrictedSmoothAtlas LM S
  apply (GlobalSpinDisplacement.relative_on LM a t S hp ha ht).trans
  apply Eq.trans _ (ofCover_restrict R.covers (W.asRefinement id hW) _)
  apply congrArg (ofCover W.domain W.covers)
  apply Eq.trans _ (difference_shrink LM R W hW A T)
  exact SpinLiftHOneTorsor.differenceClass_congr
    ((SpinGeometricLiftClasses.nonempty_between_iff_gauge M _ _).mp
      ⟨between_adaptOn_shrink LM R W hW hp A ha⟩)
    ((SpinGeometricLiftClasses.nonempty_between_iff_gauge M _ _).mp
      ⟨between_adaptOn_shrink LM R W hW hp T ht⟩)

end FoliationQM.GlobalSpinPresentationFormula
