module
public import FoliationQM.AdaptedSpinCoverRestriction
public import FoliationQM.SpinAllCoverHOne
public import FoliationQM.SmoothSpinRelativeClass

/-!
# Shrinking an adapted presentation on a point-indexed Lorentz cover

For the global Spin-frame component of v13 `prop:takabayasi`, shrink the
domain at each point while retaining its assigned Lorentz chart. On these
smaller neighborhoods the supplied source atlas and an independently
adapted atlas of the same lift are physically isomorphic by the identity.
-/

@[expose] public section
noncomputable section
open Set
namespace FoliationQM.AlignedSpinPresentation
open CliffordSpinLorentzSmooth LorentzMatrixGroup GeometricSpinObstruction SpinLiftIsomorphism
open CliffordSpinCoverRefinement RefinedGeometricPrincipalAtlas JointSpinAdaptation
open SpinSignHOne SpinHOneRestriction SpinLiftSignDifference

universe u
variable {E H EP HP : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  [NormedAddCommGroup EP] [NormedSpace ℝ EP] [TopologicalSpace HP]
  {B : Type u} [TopologicalSpace B] [ChartedSpace H B] {I : ModelWithCorners ℝ E H}
  {P ι : Type*} [TopologicalSpace P] [ChartedSpace HP P] {KP : ModelWithCorners ℝ EP HP}
  {proj : P → B} {L : GeometricPrincipalAtlas.Data (G := ProperFutureLorentz) proj ι}
  {n : WithTop ℕ∞}

/-- Compose an aligned target presentation with a pointwise shrinking, retaining each original parent. -/
def narrower (R : Refinement (domains L) B) (W : SpinHOneDirected.Cover B)
    (hW : ∀ i, W.domain i ≤ R.domain i) : Refinement (domains L) B :=
  SpinRefinementComposition.compose R (W.asRefinement id hW)

/-- Restrict an arbitrary supplied adapted Spin presentation to the smaller neighborhoods. -/
def shrink (R : Refinement (domains L) B) (W : SpinHOneDirected.Cover B)
    (hW : ∀ i, W.domain i ≤ R.domain i) (A : GeometricSpinStructure.Lift I (restrictedAtlas L R) n) :
    GeometricSpinStructure.Lift I (restrictedAtlas L (narrower R W hW)) n :=
  AdaptedSpinCoverRestriction.restrict A (W.asRefinement id hW)

/-- The restricted physical map agrees with the original map at every point of the same total space. -/
theorem shrink_map (R : Refinement (domains L) B) (W : SpinHOneDirected.Cover B)
    (hW : ∀ i, W.domain i ≤ R.domain i) (A : GeometricSpinStructure.Lift I (restrictedAtlas L R) n)
    (q : A.Carrier) : (shrink R W hW A).map q = A.map q := rfl

/-- The simultaneous restriction of the source and target charts retains the entire principal action. -/
theorem shrink_right (R : Refinement (domains L) B) (W : SpinHOneDirected.Cover B)
    (hW : ∀ i, W.domain i ≤ R.domain i) (A : GeometricSpinStructure.Lift I (restrictedAtlas L R) n) :
    (shrink R W hW A).atlas.right = A.atlas.right := rfl

variable (LM : GeometricPrincipalSmoothAtlas.Data I lorentzModel KP L n)

/-- Shrinking at each point retains the parent Spin transition itself. -/
theorem transitions_shrink (R : Refinement (domains L) B) (W : SpinHOneDirected.Cover B)
    (hW : ∀ i, W.domain i ≤ R.domain i) (A : GeometricSpinStructure.Lift I (restrictedAtlas L R) n)
    (i j : B) : (transitions (restrictedSmoothAtlas LM (narrower R W hW))
      (shrink R W hW A)).transition i j = (transitions (restrictedSmoothAtlas LM R) A).transition i j := rfl

/-- Relative signs obtained from two supplied presentations restrict to their relative signs after shrinking. -/
theorem difference_shrink (R : Refinement (domains L) B) (W : SpinHOneDirected.Cover B)
    (hW : ∀ i, W.domain i ≤ R.domain i) (A T : GeometricSpinStructure.Lift I (restrictedAtlas L R) n) :
    classOf (difference (transitions (restrictedSmoothAtlas LM (narrower R W hW)) (shrink R W hW A))
      (transitions (restrictedSmoothAtlas LM (narrower R W hW)) (shrink R W hW T))) =
      restrictHom (W.asRefinement id hW) (classOf (difference
        (transitions (restrictedSmoothAtlas LM R) A) (transitions (restrictedSmoothAtlas LM R) T))) :=
  AdaptedSpinCoverRestriction.difference_restrict (restrictedSmoothAtlas LM R) A T
    (W.asRefinement id hW)

/-- The identity diffeomorphism compares independent adaptation with the supplied charts after shrinking. -/
def between_adaptOn_shrink (R : Refinement (domains L) B) (W : SpinHOneDirected.Cover B)
    (hW : ∀ i, W.domain i ≤ R.domain i) (hp : ∀ i, R.parent i = targetChart L i)
    (A : GeometricSpinStructure.Lift I (restrictedAtlas L R) n)
    (hA : ∀ i, (W.domain i : Set B) ⊆ neighborhood LM (ofRefined LM R A) i) :
    Between (adaptOn LM (ofRefined LM R A) (narrower R W hW) hp hA) (shrink R W hW A) where
  diffeo := Diffeomorph.refl _ _ _
  equivariant _ _ := rfl
  over _ := rfl

end FoliationQM.AlignedSpinPresentation
