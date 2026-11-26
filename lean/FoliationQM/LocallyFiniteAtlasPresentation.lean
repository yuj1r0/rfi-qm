module
public import FoliationQM.ControlledTransitionRefinement
public import FoliationQM.PresentedLorentzBundle

/-!
# Presenting the actual Lorentz atlas from a locally finite shrinking

For the frame-bundle component of v13 `prop:takabayasi`, restricting the
original trivializations to the controlled opens constructs a presentation
of the given projection and right action. The shrinking only specifies
open sets. The normalized paths are constructed from the actual transitions.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.LocallyFiniteAtlasPresentation
open LorentzMatrixGroup PrincipalAtlasCrossGauge RefinedGeometricPrincipalAtlas
open PathTransitionData CliffordSpinCoverRefinement

variable {B T ι : Type*} [TopologicalSpace B] [TopologicalSpace T] {proj : T → B}
  (A : GeometricPrincipalAtlas.Data (G := ProperFutureLorentz) proj ι)
  (S : LocallyFiniteChartShrinking.Data (domains A))

/-- The original chart containing each point is chosen from the locally finite shrinking. -/
abbrev refinement : Refinement (domains A) B :=
  ControlledTransitionRefinement.refinement (data A) S

/-- Restrict the actual principal trivializations on their original total space. -/
def atlas : GeometricPrincipalAtlas.Data (G := ProperFutureLorentz) proj B :=
  restrictedAtlas A (refinement A S)

/-- The extracted geometric transitions are exactly the restrictions of the parent transitions. -/
theorem transition_data : data (atlas A S) = IntrinsicPathRestriction.data (data A) (refinement A S) :=
  rfl

/-- On each ordered refined pair one Cayley neighborhood contains the whole transition image. -/
theorem pairBounded : LorentzLocalPathFamily.PairBounded (data (atlas A S)) :=
  ControlledTransitionRefinement.pairBounded (data A) S

/-- Normalized joint paths on the restricted actual atlas. -/
def family : Family (data (atlas A S)) :=
  LorentzLocalPathFamily.family _ (pairBounded A S)

/-- At time one each path reaches the original transition between its designated parents. -/
theorem family_target (a b : B) (x : pairOverlap (data (atlas A S)) a b) :
    (family A S).homotopy a b (1, x) =
      A.transition ((refinement A S).parent a) ((refinement A S).parent b) x :=
  (family A S).target a b x

/-- The anchored atlas and its normalized family present the original projected action. -/
def presentation : PresentedLorentzBundle.Presentation proj A.right where
  atlas := atlas A S
  anchor := ControlledTransitionRefinement.mem_refinement (data A) S
  right_eq := rfl
  family := family A S

/-- The presentation's chart at an anchor is the actual restriction of its parent trivialization. -/
theorem presentation_triv (a : B) :
    (presentation A S).atlas.triv a = restrictedTriv A (refinement A S) a := rfl

include S in
/-- A locally finite open shrinking with subordinate closures supplies a path presentation. -/
theorem hasPresentation : PresentedLorentzBundle.HasPresentation proj A.right :=
  ⟨presentation A S⟩

end FoliationQM.LocallyFiniteAtlasPresentation
