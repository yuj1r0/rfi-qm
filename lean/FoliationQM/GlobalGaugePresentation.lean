module
public import FoliationQM.GlobalLorentzGaugeAtlas
public import FoliationQM.TransitionNullhomotopyCriterion
public import FoliationQM.ParacompactBundleObstruction

/-!
# Presentation and zero native obstruction of the product bundle in arbitrary gauges

For the frame component of v13 `prop:takabayasi`, the product has a
single global principal chart. Its normalized diagonal paths give zero
intrinsic triple defects. Transferring this chart's presentation to the
two given gauges supplies paths on an anchored refinement for every
continuous gauge map, including maps which do not contract.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.GlobalGaugePresentation
open LorentzMatrixGroup PrincipalAtlasCrossGauge PathTransitionData GlobalLorentzGaugeAtlas
open PresentedLorentzBundle CliffordSpinCoverRefinement RefinedGeometricPrincipalAtlas

variable {B : Type*} [TopologicalSpace B] (k : C(B, ProperFutureLorentz))

/-- With one global trivialization, all normalized paths are diagonal. -/
def standardFamily (B : Type*) [TopologicalSpace B] : Family (data (standard B)) :=
  TransitionNullhomotopyCriterion.ofNull _ (fun i j hij => (hij (Subsingleton.elim i j)).elim)

/-- The single-chart atlas presents the product with the very same action as the two gauges. -/
theorem hasPresentation : HasPresentation (Prod.fst : B × ProperFutureLorentz → B) (atlas k).right :=
  has_of_atlas (standard B) (right_eq_standard k).symm (standardFamily B)

/-- The anchored refinement of the two specified gauges obtained from the standard chart. -/
abbrev refinement : Refinement (domains (atlas k)) B :=
  AtlasPathTransfer.refinement (standard B) (atlas k)

/-- Each point belongs to the chart bearing its index. -/
theorem mem_refinement (a : B) : a ∈ (refinement k).domain a :=
  AtlasPathTransfer.mem_refinement _ _ a

/-- Normalized transition paths for the original trivializations on the refined opens. -/
def refinedFamily : Family (data (restrictedAtlas (atlas k) (refinement k))) :=
  AtlasPathTransfer.family (standard B) (atlas k) (right_eq_standard k).symm (standardFamily B)

/-- The refined path reaches the original transition at the designated parents. -/
theorem refined_target (a b : B)
    (x : pairOverlap (data (restrictedAtlas (atlas k) (refinement k))) a b) :
    (refinedFamily k).homotopy a b (1, x) =
      (atlas k).transition ((refinement k).parent a) ((refinement k).parent b) x :=
  (refinedFamily k).target a b x

variable [LocallyPathConnectedSpace B]

/-- Every intrinsic triple defect in the single chart is the group unit. -/
theorem standard_zero :
    GlobalIntrinsicPathObstruction.obstruction LorentzPathCoefficient.character (standardFamily B) = 0 := by
  apply GlobalIntrinsicPathObstruction.zero_of_defects
  intro i j l x hi hj hl
  obtain rfl : i = j := Subsingleton.elim i j
  exact IntrinsicPathCocycle.defect_self_left (standardFamily B) i l x hi hl

/-- The native obstruction of the presented product in its two gauges is zero. -/
theorem native_zero : PresentedLorentzBundle.obstruction (hasPresentation k) = 0 :=
  (PresentedLorentzBundle.obstruction_eq (hasPresentation k) (standard B)
    (right_eq_standard k).symm (standardFamily B)).trans standard_zero

/-- When the canonical atlas construction applies, it computes the same zero class. -/
theorem canonical_zero [ParacompactSpace B] [NormalSpace B] :
    ParacompactBundleObstruction.obstruction (atlas k) = 0 :=
  (ParacompactBundleObstruction.eq_presented _ (hasPresentation k)).trans (native_zero k)

end FoliationQM.GlobalGaugePresentation
