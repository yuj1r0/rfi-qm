module
public import FoliationQM.SpinHOneGlobalPullback
public import FoliationQM.GeometricPrincipalPullback
public import FoliationQM.JointSpinAdaptation

/-!
# Anchored covers under a base map

For the smooth Spin classification in v13 `prop:takabayasi`, the
neighborhood assigned to a new base point is the preimage of the original
neighborhood assigned to its image. Reindexing by that image gives a
cover refinement, retains the containing Lorentz parent, and computes
the same global degree-one pullback class.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.AnchoredPullbackRefinement
open CliffordSpinCoverRefinement SpinAllCoverHOne SpinSignHOne SpinHOneRestriction

variable {X B ι : Type*} [TopologicalSpace X] [TopologicalSpace B]
  {U : ι → TopologicalSpace.Opens B}
  (f : C(X, B)) (R : Refinement U B) (hm : ∀ b, b ∈ R.domain b)

/-- Select the preimage chart assigned to each new point by its image in the original base. -/
def reindex : Refinement (ModTwoPullback.domain f R.domain) X where
  parent := f
  domain x := ModTwoPullback.domain f R.domain (f x)
  covers x := ⟨x, hm (f x)⟩
  subset _ _ hx := hx

/-- The anchored pullback refinement has the original containing parent at the image point. -/
def refinement : Refinement (ModTwoPullback.domain f U) X :=
  SpinRefinementComposition.compose (ModTwoPullbackRefinement.refinement f R) (reindex f R hm)

/-- Each new point belongs to its assigned preimage neighborhood. -/
theorem mem_refinement (x : X) : x ∈ (refinement f R hm).domain x := hm (f x)

/-- The assigned chart is exactly the preimage of the original chart at the image index. -/
theorem refinement_domain (x : X) :
    (refinement f R hm).domain x = ModTwoPullback.domain f R.domain (f x) := rfl

/-- The parent of the new chart is the parent of the original chart at its image index. -/
theorem refinement_parent (x : X) : (refinement f R hm).parent x = R.parent (f x) := rfl

section Lorentz
open LorentzMatrixGroup GeometricPrincipalPullback RefinedGeometricPrincipalAtlas JointSpinAdaptation
variable {T : Type*} [TopologicalSpace T] {p : T → B}
  (L : GeometricPrincipalAtlas.Data (G := ProperFutureLorentz) p ι)

/-- The actual pulled Lorentz atlas selects the same parent chart at the image base point. -/
theorem targetChart_pullback (x : X) : targetChart (atlas f L) x = targetChart L (f x) := rfl

/-- Alignment of the old containing parents gives alignment of the new anchored refinement. -/
theorem aligned (R : Refinement (domains L) B) (hm : ∀ b, b ∈ R.domain b)
    (hp : ∀ b, R.parent b = targetChart L b) (x : X) :
    (refinement f R hm).parent x = targetChart (atlas f L) x := hp (f x)
end Lorentz

section Smooth
variable {EX EB HX HB : Type*}
  [NormedAddCommGroup EX] [NormedSpace ℝ EX] [TopologicalSpace HX]
  [NormedAddCommGroup EB] [NormedSpace ℝ EB] [TopologicalSpace HB]
  [ChartedSpace HX X] [ChartedSpace HB B]
  {IX : ModelWithCorners ℝ EX HX} {IB : ModelWithCorners ℝ EB HB} {n : WithTop ℕ∞}

/-- Reindexing the pulled class onto the anchored preimages computes the global pullback. -/
theorem ofCover_reindex (hf : ContMDiff IX IB n f) (c : H1 IB R.domain n) :
    ofCover (refinement f R hm).domain (refinement f R hm).covers
      (restrictHom (reindex f R hm) (SpinHOnePullback.hom f hf R.domain c)) =
        SpinHOneGlobalPullback.pull f hf (ofCover R.domain R.covers c) :=
  (ofCover_restrict (ModTwoPullback.covers f R.covers) (reindex f R hm) _).trans
    (SpinHOneGlobalPullback.pull_ofCover f hf R.domain R.covers c).symm

end Smooth
end FoliationQM.AnchoredPullbackRefinement
