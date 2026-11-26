module
public import FoliationQM.AnchoredPullbackRefinement
public import FoliationQM.RefinedGeometricPrincipalAtlas

/-!
# Restriction and pullback of principal coordinates

For the geometric Spin bundle in v13 `prop:takabayasi`, the two orders
of restricting and pulling back principal charts have identical forward
coordinates. Their inverse maps and unit sections agree on each actual
preimage chart. These equations compare the restricted physical targets.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.RestrictedPrincipalPullback
open GeometricPrincipalPullback RefinedGeometricPrincipalAtlas CliffordSpinCoverRefinement

variable {X B T G ι κ : Type*} [TopologicalSpace X] [TopologicalSpace B]
  [TopologicalSpace T] [TopologicalSpace G] [Group G] {p : T → B}
  (f : C(X, B)) (A : GeometricPrincipalAtlas.Data (G := G) p ι)
  (R : Refinement (domains A) κ)

/-- Both constructions use the lifted original right action. -/
theorem right_eq : (atlas f (restrictedAtlas A R)).right =
    (restrictedAtlas (atlas f A) (ModTwoPullbackRefinement.refinement f R)).right := rfl

/-- Their forward coordinates are identical at every actual pullback point. -/
theorem chart_eq (i : κ) (z : Total f p) :
    (atlas f (restrictedAtlas A R)).triv i z =
      (restrictedAtlas (atlas f A) (ModTwoPullbackRefinement.refinement f R)).triv i z := rfl

/-- On the true chart target, both inverse maps reconstruct the same original total point. -/
theorem inverse_eq (i : κ) (z : X × G) (hz : f z.1 ∈ R.domain i) :
    ((atlas f (restrictedAtlas A R)).triv i).toOpenPartialHomeomorph.symm z =
      ((restrictedAtlas (atlas f A) (ModTwoPullbackRefinement.refinement f R)).triv i).toOpenPartialHomeomorph.symm z := by
  apply Subtype.ext
  change (inverseChart f (restrictedAtlas A R) i z).val =
    (inverseChart f A (R.parent i) z).val
  rw [inverseChart_val f (restrictedAtlas A R) i z hz,
    inverseChart_val f A (R.parent i) z (R.subset i hz)]
  rfl

/-- In particular, the unit sections agree on each pulled refined chart. -/
theorem localSection_eq (i : κ) (x : X) (hx : f x ∈ R.domain i) :
    (atlas f (restrictedAtlas A R)).localSection i x =
      (restrictedAtlas (atlas f A) (ModTwoPullbackRefinement.refinement f R)).localSection i x :=
  inverse_eq f A R i (x, 1) hx

/-- The extracted principal transitions agree wherever the refined pair is defined. -/
theorem transition_eq (i j : κ) (x : X) (hi : f x ∈ R.domain i) (hj : f x ∈ R.domain j) :
    (atlas f (restrictedAtlas A R)).transition i j x =
      (restrictedAtlas (atlas f A) (ModTwoPullbackRefinement.refinement f R)).transition i j x := by
  rw [GeometricPrincipalPullback.transition_eq f (restrictedAtlas A R) i j x hi hj]
  exact (GeometricPrincipalPullback.transition_eq f A (R.parent i) (R.parent j) x
    (R.subset i hi) (R.subset j hj)).symm

/-- Reindexing the restricted pulled charts gives the anchored unit section of the direct pullback. -/
theorem anchored_localSection_eq (R : Refinement (domains A) B) (hm : ∀ b, b ∈ R.domain b)
    (i x : X) (hx : f x ∈ R.domain (f i)) :
    (restrictedAtlas (atlas f (restrictedAtlas A R)) (AnchoredPullbackRefinement.reindex f R hm)).localSection i x =
      (restrictedAtlas (atlas f A) (AnchoredPullbackRefinement.refinement f R hm)).localSection i x :=
  localSection_eq f A R (f i) x hx

end FoliationQM.RestrictedPrincipalPullback
