module
public import FoliationQM.GeometricPrincipalPullback
public import FoliationQM.IntrinsicPathPullback
public import FoliationQM.PresentedLorentzBundle
public import FoliationQM.ModTwoConstantPullback

/-!
# Naturality of the obstruction of a presented Lorentz principal space

For the geometric frame component of v13 `prop:takabayasi`, pulling
back an actual principal atlas gives a presentation on the fiber product.
Its transition paths are obtained from the original ones by composition.
This identifies the new bundle class with the pullback in all-cover
mod-two degree two for every continuous base map between locally path
connected spaces.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.PresentedBundlePullback
open LorentzMatrixGroup PresentedLorentzBundle

variable {X B T ι : Type*} [TopologicalSpace X] [TopologicalSpace B] [TopologicalSpace T]
  {proj : T → B} {act : T → ProperFutureLorentz → T}

/-- The prescribed action in a bundle presentation preserves its actual projection. -/
theorem proj_act (h : HasPresentation proj act) (p : T) (g : ProperFutureLorentz) :
    proj (act p g) = proj p := by
  rw [← h.some.right_eq]
  exact h.some.atlas.proj_right p g

/-- The right operation on the fiber product acts in the original principal fiber. -/
abbrev right (f : C(X, B)) (h : HasPresentation proj act) :=
  GeometricPrincipalPullback.right f act (proj_act h)

/-- Every atlas of the prescribed action induces this same geometric operation on the fiber product. -/
theorem atlas_right (f : C(X, B)) (h : HasPresentation proj act)
    (A : GeometricPrincipalAtlas.Data (G := ProperFutureLorentz) proj ι) (hA : A.right = act) :
    (GeometricPrincipalPullback.atlas f A).right = right f h := by
  subst act
  rfl

/-- Normalize the pulled transition paths against the transitions of the actual fiber-product charts. -/
def family (f : C(X, B)) (A : GeometricPrincipalAtlas.Data (G := ProperFutureLorentz) proj ι)
    (P : PathTransitionData.Family (PrincipalAtlasCrossGauge.data A)) :
    PathTransitionData.Family (PrincipalAtlasCrossGauge.data (GeometricPrincipalPullback.atlas f A)) where
  homotopy := (IntrinsicPathPullback.family f P).homotopy
  source := (IntrinsicPathPullback.family f P).source
  diagonal := (IntrinsicPathPullback.family f P).diagonal
  target i j x := ((IntrinsicPathPullback.family f P).target i j x).trans
    (GeometricPrincipalPullback.transition_eq f A i j x x.property.1 x.property.2).symm

/-- The path on each fiber-product overlap evaluates to the original path at its image. -/
theorem family_apply (f : C(X, B)) (A : GeometricPrincipalAtlas.Data (G := ProperFutureLorentz) proj ι)
    (P : PathTransitionData.Family (PrincipalAtlasCrossGauge.data A)) (i j : ι) (t : unitInterval)
    (x : PathTransitionData.pairOverlap (PrincipalAtlasCrossGauge.data (GeometricPrincipalPullback.atlas f A)) i j) :
    (family f A P).homotopy i j (t, x) = P.homotopy i j (t, ⟨f x.val, x.property⟩) := rfl

/-- A presentation of the original projected action supplies one for its actual fiber product. -/
theorem hasPresentation (f : C(X, B)) (h : HasPresentation proj act) :
    HasPresentation (GeometricPrincipalPullback.projection f proj) (right f h) :=
  has_of_atlas (GeometricPrincipalPullback.atlas f h.some.atlas) (atlas_right f h h.some.atlas h.some.right_eq)
    (family f h.some.atlas h.some.family)

variable [LocallyPathConnectedSpace X] [LocallyPathConnectedSpace B]

/-- The actual geometric obstruction on the fiber product is the continuous pullback of the bundle class. -/
theorem obstruction_natural (f : C(X, B)) (h : HasPresentation proj act) :
    obstruction (hasPresentation f h) = ModTwoGlobalPullback.pull f (obstruction h) := by
  let A := h.some.atlas
  let P := h.some.family
  rw [obstruction_eq (hasPresentation f h) _ (atlas_right f h A h.some.right_eq) (family f A P),
    obstruction_eq h A h.some.right_eq P]
  exact (IntrinsicAtlasComparison.obstruction_eqOn LorentzPathCoefficient.character
    (family f A P) (IntrinsicPathPullback.family f P) rfl (GeometricPrincipalPullback.transition_eq f A)).trans
    (IntrinsicPathPullback.obstruction_pull LorentzPathCoefficient.character f P)

/-- Any presentation with the same prescribed action on the fiber product computes the pullback class. -/
theorem obstruction_of_right_eq (f : C(X, B)) (h : HasPresentation proj act)
    {a : GeometricPrincipalPullback.Total f proj → ProperFutureLorentz → GeometricPrincipalPullback.Total f proj}
    (k : HasPresentation (GeometricPrincipalPullback.projection f proj) a) (ha : a = right f h) :
    obstruction k = ModTwoGlobalPullback.pull f (obstruction h) := by
  subst a
  exact obstruction_natural f h

/-- A zero obstruction remains zero after every continuous base change. -/
theorem zero_of_zero (f : C(X, B)) (h : HasPresentation proj act) (hz : obstruction h = 0) :
    obstruction (hasPresentation f h) = 0 := by rw [obstruction_natural, hz, map_zero]

/-- Pullback along a constant map has vanishing bundle obstruction. -/
theorem constant_zero (b : B) (h : HasPresentation proj act) :
    obstruction (hasPresentation (ContinuousMap.const X b) h) = 0 := by
  rw [obstruction_natural, ModTwoConstantPullback.pull_const]

/-- A homeomorphic change of base preserves and reflects vanishing for the fiber-product bundle. -/
theorem homeomorph_zero_iff (e : X ≃ₜ B) (h : HasPresentation proj act) :
    obstruction (hasPresentation (e : C(X, B)) h) = 0 ↔ obstruction h = 0 := by
  rw [obstruction_natural, ModTwoGlobalPullback.homeomorph_zero_iff]

end FoliationQM.PresentedBundlePullback
