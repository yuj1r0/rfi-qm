module
public import FoliationQM.GlobalIntrinsicPathObstruction
public import FoliationQM.ModTwoGlobalPullback

/-!
# Pullback of the intrinsic path obstruction

For the characteristic-class comparison supporting v13 `prop:takabayasi`,
pull back each open and transition along the continuous base map. The joint
paths on the resulting overlaps are the original joint paths at the image
points. Their triple defects give the pulled-back native mod-two cocycle and
its corresponding all-cover class.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.IntrinsicPathPullback
open PathTransitionData BasedPathGroup IntrinsicPathCocycle GlobalIntrinsicPathObstruction

variable {G B X Y ι : Type*} [TopologicalSpace G] [Group G]
  [TopologicalSpace B] [TopologicalSpace X] [TopologicalSpace Y]

/-- Pull an actual topological transition presentation back on the preimage open cover. -/
def data (f : C(X, B)) (D : Data G B ι) : Data G X ι where
  domain := ModTwoPullback.domain f D.domain
  covers := ModTwoPullback.covers f D.covers
  transition i j x := D.transition i j (f x)
  continuous_transition i j := (D.continuous_transition i j).comp f.continuous.continuousOn (fun _ h => h)
  identity i x hx := D.identity i (f x) hx
  comp i j k x hi hj hk := D.comp i j k (f x) hi hj hk

/-- The pulled presentation has the actual preimages of the original opens. -/
theorem data_domain (f : C(X, B)) (D : Data G B ι) :
    (data f D).domain = ModTwoPullback.domain f D.domain := rfl

/-- A pulled transition is the original transition at the image point. -/
theorem data_transition (f : C(X, B)) (D : Data G B ι) (i j : ι) (x : X) :
    (data f D).transition i j x = D.transition i j (f x) := rfl

variable {D : Data G B ι}

/-- Precompose each joint family with the actual time-preserving map of pair overlaps. -/
def family (f : C(X, B)) (P : Family D) : Family (data f D) where
  homotopy i j := (P.homotopy i j).comp
    ⟨fun z => (z.1, ModTwoPullback.pairMap f D.domain i j z.2),
      continuous_fst.prodMk ((ModTwoPullback.pairMap f D.domain i j).continuous.comp continuous_snd)⟩
  source i j x := P.source i j (ModTwoPullback.pairMap f D.domain i j x)
  target i j x := P.target i j (ModTwoPullback.pairMap f D.domain i j x)
  diagonal i t x := P.diagonal i t (ModTwoPullback.pairMap f D.domain i i x)

/-- At every time, the pulled-back family keeps the path value at the image point. -/
theorem family_apply (f : C(X, B)) (P : Family D) (i j : ι) (t : unitInterval)
    (x : pairOverlap (data f D) i j) : (family f P).homotopy i j (t, x) =
      P.homotopy i j (t, ModTwoPullback.pairMap f D.domain i j x) := rfl

/-- Pullback by the identity preserves the entire normalized joint family. -/
theorem family_id (P : Family D) : family (ContinuousMap.id B) P = P := rfl

/-- The two ways of pulling a joint path family along a composite give the same family. -/
theorem family_comp (f : C(X, B)) (g : C(Y, X)) (P : Family D) :
    family g (family f P) = family (f.comp g) P := rfl

/-- The whole transition path at a pulled-back pair point is the original path at its image. -/
theorem path_pull (f : C(X, B)) (P : Family D) (i j : ι) (x : X)
    (hi : x ∈ (data f D).domain i) (hj : x ∈ (data f D).domain j) :
    path (family f P) i j x hi hj = path P i j (f x) hi hj := rfl

variable [IsTopologicalGroup G]

/-- Passing to the intrinsic based-path quotient preserves this exact pullback formula. -/
theorem lift_pull (f : C(X, B)) (P : Family D) (i j : ι) (x : X)
    (hi : x ∈ (data f D).domain i) (hj : x ∈ (data f D).domain j) :
    lift (family f P) i j x hi hj = lift P i j (f x) hi hj := rfl

/-- The ordered triple loop at all times is the original loop on the corresponding true triple. -/
theorem loop_pull (f : C(X, B)) (P : Family D) (i j k : ι) (t : unitInterval)
    (x : tripleOverlap (data f D) i j k) : loopFamily (family f P) i j k (t, x) =
      loopFamily P i j k (t, ModTwoPullback.tripleMap f D.domain i j k x) := rfl

/-- The defect in the intrinsic endpoint kernel pulls back pointwise. -/
theorem defect_pull (f : C(X, B)) (P : Family D) (i j k : ι) (x : X)
    (hi : x ∈ (data f D).domain i) (hj : x ∈ (data f D).domain j) (hk : x ∈ (data f D).domain k) :
    defect (family f P) i j k x hi hj hk = defect P i j k (f x) hi hj hk := rfl

variable (e : (projection (G := G)).ker →* Multiplicative (ZMod 2))

/-- Evaluation of any intrinsic-kernel character retains its original triple coefficient. -/
theorem coefficient_pull (f : C(X, B)) (P : Family D) (i j k : ι) (x : X)
    (hi : x ∈ (data f D).domain i) (hj : x ∈ (data f D).domain j) (hk : x ∈ (data f D).domain k) :
    coefficient e (family f P) i j k x hi hj hk = coefficient e P i j k (f x) hi hj hk := rfl

variable [LocallyPathConnectedSpace B] [LocallyPathConnectedSpace X]

/-- The entire normalized path cocycle is the fixed-cover pullback of the original cocycle. -/
theorem cocycle_pull (f : C(X, B)) (P : Family D) :
    cocycle e (family f P) = ModTwoPullback.two f (cocycle e P) := rfl

/-- On the preimage cover the path class is the additive cohomology pullback. -/
theorem class_pull (f : C(X, B)) (P : Family D) :
    ModTwoCohomology.classOf (cocycle e (family f P)) =
      ModTwoPullback.hom f D.domain (ModTwoCohomology.classOf (cocycle e P)) :=
  (congrArg ModTwoCohomology.classOf (cocycle_pull e f P)).trans
    (ModTwoPullback.hom_classOf f (cocycle e P)).symm

/-- The global class computed from the actual pulled paths is the all-cover pullback of the original obstruction. -/
theorem obstruction_pull (f : C(X, B)) (P : Family D) :
    obstruction e (family f P) = ModTwoGlobalPullback.pull f (obstruction e P) :=
  (congrArg (ModTwoAllCover.ofCover (data f D).domain (data f D).covers) (class_pull e f P)).trans
    (ModTwoGlobalPullback.pull_ofCover f D.domain D.covers _).symm

end FoliationQM.IntrinsicPathPullback
