module
public import FoliationQM.PathTransitionData
public import Mathlib.Topology.Homotopy.Contractible

/-!
# Constructing actual transition paths from standard contractibility

For the geometric characteristic-class comparison supporting v13
`prop:takabayasi`, standard contractibility of every nonempty actual
pair overlap constructs normalized jointly continuous transition paths.
The construction concatenates a genuine path from the group identity
to a transition value with the image of an actual contraction. Empty
overlaps require no contractibility premise, and diagonals are constant.
No Spin lift, chosen transition-path family, or desired cocycle is an input.
Existence of a cover with these properties is not asserted.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.ContractibleTransitionPaths
open PathTransitionData

section ContractibleMap

variable {X G : Type*} [TopologicalSpace X] [ContractibleSpace X]
  [TopologicalSpace G] [One G] [PathConnectedSpace G]

/-- An actual joint homotopy from the constant unit to any continuous
map on a standard contractible parameter space. -/
def fromOne (f : C(X, G)) : (ContinuousMap.const X 1).Homotopy f := by
  let x := Classical.choose (id_nullhomotopic X)
  let H := Classical.choice (Classical.choose_spec (id_nullhomotopic X))
  exact (PathConnectedSpace.somePath 1 (f x)).toHomotopyConst.trans
    ((ContinuousMap.Homotopy.refl f).comp H.symm)

/-- Every constructed joint homotopy starts at the actual group unit. -/
theorem fromOne_zero (f : C(X, G)) (x : X) : fromOne f (0, x) = 1 :=
  (fromOne f).apply_zero x

/-- Every constructed joint homotopy ends at the original continuous map. -/
theorem fromOne_one (f : C(X, G)) (x : X) : fromOne f (1, x) = f x :=
  (fromOne f).apply_one x

end ContractibleMap

variable {G B ι : Type*} [TopologicalSpace G] [Group G] [TopologicalSpace B]

/-- Standard topological contractibility is required precisely for
nonempty actual pair overlaps, with no separately supplied contractions. -/
def PairContractible (D : Data G B ι) : Prop :=
  ∀ i j, Nonempty ↥(pairOverlap D i j) → ContractibleSpace ↥(pairOverlap D i j)

/-- The diagonal pair hypothesis gives standard contractibility of
every nonempty original chart domain. -/
theorem chart_contractible (D : Data G B ι) (h : PairContractible D) (i : ι) :
    Nonempty ↥(D.domain i) → ContractibleSpace ↥(D.domain i) := by
  have he : pairOverlap D i i = D.domain i := inf_idem _
  exact (congrArg (fun U : TopologicalSpace.Opens B =>
    Nonempty ↥U → ContractibleSpace ↥U) he).mp (h i i)

/-- The original transition as a continuous map on its actual pair overlap. -/
def transitionMap (D : Data G B ι) (i j : ι) : C(↥(pairOverlap D i j), G) :=
  ⟨fun x => D.transition i j x,
    (D.continuous_transition i j).comp_continuous continuous_subtype_val (fun x => x.property)⟩

/-- The continuous-map view retains the original transition at every overlap point. -/
theorem transitionMap_apply (D : Data G B ι) (i j : ι) (x : pairOverlap D i j) :
    transitionMap D i j x = D.transition i j x := rfl

variable [PathConnectedSpace G]

/-- Construct the joint identity-to-transition homotopy, using the
constant unit on diagonals and vacuously on empty off-diagonal overlaps. -/
def joint (D : Data G B ι) (h : PairContractible D) (i j : ι) :
    (ContinuousMap.const ↥(pairOverlap D i j) 1).Homotopy (transitionMap D i j) := by
  classical
  by_cases he : i = j
  · subst j
    exact (ContinuousMap.Homotopy.refl (ContinuousMap.const ↥(pairOverlap D i i) (1 : G))).cast rfl
      (ContinuousMap.ext (fun x => (D.identity i x x.property.1).symm))
  · by_cases hn : Nonempty ↥(pairOverlap D i j)
    · letI : ContractibleSpace ↥(pairOverlap D i j) := h i j hn
      exact fromOne (transitionMap D i j)
    · exact
        { toFun := fun _ => 1
          continuous_toFun := continuous_const
          map_zero_left := fun _ => rfl
          map_one_left := fun x => (hn ⟨x⟩).elim }

/-- Every constructed actual transition homotopy starts at the unit. -/
theorem joint_zero (D : Data G B ι) (h : PairContractible D) (i j : ι)
    (x : pairOverlap D i j) : joint D h i j (0, x) = 1 :=
  (joint D h i j).apply_zero x

/-- Every constructed actual transition homotopy ends at the given transition. -/
theorem joint_one (D : Data G B ι) (h : PairContractible D) (i j : ι)
    (x : pairOverlap D i j) : joint D h i j (1, x) = D.transition i j x :=
  (joint D h i j).apply_one x

/-- The diagonal homotopy is the constant unit at every time and actual chart point. -/
theorem joint_diagonal (D : Data G B ι) (h : PairContractible D) (i : ι)
    (t : unitInterval) (x : pairOverlap D i i) : joint D h i i (t, x) = 1 := by
  classical
  simp only [joint]
  rfl

/-- Standard contractibility of the nonempty pair overlaps constructs
a normalized jointly continuous family for the original transition data. -/
def family (D : Data G B ι) (h : PairContractible D) : Family D where
  homotopy i j := (joint D h i j).toContinuousMap
  source := joint_zero D h
  target := joint_one D h
  diagonal := joint_diagonal D h

/-- The constructed family's actual joint maps are precisely the homotopies
built from the original overlap topology and transition values. -/
theorem family_homotopy (D : Data G B ι) (h : PairContractible D) (i j : ι) :
    (family D h).homotopy i j = (joint D h i j).toContinuousMap := rfl

/-- The constructed family retains the actual original transition endpoint on each true pair overlap. -/
theorem family_target (D : Data G B ι) (h : PairContractible D) (i j : ι)
    (x : pairOverlap D i j) : (family D h).homotopy i j (1, x) = D.transition i j x :=
  (family D h).target i j x

end FoliationQM.ContractibleTransitionPaths
