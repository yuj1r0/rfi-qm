module
public import FoliationQM.BasedPathQuotient
public import Mathlib.Topology.Sets.Opens

/-!
# Independent topological transition data and actual path families

For the geometric characteristic-class comparison supporting v13
`prop:takabayasi`, the input consists only of a topological group,
an open cover, and actual continuous group-valued transitions.
Jointly continuous normalized paths to those transitions determine
intrinsic path classes. No physical Spin lift or cocycle in a covering
group is supplied.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.PathTransitionData
open BasedPathGroup

/-- Actual topological group transitions on a specified open cover,
with the original ordered composition law. -/
structure Data (G : Type*) [TopologicalSpace G] [Group G]
    (B : Type*) [TopologicalSpace B] (ι : Type*) where
  /-- The original covering domains. -/
  domain : ι → TopologicalSpace.Opens B
  /-- These domains cover the actual base. -/
  covers : ∀ x : B, ∃ i, x ∈ domain i
  /-- Total representatives of the actual transitions. -/
  transition : ι → ι → B → G
  /-- Only true pair intersections carry a continuity requirement. -/
  continuous_transition : ∀ i j, ContinuousOn (transition i j)
    ((domain i : Set B) ∩ domain j)
  /-- Every true diagonal transition is the identity. -/
  identity : ∀ i x, x ∈ domain i → transition i i x = 1
  /-- Actual transition composition holds on each true triple overlap. -/
  comp : ∀ i j k x, x ∈ domain i → x ∈ domain j → x ∈ domain k →
    transition j k x * transition i j x = transition i k x

variable {G B ι : Type*} [TopologicalSpace G] [Group G] [TopologicalSpace B]

/-- The genuine open pair overlap of the independent transition data. -/
abbrev pairOverlap (D : Data G B ι) (i j : ι) : TopologicalSpace.Opens B :=
  D.domain i ⊓ D.domain j

/-- The genuine open triple overlap of the independent transition data. -/
abbrev tripleOverlap (D : Data G B ι) (i j k : ι) : TopologicalSpace.Opens B :=
  (D.domain i ⊓ D.domain j) ⊓ D.domain k

/-- Actual normalized transition paths jointly continuous in time and the point
of the original pair intersection. -/
structure Family (D : Data G B ι) where
  /-- The actual jointly continuous path family. -/
  homotopy : ∀ i j, C(unitInterval × ↥(pairOverlap D i j), G)
  /-- Every path starts at the group unit. -/
  source : ∀ i j (x : pairOverlap D i j), homotopy i j (0, x) = 1
  /-- Every path ends at the original transition. -/
  target : ∀ i j (x : pairOverlap D i j), homotopy i j (1, x) = D.transition i j x
  /-- Diagonal paths are the actual constant unit paths. -/
  diagonal : ∀ i (t : unitInterval) (x : pairOverlap D i i), homotopy i i (t, x) = 1

variable {D : Data G B ι}

/-- The actual identity-anchored transition path at a point of a true overlap. -/
def path (P : Family D) (i j : ι) (x : B)
    (hi : x ∈ D.domain i) (hj : x ∈ D.domain j) : Path 1 (D.transition i j x) where
  toContinuousMap := (P.homotopy i j).comp
    ((ContinuousMap.id unitInterval).prodMk (.const unitInterval ⟨x, hi, hj⟩))
  source' := P.source i j ⟨x, hi, hj⟩
  target' := P.target i j ⟨x, hi, hj⟩

/-- Each pointwise path is the exact time slice of the supplied joint family. -/
theorem path_apply (P : Family D) (i j : ι) (x : B)
    (hi : x ∈ D.domain i) (hj : x ∈ D.domain j) (t : unitInterval) :
    path P i j x hi hj t = P.homotopy i j (t, ⟨x, hi, hj⟩) := rfl

variable [IsTopologicalGroup G]

/-- The actual based path underlying a given transition time slice. -/
def basedPath (P : Family D) (i j : ι) (x : B)
    (hi : x ∈ D.domain i) (hj : x ∈ D.domain j) : BasedPath G :=
  fromPath (path P i j x hi hj)

/-- The based-path group representative retains every supplied path value. -/
theorem basedPath_apply (P : Family D) (i j : ι) (x : B)
    (hi : x ∈ D.domain i) (hj : x ∈ D.domain j) (t : unitInterval) :
    (basedPath P i j x hi hj).val t = P.homotopy i j (t, ⟨x, hi, hj⟩) := rfl

/-- The intrinsic path-class lift is defined by the actual transition path,
without any external covering-group choice. -/
def lift (P : Family D) (i j : ι) (x : B)
    (hi : x ∈ D.domain i) (hj : x ∈ D.domain j) : PathCover G :=
  classOf (basedPath P i j x hi hj)

/-- The intrinsic path-class endpoint is precisely the original transition. -/
theorem projection_lift (P : Family D) (i j : ι) (x : B)
    (hi : x ∈ D.domain i) (hj : x ∈ D.domain j) :
    projection (lift P i j x hi hj) = D.transition i j x :=
  (path P i j x hi hj).target

/-- The intrinsic lift of every true diagonal is the unit class. -/
theorem lift_diagonal (P : Family D) (i : ι) (x : B) (hi : x ∈ D.domain i) :
    lift P i i x hi hi = 1 := by
  have he : basedPath P i i x hi hi = 1 :=
    Subtype.ext (ContinuousMap.ext (fun t => P.diagonal i t ⟨x, hi, hi⟩))
  change classOf (basedPath P i i x hi hi) = 1
  rw [he, map_one]

end FoliationQM.PathTransitionData
