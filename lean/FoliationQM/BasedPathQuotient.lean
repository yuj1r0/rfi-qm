module
public import FoliationQM.BasedPathGroup
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# The intrinsic endpoint extension defined by actual based paths

For the geometric characteristic-class comparison supporting v13
`prop:takabayasi`, quotient the actual based path group by its proved
normal nullhomotopic subgroup. Equality in this group is exactly
endpoint-relative path homotopy. Its endpoint homomorphism is defined
intrinsically and is surjective when the original group is path connected.
No external covering group, covering topology, or Spin identification
is used or asserted in this algebraic construction.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.BasedPathGroup

variable (G : Type*) [TopologicalSpace G] [Group G] [IsTopologicalGroup G]

/-- The intrinsic group of based path classes modulo actual endpoint-relative nullhomotopies. -/
abbrev PathCover := BasedPath G ⧸ nullPaths G

variable {G}

/-- The intrinsic quotient homomorphism from actual based paths to their classes. -/
def classOf : BasedPath G →* PathCover G := QuotientGroup.mk' (nullPaths G)

/-- Every intrinsic path class has an actual continuous based path representative. -/
theorem classOf_surjective : Function.Surjective (classOf (G := G)) :=
  QuotientGroup.mk'_surjective (nullPaths G)

/-- Equality of intrinsic classes is precisely a homotopy relative to both endpoints. -/
theorem classOf_eq_iff_homotopic (p q : BasedPath G) :
    classOf p = classOf q ↔ p.val.HomotopicRel q.val {0, 1} :=
  QuotientGroup.eq.trans (homotopic_iff_inv_mul_null p q).symm

/-- An actual endpoint-relative homotopy identifies the intrinsic path classes. -/
theorem classOf_eq_of_homotopic (p q : BasedPath G)
    (h : p.val.HomotopicRel q.val {0, 1}) : classOf p = classOf q :=
  (classOf_eq_iff_homotopic p q).mpr h

/-- An intrinsic based path class is the unit exactly when the actual path is nullhomotopic relative endpoints. -/
theorem classOf_eq_one_iff (p : BasedPath G) :
    classOf p = 1 ↔ p.val.HomotopicRel 1 {0, 1} :=
  QuotientGroup.eq_one_iff p

/-- Endpoint evaluation descends to the intrinsic path-class group because every null path closes. -/
def projection : PathCover G →* G :=
  QuotientGroup.lift (nullPaths G) endpoint nullPaths_le_endpoint_ker

/-- The endpoint of a class represented by a based path is its literal actual endpoint. -/
theorem projection_classOf (p : BasedPath G) : projection (classOf p) = endpoint p := rfl

/-- Every element of a path-connected original group is the projection of an intrinsic path class. -/
theorem projection_surjective [PathConnectedSpace G] :
    Function.Surjective (projection (G := G)) := by
  intro g
  obtain ⟨p, hp⟩ := endpoint_surjective (G := G) g
  exact ⟨classOf p, hp⟩

/-- An actual identity-anchored path defines its intrinsic class without any external lift choice. -/
def pathClass {g : G} (p : Path (1 : G) g) : PathCover G := classOf (fromPath p)

/-- The intrinsic class of an actual path projects to the supplied endpoint of that path. -/
theorem projection_pathClass {g : G} (p : Path (1 : G) g) : projection (pathClass p) = g :=
  endpoint_fromPath p

/-- For paths with the same actual endpoint, intrinsic class equality is exactly based path homotopy. -/
theorem pathClass_eq_iff {g : G} (p q : Path (1 : G) g) :
    pathClass p = pathClass q ↔ p.Homotopic q :=
  classOf_eq_iff_homotopic (fromPath p) (fromPath q)

end FoliationQM.BasedPathGroup
