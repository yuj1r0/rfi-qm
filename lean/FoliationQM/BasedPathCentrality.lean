module
public import FoliationQM.BasedPathQuotient
public import FoliationQM.PathConjugationHomotopy

/-!
# Centrality of the intrinsic path-group endpoint kernel

For the geometric frame obstruction associated with v13 `prop:takabayasi`,
the based-path quotient is constructed from actual paths and homotopies.
The kernel of its endpoint homomorphism is central because conjugating
a loop by a based path preserves its relative-endpoint homotopy class.
No Clifford group, Spin covering, or transported group law occurs here.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.BasedPathCentrality
open BasedPathGroup

variable {G : Type*} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]

/-- The class of an endpoint-one based path is unchanged by conjugating it by another based path. -/
theorem classOf_conjugate (p q : BasedPath G) (hp : endpoint p = 1) :
    classOf (q * p * q⁻¹) = classOf p := by
  symm
  exact classOf_eq_of_homotopic p (q * p * q⁻¹)
    (PathConjugationHomotopy.homotopicRel q.val p.val
      (basedPath_zero q) (basedPath_zero p) hp)

/-- Every element of the endpoint kernel commutes with every intrinsic path-group element. -/
theorem commute_of_projection_eq_one (a b : PathCover G) (ha : projection a = 1) :
    Commute a b := by
  obtain ⟨p, rfl⟩ := classOf_surjective a
  obtain ⟨q, rfl⟩ := classOf_surjective b
  have hp : endpoint p = 1 := (projection_classOf p).symm.trans ha
  have h := congrArg (fun x : PathCover G => x * classOf q) (classOf_conjugate p q hp)
  change classOf p * classOf q = classOf q * classOf p
  simpa only [map_mul, map_inv, mul_assoc, inv_mul_cancel, mul_one] using h.symm

/-- The literal kernel of the actual endpoint homomorphism is a central subgroup. -/
theorem kernel_central (a : (projection (G := G)).ker) (b : PathCover G) :
    Commute a.val b := commute_of_projection_eq_one a.val b a.property

/-- In particular, the intrinsic endpoint-kernel multiplication is commutative. -/
theorem kernel_mul_comm (a b : (projection (G := G)).ker) : a * b = b * a :=
  Subtype.ext (kernel_central a b.val).eq

/-- The literal endpoint kernel has its original subgroup operations and the proved commutativity law. -/
instance instCommGroupKernel : CommGroup ↥((projection (G := G)).ker) :=
  { (inferInstance : Group ↥((projection (G := G)).ker)) with
    mul_comm := kernel_mul_comm }

end FoliationQM.BasedPathCentrality
