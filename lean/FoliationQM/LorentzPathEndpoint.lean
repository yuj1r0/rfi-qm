module
public import FoliationQM.BasedPathQuotient
public import FoliationQM.CliffordSpinPathLifting

/-!
# Actual Spin endpoints of intrinsic Lorentz path classes

For the geometric component of v13 `prop:takabayasi`, lift each actual
identity-based Lorentz path through the Clifford unit. Uniqueness of
covering-path lifts proves multiplicativity. Endpoint-relative homotopy
invariance kills the intrinsic null subgroup, so the endpoint descends
to the independently constructed path quotient. Its actual Lorentz
projection is the original endpoint homomorphism.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.LorentzPathEndpoint
open BasedPathGroup CliffordSpinMap CliffordSpinLorentz CliffordSpinPathLifting LorentzMatrixGroup

/-- The actual continuous Spin path over a given based Lorentz path, anchored at the Clifford unit. -/
def lifted (p : BasedPath ProperFutureLorentz) : C(unitInterval, Spin) :=
  pathLift p.val 1 (p.property.trans (map_one lorentzHom).symm)

/-- The lifted path retains the actual Lorentz path at every parameter. -/
theorem lifted_projects (p : BasedPath ProperFutureLorentz) (t : unitInterval) :
    lorentzHom (lifted p t) = p.val t :=
  congrFun (pathLift_projects p.val 1 (p.property.trans (map_one lorentzHom).symm)) t

/-- Every lifted based path starts at the actual Clifford unit. -/
theorem lifted_zero (p : BasedPath ProperFutureLorentz) : lifted p 0 = 1 :=
  pathLift_zero _ _ _

/-- The actual lift of the constant based Lorentz path is the constant Spin path. -/
theorem lifted_one : lifted (1 : BasedPath ProperFutureLorentz) = 1 := by
  symm
  apply (eq_pathLift_iff _ 1 _ (1 : C(unitInterval, Spin))).mpr
  constructor
  · funext t
    exact map_one lorentzHom
  · rfl

/-- Uniqueness of genuine path lifts makes lifting compatible with pointwise multiplication. -/
theorem lifted_mul (p q : BasedPath ProperFutureLorentz) : lifted (p * q) = lifted p * lifted q := by
  symm
  apply (eq_pathLift_iff _ 1 _ (lifted p * lifted q)).mpr
  constructor
  · funext t
    change lorentzHom (lifted p t * lifted q t) = p.val t * q.val t
    rw [map_mul, lifted_projects, lifted_projects]
  · change lifted p 0 * lifted q 0 = 1
    rw [lifted_zero, lifted_zero, one_mul]

/-- The actual final Spin value of a unit-anchored Lorentz path lift. -/
def endpoint (p : BasedPath ProperFutureLorentz) : Spin := lifted p 1

/-- The final Spin value projects to the original actual Lorentz endpoint. -/
theorem endpoint_projects (p : BasedPath ProperFutureLorentz) :
    lorentzHom (endpoint p) = BasedPathGroup.endpoint p := lifted_projects p 1

/-- The constant path has the actual unit endpoint in Spin. -/
theorem endpoint_one : endpoint (1 : BasedPath ProperFutureLorentz) = 1 := by
  unfold endpoint
  rw [lifted_one]
  rfl

/-- Actual lifted endpoints multiply in the original pointwise path order. -/
theorem endpoint_mul (p q : BasedPath ProperFutureLorentz) : endpoint (p * q) = endpoint p * endpoint q :=
  congrArg (fun f : C(unitInterval, Spin) => f 1) (lifted_mul p q)

/-- The original actual-path interface computes exactly the same anchored lifted endpoint. -/
theorem endpoint_fromPath {g : ProperFutureLorentz} (p : Path (1 : ProperFutureLorentz) g) :
    endpoint (fromPath p) = pathLift p 1 (p.source.trans (map_one lorentzHom).symm) 1 := rfl

/-- The actual lifted endpoint is a homomorphism on the intrinsic based-path group. -/
def basedEndpoint : BasedPath ProperFutureLorentz →* Spin where
  toFun := endpoint
  map_one' := endpoint_one
  map_mul' := endpoint_mul

/-- Genuine endpoint-relative nullhomotopies force the actual Spin endpoint to be the unit. -/
theorem nullPaths_le_ker : nullPaths ProperFutureLorentz ≤ basedEndpoint.ker := by
  intro p hp
  change endpoint p = 1
  have he := pathLift_one_eq_of_homotopicRel hp 1
    (p.property.trans (map_one lorentzHom).symm)
    ((basedPath_zero (1 : BasedPath ProperFutureLorentz)).trans (map_one lorentzHom).symm)
  exact he.trans endpoint_one

/-- Actual Spin endpoints descend to the independently defined Lorentz path quotient. -/
def toSpin : PathCover ProperFutureLorentz →* Spin :=
  QuotientGroup.lift (nullPaths ProperFutureLorentz) basedEndpoint nullPaths_le_ker

/-- The quotient homomorphism retains the original actual lifted endpoint on every representative. -/
theorem toSpin_classOf (p : BasedPath ProperFutureLorentz) : toSpin (classOf p) = endpoint p := rfl

/-- The quotient-to-Spin comparison commutes with the actual Lorentz projections. -/
theorem toSpin_projection (c : PathCover ProperFutureLorentz) :
    lorentzHom (toSpin c) = projection c := by
  obtain ⟨p, rfl⟩ := classOf_surjective c
  exact endpoint_projects p

end FoliationQM.LorentzPathEndpoint
