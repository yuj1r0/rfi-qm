module
public import Mathlib.Topology.ContinuousMap.Algebra
public import Mathlib.Topology.Homotopy.Path
public import Mathlib.Topology.Connected.PathConnected
public import Mathlib.Algebra.Group.Subgroup.Basic

/-!
# The intrinsic group of based paths and its nullhomotopic subgroup

For the geometric characteristic-class comparison supporting v13
`prop:takabayasi`, this construction uses only continuous paths in a
topological group and homotopies relative to their two endpoints.
Neither a Clifford algebra nor a Spin covering enters any definition.
The based paths multiply pointwise. Paths homotopic relative endpoints
to the constant unit form a normal subgroup, proved by actual homotopies.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.BasedPathGroup

variable (G : Type*) [TopologicalSpace G] [Group G] [IsTopologicalGroup G]

/-- The pointwise subgroup of continuous paths starting at the group unit. -/
def basedPaths : Subgroup C(unitInterval, G) where
  carrier := {p | p 0 = 1}
  one_mem' := rfl
  mul_mem' {p q} hp hq := by
    change p 0 * q 0 = 1
    rw [hp, hq, one_mul]
  inv_mem' {p} hp := by
    change (p 0)⁻¹ = 1
    rw [hp, inv_one]

/-- Actual continuous based paths with their inherited pointwise group structure. -/
abbrev BasedPath := ↥(basedPaths G)

variable {G}

/-- Every based path starts at the genuine group identity. -/
theorem basedPath_zero (p : BasedPath G) : p.val 0 = 1 := p.property

/-- A based path has an actual endpoint, compatible with pointwise group operations. -/
def endpoint : BasedPath G →* G where
  toFun p := p.val 1
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The endpoint homomorphism is literal evaluation at the end of the interval. -/
theorem endpoint_apply (p : BasedPath G) : endpoint p = p.val 1 := rfl

/-- A based continuous map is an actual path to its own endpoint. -/
def toPath (p : BasedPath G) : Path (1 : G) (endpoint p) where
  toContinuousMap := p.val
  source' := p.property
  target' := rfl

/-- Any actual path from the identity gives an element of the based path group. -/
def fromPath {g : G} (p : Path (1 : G) g) : BasedPath G :=
  ⟨p.toContinuousMap, p.source⟩

/-- The constructed based map retains the original path's actual endpoint. -/
theorem endpoint_fromPath {g : G} (p : Path (1 : G) g) : endpoint (fromPath p) = g := p.target

/-- Path connectedness supplies based paths to every group element. -/
theorem endpoint_surjective [PathConnectedSpace G] : Function.Surjective (endpoint (G := G)) :=
  fun g => ⟨fromPath (PathConnectedSpace.somePath 1 g), endpoint_fromPath _⟩

/-- Pointwise multiplication preserves homotopy relative to any specified parameter subset. -/
theorem homotopic_mul {S : Set unitInterval} {p q r s : C(unitInterval, G)}
    (hp : p.HomotopicRel q S) (hr : r.HomotopicRel s S) :
    (p * r).HomotopicRel (q * s) S := by
  rcases hp with ⟨H⟩
  rcases hr with ⟨K⟩
  refine ⟨{ toFun := fun z => H z * K z
            continuous_toFun := H.continuous.mul K.continuous
            map_zero_left := ?_
            map_one_left := ?_
            prop' := ?_ }⟩
  · intro t
    change H (0, t) * K (0, t) = p t * r t
    rw [H.apply_zero, K.apply_zero]
  · intro t
    change H (1, t) * K (1, t) = q t * s t
    rw [H.apply_one, K.apply_one]
  · intro t x hx
    change H (t, x) * K (t, x) = p x * r x
    rw [H.eq_fst t hx, K.eq_fst t hx]

/-- Pointwise group inversion preserves homotopy relative to a parameter subset. -/
theorem homotopic_inv {S : Set unitInterval} {p q : C(unitInterval, G)}
    (hp : p.HomotopicRel q S) : p⁻¹.HomotopicRel q⁻¹ S := by
  rcases hp with ⟨H⟩
  refine ⟨{ toFun := fun z => (H z)⁻¹
            continuous_toFun := H.continuous.inv
            map_zero_left := ?_
            map_one_left := ?_
            prop' := ?_ }⟩
  · intro t
    change (H (0, t))⁻¹ = (p t)⁻¹
    rw [H.apply_zero]
  · intro t
    change (H (1, t))⁻¹ = (q t)⁻¹
    rw [H.apply_one]
  · intro t x hx
    change (H (t, x))⁻¹ = (p x)⁻¹
    rw [H.eq_fst t hx]

variable (G)

/-- The null subgroup consists precisely of based paths homotopic to
the constant unit relative to both endpoints. Endpoint closure is a consequence. -/
def nullPaths : Subgroup (BasedPath G) where
  carrier := {p | p.val.HomotopicRel 1 {0, 1}}
  one_mem' := ContinuousMap.HomotopicRel.refl 1
  mul_mem' hp hq := by
    change (_ * _ : C(unitInterval, G)).HomotopicRel 1 {0, 1}
    simpa only [mul_one] using homotopic_mul hp hq
  inv_mem' hp := by
    change (_⁻¹ : C(unitInterval, G)).HomotopicRel 1 {0, 1}
    simpa only [inv_one] using homotopic_inv hp

variable {G}

/-- Membership in the null subgroup is exactly an actual endpoint-relative nullhomotopy. -/
theorem mem_nullPaths_iff (p : BasedPath G) :
    p ∈ nullPaths G ↔ p.val.HomotopicRel 1 {0, 1} := Iff.rfl

/-- Nullhomotopic based paths end at the unit, so their subgroup lies in the endpoint kernel. -/
theorem nullPaths_le_endpoint_ker : nullPaths G ≤ (endpoint (G := G)).ker := by
  rintro p ⟨H⟩
  exact H.fst_eq_snd (by simp : (1 : unitInterval) ∈ ({0, 1} : Set unitInterval))

/-- Conjugating a nullhomotopy pointwise by a based path proves normality,
without reference to any external covering group. -/
instance nullPaths_normal : (nullPaths G).Normal where
  conj_mem p hp g := by
    change (g.val * p.val * g.val⁻¹).HomotopicRel 1 {0, 1}
    have h := homotopic_mul
      (homotopic_mul (ContinuousMap.HomotopicRel.refl g.val) hp)
      (ContinuousMap.HomotopicRel.refl g.val⁻¹)
    simpa only [mul_one, mul_inv_cancel] using h

/-- Endpoint-relative homotopy is exactly equality modulo the normal null subgroup,
expressed through the actual pointwise difference of based paths. -/
theorem homotopic_iff_inv_mul_null (p q : BasedPath G) :
    p.val.HomotopicRel q.val {0, 1} ↔ p⁻¹ * q ∈ nullPaths G := by
  constructor
  · intro h
    change (p.val⁻¹ * q.val).HomotopicRel 1 {0, 1}
    have hm := homotopic_mul (ContinuousMap.HomotopicRel.refl p.val⁻¹) h
    simpa only [inv_mul_cancel] using hm.symm
  · intro h
    change (p.val⁻¹ * q.val).HomotopicRel 1 {0, 1} at h
    have hm := homotopic_mul (ContinuousMap.HomotopicRel.refl p.val) h
    simpa only [mul_inv_cancel_left, mul_one] using hm.symm

end FoliationQM.BasedPathGroup
