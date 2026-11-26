module
public import FoliationQM.BasedPathQuotient
public import Mathlib.Topology.Connected.LocallyPathConnected
public import Mathlib.Topology.LocallyConstant.Basic

/-!
# Local constancy of intrinsic classes in jointly continuous loop families

For the geometric frame obstruction associated with v13 `prop:takabayasi`,
an actual path in the parameter space gives an endpoint-relative homotopy
between the corresponding loops. On a locally path connected parameter
space its path components are open, so the intrinsic path class is locally
constant. No topology on the quotient and no Spin lift is used.
-/

@[expose] public section
noncomputable section
open Set
namespace FoliationQM.BasedPathGroup

variable {G X : Type*} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
  [TopologicalSpace X]

/-- The actual based path at a parameter of a jointly continuous identity-starting family. -/
def slice (F : C(unitInterval × X, G)) (h₀ : ∀ x, F (0, x) = 1) (x : X) : BasedPath G :=
  ⟨F.comp ((ContinuousMap.id unitInterval).prodMk (.const unitInterval x)), h₀ x⟩

/-- Slicing retains the exact original value at each time and parameter. -/
theorem slice_apply (F : C(unitInterval × X, G)) (h₀ : ∀ x, F (0, x) = 1)
    (x : X) (t : unitInterval) : (slice F h₀ x).val t = F (t, x) := rfl

/-- A parameter-space path produces an actual homotopy between the loop slices,
with both loop endpoints fixed throughout. -/
def sliceHomotopy (F : C(unitInterval × X, G))
    (h₀ : ∀ x, F (0, x) = 1) (h₁ : ∀ x, F (1, x) = 1)
    {x y : X} (δ : Path x y) :
    (slice F h₀ x).val.HomotopyRel (slice F h₀ y).val {0, 1} where
  toFun z := F (z.2, δ z.1)
  continuous_toFun := F.continuous.comp
    (continuous_snd.prodMk (δ.continuous.comp continuous_fst))
  map_zero_left t := by
    change F (t, δ 0) = F (t, x)
    rw [δ.source]
  map_one_left t := by
    change F (t, δ 1) = F (t, y)
    rw [δ.target]
  prop' s t ht := by
    change F (t, δ s) = F (t, x)
    rcases ht with ht | ht
    · subst t
      rw [h₀, h₀]
    · rw [Set.mem_singleton_iff] at ht
      subst t
      rw [h₁, h₁]

/-- The slice homotopy is precisely evaluation along the actual parameter path. -/
theorem sliceHomotopy_apply (F : C(unitInterval × X, G))
    (h₀ : ∀ x, F (0, x) = 1) (h₁ : ∀ x, F (1, x) = 1)
    {x y : X} (δ : Path x y) (s t : unitInterval) :
    sliceHomotopy F h₀ h₁ δ (s, t) = F (t, δ s) := rfl

/-- Loop slices joined by an actual path of parameters have the same intrinsic class. -/
theorem classOf_slice_eq_of_path (F : C(unitInterval × X, G))
    (h₀ : ∀ x, F (0, x) = 1) (h₁ : ∀ x, F (1, x) = 1)
    {x y : X} (δ : Path x y) : classOf (slice F h₀ x) = classOf (slice F h₀ y) :=
  classOf_eq_of_homotopic _ _ ⟨sliceHomotopy F h₀ h₁ δ⟩

/-- Jointly continuous loops over a locally path connected parameter space
have locally constant intrinsic classes, with no topology imposed on the quotient. -/
theorem classOf_locallyConstant [LocallyPathConnectedSpace X]
    (F : C(unitInterval × X, G))
    (h₀ : ∀ x, F (0, x) = 1) (h₁ : ∀ x, F (1, x) = 1) :
    IsLocallyConstant (fun x => classOf (slice F h₀ x)) := by
  apply (IsLocallyConstant.iff_exists_open _).mpr
  intro x
  refine ⟨pathComponent x, IsOpen.pathComponent x, mem_pathComponent_self x, ?_⟩
  intro y hy
  exact (classOf_slice_eq_of_path F h₀ h₁ (mem_pathComponent_iff.mp hy).somePath).symm

/-- A closed slice belongs to the literal kernel of the intrinsic endpoint homomorphism. -/
def kernelSlice (F : C(unitInterval × X, G))
    (h₀ : ∀ x, F (0, x) = 1) (h₁ : ∀ x, F (1, x) = 1) (x : X) :
    (projection (G := G)).ker :=
  ⟨classOf (slice F h₀ x), h₁ x⟩

/-- The kernel-valued slice retains precisely the original intrinsic loop class. -/
theorem kernelSlice_val (F : C(unitInterval × X, G))
    (h₀ : ∀ x, F (0, x) = 1) (h₁ : ∀ x, F (1, x) = 1) (x : X) :
    (kernelSlice F h₀ h₁ x).val = classOf (slice F h₀ x) := rfl

/-- The actual endpoint-kernel classes are locally constant over a locally path connected parameter space. -/
theorem kernelSlice_locallyConstant [LocallyPathConnectedSpace X]
    (F : C(unitInterval × X, G))
    (h₀ : ∀ x, F (0, x) = 1) (h₁ : ∀ x, F (1, x) = 1) :
    IsLocallyConstant (kernelSlice F h₀ h₁) :=
  IsLocallyConstant.desc _ Subtype.val (classOf_locallyConstant F h₀ h₁) Subtype.val_injective

/-- The intrinsic loop class is locally constant on any actual open parameter subset of a locally path connected base. -/
theorem classOf_locallyConstant_open [LocallyPathConnectedSpace X]
    (U : TopologicalSpace.Opens X) (F : C(unitInterval × ↥U, G))
    (h₀ : ∀ x, F (0, x) = 1) (h₁ : ∀ x, F (1, x) = 1) :
    IsLocallyConstant (fun x => classOf (slice F h₀ x)) := by
  let : LocallyPathConnectedSpace U := U.isOpen.locallyPathConnectedSpace
  exact classOf_locallyConstant F h₀ h₁

/-- The endpoint-kernel class is locally constant on actual open overlaps, using only the base's local path connectivity. -/
theorem kernelSlice_locallyConstant_open [LocallyPathConnectedSpace X]
    (U : TopologicalSpace.Opens X) (F : C(unitInterval × ↥U, G))
    (h₀ : ∀ x, F (0, x) = 1) (h₁ : ∀ x, F (1, x) = 1) :
    IsLocallyConstant (kernelSlice F h₀ h₁) := by
  let : LocallyPathConnectedSpace U := U.isOpen.locallyPathConnectedSpace
  exact kernelSlice_locallyConstant F h₀ h₁

end FoliationQM.BasedPathGroup
