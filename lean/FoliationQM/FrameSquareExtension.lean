module
public import FoliationQM.GeometricPrincipalAtlas
public import Mathlib.Topology.Homotopy.Path

/-!
# Actual frame fields extending a prescribed square boundary

For the geometric Spin-frame component of v13 `prop:takabayasi`, an
actual principal chart converts a continuous frame field over a
parameterized base square into a group-valued nullhomotopy. The field
is a section of the pullback bundle along that square. The square is
not assumed embedded, and no section on its image, smooth extension,
or cellular structure is claimed. Whole-square chart containment is
an explicit hypothesis of the comparison.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.FrameSquareExtension
open GeometricPrincipalAtlas

variable {B P G ι : Type*} [TopologicalSpace B] [TopologicalSpace P]
  [TopologicalSpace G] [Group G] {proj : P → B}

/-- An actual continuous frame field over a parameterized base square,
with the given loop along the initial edge and the chart unit section
along the other three edges. This is a section of the pullback bundle. -/
structure Filling (A : Data (G := G) proj ι) (i : ι)
    (σ : C(unitInterval × unitInterval, B)) (γ : Path (1 : G) 1) where
  /-- The actual field takes values in the original total space. -/
  map : C(unitInterval × unitInterval, P)
  /-- Every field value lies over the specified parameterized base point. -/
  proj_map : ∀ z, proj (map z) = σ z
  /-- The initial edge has the prescribed actual group-coordinate loop. -/
  initial : ∀ s, map (0, s) =
    (A.triv i).toOpenPartialHomeomorph.symm (σ (0, s), γ s)
  /-- The final edge is the actual chart unit section. -/
  final : ∀ s, map (1, s) = A.localSection i (σ (1, s))
  /-- The bottom edge is the actual chart unit section. -/
  bottom : ∀ t, map (t, 0) = A.localSection i (σ (t, 0))
  /-- The top edge is the actual chart unit section. -/
  top : ∀ t, map (t, 1) = A.localSection i (σ (t, 1))

variable (A : Data (G := G) proj ι) (i : ι)
  (σ : C(unitInterval × unitInterval, B)) (γ : Path (1 : G) 1)

/-- Actual fillings are determined by their values in the original total space. -/
theorem filling_ext {F K : Filling A i σ γ} (h : ∀ z, F.map z = K.map z) : F = K := by
  have hm : F.map = K.map := ContinuousMap.ext h
  cases F
  cases K
  cases hm
  rfl

variable (hσ : ∀ z, σ z ∈ (A.triv i).baseSet)

/-- Inverse trivialization turns a based nullhomotopy into an actual
continuous field over the entire given parameterized square. -/
def ofHomotopy (H : γ.Homotopy (Path.refl 1)) : Filling A i σ γ where
  map := ⟨fun z => (A.triv i).toOpenPartialHomeomorph.symm (σ z, H z),
    (A.triv i).toOpenPartialHomeomorph.continuousOn_symm.comp_continuous
      (σ.continuous.prodMk H.continuous) (fun z => (A.triv i).mem_target.mpr (hσ z))⟩
  proj_map z := (A.triv i).proj_symm_apply' (hσ z)
  initial s := by
    change (A.triv i).toOpenPartialHomeomorph.symm (σ (0, s), H (0, s)) = _
    rw [H.apply_zero]
    rfl
  final s := by
    change (A.triv i).toOpenPartialHomeomorph.symm (σ (1, s), H (1, s)) = _
    rw [H.apply_one]
    rfl
  bottom t := by
    change (A.triv i).toOpenPartialHomeomorph.symm (σ (t, 0), H (t, 0)) = _
    rw [H.source]
    rfl
  top t := by
    change (A.triv i).toOpenPartialHomeomorph.symm (σ (t, 1), H (t, 1)) = _
    rw [H.target]
    rfl

/-- The constructed field is the inverse chart applied to the actual
base square and the supplied nullhomotopy at every parameter value. -/
theorem ofHomotopy_map (H : γ.Homotopy (Path.refl 1)) (z : unitInterval × unitInterval) :
    (ofHomotopy A i σ γ hσ H).map z =
      (A.triv i).toOpenPartialHomeomorph.symm (σ z, H z) := rfl

/-- Actual chart coordinates recover a based nullhomotopy from a
continuous filling whose entire base square lies in this chart. -/
def toHomotopy (F : Filling A i σ γ) : γ.Homotopy (Path.refl 1) where
  toFun z := (A.triv i (F.map z)).2
  continuous_toFun := continuous_snd.comp
    ((A.triv i).toOpenPartialHomeomorph.continuousOn.comp_continuous F.map.continuous
      (fun z => (A.triv i).mem_source.mpr ((F.proj_map z).symm ▸ hσ z)))
  map_zero_left s := by
    rw [F.initial, (A.triv i).apply_symm_apply' (hσ (0, s))]
    rfl
  map_one_left s := by
    rw [F.final, A.localSection_coordinate i _ (hσ (1, s))]
    rfl
  prop' t s hs := by
    change (A.triv i (F.map (t, s))).2 = γ s
    rcases hs with hs | hs
    · subst s
      rw [F.bottom, A.localSection_coordinate i _ (hσ (t, 0))]
      exact γ.source.symm
    · rw [Set.mem_singleton_iff] at hs
      subst s
      rw [F.top, A.localSection_coordinate i _ (hσ (t, 1))]
      exact γ.target.symm

/-- Every recovered homotopy value is the actual group coordinate of
the original filling, rather than a separately chosen group map. -/
theorem toHomotopy_apply (F : Filling A i σ γ) (z : unitInterval × unitInterval) :
    toHomotopy A i σ γ hσ F z = (A.triv i (F.map z)).2 := rfl

/-- Recovering coordinates from the constructed field retains the
entire supplied nullhomotopy. -/
theorem toHomotopy_ofHomotopy (H : γ.Homotopy (Path.refl 1)) :
    toHomotopy A i σ γ hσ (ofHomotopy A i σ γ hσ H) = H := by
  apply Path.Homotopy.coeFn_injective
  funext z
  exact congrArg Prod.snd ((A.triv i).apply_symm_apply' (hσ z))

/-- Reconstructing from chart coordinates retains every actual frame
of the original filling over the parameterized square. -/
theorem ofHomotopy_toHomotopy (F : Filling A i σ γ) :
    ofHomotopy A i σ γ hσ (toHomotopy A i σ γ hσ F) = F := by
  apply filling_ext A i σ γ
  intro z
  change (A.triv i).toOpenPartialHomeomorph.symm (σ z, (A.triv i (F.map z)).2) = F.map z
  rw [← F.proj_map z]
  exact (A.triv i).symm_apply_mk_proj ((A.triv i).mem_source.mpr
    ((F.proj_map z).symm ▸ hσ z))

/-- The actual fields with these four boundary conditions are in
bijection with based nullhomotopies of the given coordinate loop. -/
def homotopyEquiv : Filling A i σ γ ≃ γ.Homotopy (Path.refl 1) where
  toFun := toHomotopy A i σ γ hσ
  invFun := ofHomotopy A i σ γ hσ
  left_inv := ofHomotopy_toHomotopy A i σ γ hσ
  right_inv := toHomotopy_ofHomotopy A i σ γ hσ

include hσ in
/-- The prescribed actual boundary frame field extends over the
parameterized square exactly when its chart-coordinate loop is
based nullhomotopic, assuming whole-square chart containment. -/
theorem nonempty_iff : Nonempty (Filling A i σ γ) ↔ γ.Homotopic (Path.refl 1) :=
  (homotopyEquiv A i σ γ hσ).nonempty_congr

end FoliationQM.FrameSquareExtension
