module
public import FoliationQM.AdaptedGeometricSpinLift
public import FoliationQM.CliffordSpinPrincipalBundle
public import FoliationQM.PrincipalAtlasReconstruction
public import FoliationQM.GeometricSpinSmoothCover
public import FoliationQM.GeometricSpinCocycleCongruence

/-!
# Geometric Spin structures and the same-cover cocycle criterion

Source scope: the geometric Spin-structure component of v13 `prop:takabayasi`.
A lift consists of an actual independently topologized and charted principal
Spin total space, a continuous physical equivariant map to the original Lorentz
bundle, and adaptation to the specified cover. Smoothness, the covering property,
local smooth inverses, and the projected transition cocycle are conclusions.
Conversely a genuine same-cover Spin cocycle constructs such geometric data,
using the proved reconstruction of the original Lorentz bundle. No arbitrary
existence or removal of a sign obstruction is asserted.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Function Bundle Topology
open scoped Manifold
namespace FoliationQM.GeometricSpinStructure
open CliffordSpinMap CliffordSpinLorentz CliffordSpinLorentzSmooth LorentzMatrixGroup
open CliffordSpinPrincipalBundle PrincipalAtlasReconstruction

universe u
variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {B : Type u} [TopologicalSpace B] [ChartedSpace H B]
  {P : Type*} [TopologicalSpace P] {frameProj : P → B} {ι : Type*}

/-- A geometric Spin lift adapted to a specified Lorentz cover, with its own actual carrier, topology and smooth principal atlas; no covering or cocycle conclusion is assumed. -/
structure Lift (I : ModelWithCorners ℝ E H)
    (L : GeometricPrincipalAtlas.Data (G := ProperFutureLorentz) frameProj ι)
    (n : WithTop ℕ∞) where
  /-- The original carrier of geometric Spin frames. -/
  Carrier : Type u
  /-- Its original topology. -/
  [topology : TopologicalSpace Carrier]
  /-- Its independently specified charted-space structure. -/
  [charted : ChartedSpace (ModelProd H CliffordSpinManifold.Model) Carrier]
  /-- Regularity of the original source atlas at exactly the stated order. -/
  [manifold : IsManifold (I.prod spinModel) n Carrier]
  /-- The actual principal projection. -/
  proj : Carrier → B
  /-- Actual principal trivializations and right action over the specified cover. -/
  atlas : GeometricPrincipalAtlas.Data (G := Spin) proj ι
  /-- Smoothness of those original trivializations and their inverses. -/
  smoothAtlas : GeometricPrincipalSmoothAtlas.Data I spinModel (I.prod spinModel) atlas n
  /-- The continuous, base-preserving, physically equivariant geometric map. -/
  map : GeometricSpinLift.Map atlas L
  /-- Exact original chart domains and canonical unit-section compatibility. -/
  adapted : AdaptedGeometricSpinLift.Adapted map

attribute [instance] Lift.topology Lift.charted Lift.manifold

variable {I : ModelWithCorners ℝ E H}
  {L : GeometricPrincipalAtlas.Data (G := ProperFutureLorentz) frameProj ι}
  {n : WithTop ℕ∞}

namespace Lift
variable (A : Lift I L n)

/-- Every supplied geometric Spin structure has a genuine covering projection in its original topology. -/
theorem isCoveringMap : IsCoveringMap A.map := A.map.isCoveringMap

/-- The actual geometric projection has precisely two preimages of each original Lorentz frame. -/
theorem fiber_card (p : P) : Nat.card {q : A.Carrier // A.map q = p} = 2 :=
  A.map.fiber_card p

variable {EP HP : Type*} [NormedAddCommGroup EP] [NormedSpace ℝ EP]
  [TopologicalSpace HP] {KP : ModelWithCorners ℝ EP HP} [ChartedSpace HP P]
  (LM : GeometricPrincipalSmoothAtlas.Data I lorentzModel KP L n)

include A LM

/-- Smoothness of the actual geometric projection follows from adaptation and the independent smooth principal charts. -/
theorem contMDiff : ContMDiff (I.prod spinModel) KP n A.map :=
  A.adapted.contMDiff A.smoothAtlas LM

/-- The geometric projection has genuine smooth local inverses for the original source and target atlases. -/
theorem isLocalDiffeomorph : IsLocalDiffeomorph (I.prod spinModel) KP n A.map :=
  A.map.isLocalDiffeomorph A.smoothAtlas LM (A.contMDiff LM)

/-- A geometric Spin structure yields a genuine smooth Clifford cocycle lift on exactly the specified Lorentz cover. -/
theorem hasSpinCocycleLift : CliffordSpinCocycleCorrection.HasSpinCocycleLift
    (AdaptedGeometricSpinLift.lorentzData LM) :=
  A.adapted.hasSpinCocycleLift A.smoothAtlas LM
end Lift

section Construction
variable {EP HP : Type*} [NormedAddCommGroup EP] [NormedSpace ℝ EP]
  [TopologicalSpace HP] {KP : ModelWithCorners ℝ EP HP} [ChartedSpace HP P]
  (LM : GeometricPrincipalSmoothAtlas.Data I lorentzModel KP L n)
  [IsManifold I n B]
  {S : CliffordSpinPolarCocycle.Data I B ι n}
  (C : Compatible S (cocycleData LM))

/-- A compatible Clifford cocycle maps to the original Lorentz total space through the inverse genuine reconstruction diffeomorphism. -/
def constructedMap : GeometricSpinLift.Map
    (PrincipalCocycleBundle.geometricData (spinData S)) L where
  toFun q := (reconstructionDiffeomorph LM).symm (C.geometricMap q)
  continuous_toFun := (reconstructionDiffeomorph LM).symm.continuous.comp
    C.continuous_geometricMap
  proj q := by
    have h := reconstructionDiffeomorph_proj LM
      ((reconstructionDiffeomorph LM).symm (C.geometricMap q))
    rw [(reconstructionDiffeomorph LM).apply_symm_apply] at h
    exact h.symm.trans (C.geometricMap_proj q)
  equivariant q s := by
    apply (reconstructionDiffeomorph LM).injective
    change reconstructionDiffeomorph LM ((reconstructionDiffeomorph LM).symm
      (C.geometricMap (PrincipalCocycleBundle.rightAct (spinData S) q s))) =
      reconstructionDiffeomorph LM (L.right
        ((reconstructionDiffeomorph LM).symm (C.geometricMap q)) (lorentzHom s))
    rw [(reconstructionDiffeomorph LM).apply_symm_apply, reconstructionDiffeomorph_right,
      (reconstructionDiffeomorph LM).apply_symm_apply]
    exact C.geometricMap_right q s

/-- Reconstruction maps an original canonical geometric unit section to the genuine unit section of its extracted principal cocycle bundle. -/
theorem reconstruction_localSection (i : ι) (x : B) (hx : x ∈ (L.triv i).baseSet) :
    reconstructionDiffeomorph LM (L.localSection i x) =
      (PrincipalCocycleBundle.geometricData (cocycleData LM)).localSection i x := by
  apply (PrincipalCocycleBundle.geometricData (cocycleData LM)).coordinate_injective i
  · change (reconstructionDiffeomorph LM (L.localSection i x)).proj ∈ (L.triv i).baseSet
    rw [reconstructionDiffeomorph_proj, L.proj_localSection i x hx]
    exact hx
  · exact hx
  · exact (reconstructionDiffeomorph_proj LM (L.localSection i x)).trans
      (L.proj_localSection i x hx)
  · rw [show (PrincipalCocycleBundle.geometricData (cocycleData LM)).triv i =
        (PrincipalCocycleBundle.core (cocycleData LM)).localTriv i from rfl,
      reconstructionDiffeomorph_localTriv LM i _ (by rw [L.proj_localSection i x hx]; exact hx)]
    exact congrArg Prod.snd ((L.localSection_coordinate i x hx).trans
      ((PrincipalCocycleBundle.geometricData (cocycleData LM)).localSection_coordinate i x hx).symm)

/-- The constructed physical map is adapted to the original independent Lorentz principal charts on their exact domains. -/
theorem constructedMap_adapted : AdaptedGeometricSpinLift.Adapted (constructedMap LM C) where
  domain_eq i := congrArg (fun U : ι → TopologicalSpace.Opens B => (U i : Set B)) C.domain_eq
  unit i x hx := by
    have hs : x ∈ S.domain i := by rw [C.domain_eq]; exact hx
    change (reconstructionDiffeomorph LM).symm
      (C.geometricMap ((PrincipalCocycleBundle.geometricData (spinData S)).localSection i x)) = _
    rw [C.geometricMap_localSection i x hs, ← reconstruction_localSection LM i x hx]
    exact (reconstructionDiffeomorph LM).symm_apply_apply _

/-- A genuine compatible Spin cocycle constructs an actual geometric Spin structure over the original Lorentz total space and specified cover. -/
def ofCompatible : Lift I L n where
  Carrier := SpinTotal S
  proj := Bundle.TotalSpace.proj
  atlas := PrincipalCocycleBundle.geometricData (spinData S)
  smoothAtlas := spinSmoothAtlas S
  map := constructedMap LM C
  adapted := constructedMap_adapted LM C

end Construction

section Existence
variable {EP HP : Type*} [NormedAddCommGroup EP] [NormedSpace ℝ EP]
  [TopologicalSpace HP] {KP : ModelWithCorners ℝ EP HP} [ChartedSpace HP P]
  (LM : GeometricPrincipalSmoothAtlas.Data I lorentzModel KP L n)
  [IsManifold I n B]

/-- Existence of an actual geometric Spin structure adapted to the specified independent Lorentz cover is equivalent to a genuine same-cover Clifford Spin cocycle lift of its extracted transitions. -/
theorem nonempty_lift_iff : Nonempty (Lift I L n) ↔
    CliffordSpinCocycleCorrection.HasSpinCocycleLift
      (AdaptedGeometricSpinLift.lorentzData LM) := by
  constructor
  · rintro ⟨A⟩
    exact A.hasSpinCocycleLift LM
  · rintro ⟨S, hd, hp⟩
    have C : Compatible S (cocycleData LM) :=
      { domain_eq := hd
        transition := fun i j x hi hj => hp i j x
          (by rw [← hd]; exact hi) (by rw [← hd]; exact hj) }
    exact ⟨ofCompatible LM C⟩

/-- For supplied normalized pair lifts on the original cover, an actual adapted geometric Spin structure exists exactly when their genuine central sign defect admits a smooth correction. -/
theorem nonempty_lift_iff_correction
    (P : CliffordSpinTransitionLifts.PairLifts (AdaptedGeometricSpinLift.lorentzData LM)) :
    Nonempty (Lift I L n) ↔ ∃ b : CliffordSpinCocycleCorrection.Correction
      (AdaptedGeometricSpinLift.lorentzData LM), CliffordSpinCocycleCorrection.RemovesDefect P b :=
  (nonempty_lift_iff LM).trans (CliffordSpinCocycleCorrection.exists_correction_iff P).symm

end Existence
end FoliationQM.GeometricSpinStructure
