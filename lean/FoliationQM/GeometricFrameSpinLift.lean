module
public import FoliationQM.SmoothLorentzFrameBundle
public import FoliationQM.CliffordSpinPrincipalBundle
public import FoliationQM.GeometricSpinSmoothCover
public import FoliationQM.AdaptedGeometricSpinLift
public import FoliationQM.GeometricSpinStructure

/-!
# Actual geometric frame Spin lifts from compatible Clifford cocycles

A genuine Clifford Spin cocycle compatible with the Lorentz transitions
calculated from supplied smooth tetrads produces a map into the literal
geometric frame total space. That target retains its independently induced
vector-point topology and direct tetrad atlas. The map preserves the base,
is smooth and equivariant, and is a genuine covering with exactly the two
Clifford signs as each fiber. Its local formula reconstructs actual frame
vectors from the original tetrad using the physical Lorentz matrix.

The supplied compatibility is an actual cocycle-lifting condition. This
construction does not assert that arbitrary Lorentz bundles have Spin lifts.
For the independently defined adapted geometric Spin-structure package,
existence is proved equivalent to a same-cover Spin cocycle lift of the
literal original tetrad transitions, and hence to the explicit central-sign
correction condition. Pairwise simple-connectivity hypotheses are retained
precisely when using the constructed pair lifts.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Bundle Function
open scoped Manifold Topology Matrix.Norms.Operator
namespace FoliationQM.GeometricFrameSpinLift
open GeometricLorentzFrameBundle SmoothLorentzFrameBundle
open CliffordSpinPrincipalBundle CliffordSpinMap CliffordSpinLorentz
open CliffordSpinLorentzSmooth LorentzMatrixGroup

variable {E H B F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace B] [ChartedSpace H B]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : B → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle ℝ F V]
  {ι : Type*} {n : WithTop ℕ∞} [ContMDiffVectorBundle n F V I]
  (D : SmoothLorentzTetrad.Data (F := F) I V ι n) [IsManifold I n B]
  {S : CliffordSpinPolarCocycle.Data I B ι n}
  (C : Compatible S (principalData D))

/-- The actual geometric frame lift composes the physical principal Spin map with the inverse independently proved frame reconstruction diffeomorphism. -/
def geometricMap : GeometricSpinLift.Map
    (PrincipalCocycleBundle.geometricData (spinData S)) (principalAtlas D) where
  toFun p := (frameDiffeomorph D).symm (C.geometricMap p)
  continuous_toFun := (frameDiffeomorph D).symm.continuous.comp C.continuous_geometricMap
  proj p := (frameDiffeomorph_symm_proj D (C.geometricMap p)).trans (C.geometricMap_proj p)
  equivariant p s := by
    change (frameDiffeomorph D).symm (C.geometricMap (PrincipalCocycleBundle.rightAct (spinData S) p s)) =
      rightAction D ((frameDiffeomorph D).symm (C.geometricMap p)) (lorentzHom s)
    apply (frameDiffeomorph D).injective
    change frameDiffeomorph D ((frameDiffeomorph D).symm (C.geometricMap
      (PrincipalCocycleBundle.rightAct (spinData S) p s))) =
      frameDiffeomorph D (rightAction D ((frameDiffeomorph D).symm (C.geometricMap p)) (lorentzHom s))
    rw [(frameDiffeomorph D).apply_symm_apply, frameDiffeomorph_rightAction,
      (frameDiffeomorph D).apply_symm_apply]
    exact C.geometricMap_right p s

/-- The geometric Spin lift has exactly the actual inverse-frame-reconstruction formula. -/
theorem geometricMap_apply (p : SpinTotal S) :
    geometricMap D C p = (frameDiffeomorph D).symm (C.geometricMap p) := rfl

/-- The geometric Spin projection preserves the original base point of each actual Spin frame. -/
theorem geometricMap_proj (p : SpinTotal S) : (geometricMap D C p).proj = p.proj :=
  (geometricMap D C).proj p

/-- The actual geometric Spin projection intertwines the genuine principal Spin right action and the original Lorentz action on geometric bases. -/
theorem geometricMap_right (p : SpinTotal S) (s : Spin) :
    geometricMap D C (PrincipalCocycleBundle.rightAct (spinData S) p s) =
      rightAction D (geometricMap D C p) (lorentzHom s) :=
  (geometricMap D C).equivariant p s

/-- The actual geometric map is continuous for the unchanged core Spin topology and independently induced frame topology. -/
theorem continuous_geometricMap : Continuous (geometricMap D C) :=
  (geometricMap D C).continuous_toFun

/-- The actual map to geometric frames is smooth for the independent source atlas and direct tetrad target atlas. -/
theorem contMDiff_geometricMap :
    ContMDiff (I.prod spinModel) (I.prod lorentzModel) n (geometricMap D C) :=
  (frameDiffeomorph D).symm.contMDiff.comp C.contMDiff_geometricMap

/-- Every actual metric-compatible oriented future frame has a preimage under the compatible geometric Spin lift. -/
theorem geometricMap_surjective : Surjective (geometricMap D C) :=
  (geometricMap D C).surjective

/-- Equality of actual projected geometric frames is exactly equality or right multiplication by the literal negative Clifford unit. -/
theorem geometricMap_image_eq_iff (p q : SpinTotal S) :
    geometricMap D C q = geometricMap D C p ↔ q = p ∨
      q = PrincipalCocycleBundle.rightAct (spinData S) p CliffordSpinEquivalence.negativeOne :=
  (geometricMap D C).image_eq_iff p q

/-- Every actual geometric frame has exactly two Spin-frame preimages under the constructed map. -/
theorem geometricMap_fiber_card (p : Total D) :
    Nat.card {q : SpinTotal S // geometricMap D C q = p} = 2 :=
  (geometricMap D C).fiber_card p

/-- The actual map into the independently topologized geometric frame bundle is a genuine covering, by the verified local product-cover argument. -/
theorem geometricMap_isCoveringMap : IsCoveringMap (geometricMap D C) :=
  (geometricMap D C).isCoveringMap

/-- Each actual geometric frame has an evenly covered neighborhood with precisely two sheets. -/
theorem geometricMap_isEvenlyCovered_two (p : Total D) :
    IsEvenlyCovered (geometricMap D C) p (Fin 2) :=
  (geometricMap D C).isEvenlyCovered_two p

/-- On every genuine tetrad chart, the physical Clifford homomorphism is exactly the local fiber formula of the geometric frame projection. -/
theorem geometricMap_localTriv (i : ι) (p : SpinTotal S) (hp : p.proj ∈ D.domain i) :
    localTriv D i (geometricMap D C p) =
      (p.proj, lorentzHom (((PrincipalCocycleBundle.core (spinData S)).localTriv i p).2)) := by
  rw [geometricMap_apply, frameDiffeomorph_symm_localTriv D i (C.geometricMap p)
    (by rw [C.geometricMap_proj]; exact hp)]
  apply C.geometricMap_localTriv
  rw [C.domain_eq]
  exact hp

/-- The projected actual frame is literally the inverse geometric tetrad chart at the physical Lorentz image of its original Spin chart coordinate. -/
theorem geometricMap_eq_localFromProd (i : ι) (p : SpinTotal S) (hp : p.proj ∈ D.domain i) :
    geometricMap D C p = localFromProd D i
      (p.proj, lorentzHom (((PrincipalCocycleBundle.core (spinData S)).localTriv i p).2)) := by
  calc
    _ = localFromProd D i (localToProd D i (geometricMap D C p)) :=
      (localFromProd_localToProd D i _).symm
    _ = _ := congrArg (localFromProd D i) (geometricMap_localTriv D C i p hp)

/-- The canonical unit Spin section projects to the original actual tetrad frame on its genuine chart domain. -/
theorem geometricMap_localSection (i : ι) (x : B) (hx : x ∈ D.domain i) :
    geometricMap D C ((PrincipalCocycleBundle.geometricData (spinData S)).localSection i x) =
      (⟨x, SmoothLorentzTetrad.frameAt D i x hx⟩ : Total D) := by
  have hs : x ∈ S.domain i := by rw [C.domain_eq]; exact hx
  have hp := (PrincipalCocycleBundle.geometricData (spinData S)).proj_localSection i x hs
  change ((PrincipalCocycleBundle.geometricData (spinData S)).localSection i x).proj = x at hp
  rw [geometricMap_eq_localFromProd D C i _ (by rw [hp]; exact hx)]
  change localFromProd D i
    (_, lorentzHom (((PrincipalCocycleBundle.geometricData (spinData S)).triv i
      ((PrincipalCocycleBundle.geometricData (spinData S)).localSection i x)).2)) = _
  rw [(PrincipalCocycleBundle.geometricData (spinData S)).localSection_coordinate i x hs]
  simp only [map_one]
  change localFromProd D i
    (((PrincipalCocycleBundle.geometricData (spinData S)).localSection i x).proj, 1) = _
  rw [hp]
  simp only [localFromProd, GeometricLorentzFrame.rightAction_one, referenceFrame_eq D i x hx]

/-- Canonical Spin sections and actual geometric unit sections are adapted to the constructed physical projection on precisely their original chart domains. -/
theorem geometricMap_adapted (i : ι) (x : B) (hx : x ∈ D.domain i) :
    geometricMap D C ((PrincipalCocycleBundle.geometricData (spinData S)).localSection i x) =
      (principalAtlas D).localSection i x := by
  rw [geometricMap_localSection D C i x hx, localSection_eq D i x hx]

/-- Each projected frame vector, as an actual point of the original vector bundle, is the physical Lorentz-matrix linear combination of the original tetrad vectors. -/
theorem geometricMap_vectorPoint (i : ι) (p : SpinTotal S) (hp : p.proj ∈ D.domain i)
    (a : Fin 4) :
    (⟨(geometricMap D C p).proj, (geometricMap D C p).snd.basis a⟩ : TotalSpace F V) =
      ⟨p.proj, ∑ b : Fin 4,
        SpinLorentzAction.lorentzMatrix
          (toMatrix (((PrincipalCocycleBundle.core (spinData S)).localTriv i p).2)).val b a •
            D.tetrad i b p.proj⟩ := by
  rw [geometricMap_eq_localFromProd D C i p hp]
  apply congrArg (fun v : V p.proj => (⟨p.proj, v⟩ : TotalSpace F V))
  rw [localFromProd_vector D i _ hp, lorentzHom_matrix]

/-- The actual geometric frame projection is a local diffeomorphism for its independently defined source and target atlases. -/
theorem geometricMap_isLocalDiffeomorph :
    IsLocalDiffeomorph (I.prod spinModel) (I.prod lorentzModel) n (geometricMap D C) :=
  (geometricMap D C).isLocalDiffeomorph (spinSmoothAtlas S) (smoothAtlas D)
    (contMDiff_geometricMap D C)

/-- A compatible genuine Clifford cocycle produces a smooth two-sheeted covering of the literal geometric frame bundle, with no topology or atlas transported to force this conclusion. -/
theorem geometricMap_smooth_two_sheeted :
    IsCoveringMap (geometricMap D C) ∧
      IsLocalDiffeomorph (I.prod spinModel) (I.prod lorentzModel) n (geometricMap D C) ∧
      ∀ p : Total D, Nat.card {q : SpinTotal S // geometricMap D C q = p} = 2 :=
  ⟨geometricMap_isCoveringMap D C, geometricMap_isLocalDiffeomorph D C,
    geometricMap_fiber_card D C⟩

/-- The actual constructed geometric frame lift is adapted to the original tetrad cover: its chart domains agree and its canonical Spin unit sections project to the original tetrad unit sections. -/
theorem adapted : AdaptedGeometricSpinLift.Adapted (geometricMap D C) where
  domain_eq i := congrArg (fun U : ι → TopologicalSpace.Opens B => (U i : Set B)) C.domain_eq
  unit := geometricMap_adapted D C

/-- An actual smooth Spin structure adapted to the original geometric tetrad cover exists exactly when the literal tetrad-derived Lorentz transitions have a same-cover genuine Clifford Spin cocycle lift. -/
theorem nonempty_lift_iff :
    Nonempty (GeometricSpinStructure.Lift I (principalAtlas D) n) ↔
      CliffordSpinCocycleCorrection.HasSpinCocycleLift (SmoothLorentzTetrad.lorentzData D) := by
  exact (GeometricSpinStructure.nonempty_lift_iff (smoothAtlas D)).trans
    (GeometricSpinStructure.hasSpinCocycleLift_congr rfl
      (fun i j x hi hj => principalAtlas_transition D i j x hi hj))

/-- The explicit central-sign defect correction for any supplied normalized pair lifts is equivalent to existence of an actual smooth geometric Spin structure adapted to the original tetrad cover. -/
theorem nonempty_lift_iff_correction
    (P : CliffordSpinTransitionLifts.PairLifts (SmoothLorentzTetrad.lorentzData D)) :
    Nonempty (GeometricSpinStructure.Lift I (principalAtlas D) n) ↔
      ∃ b : CliffordSpinCocycleCorrection.Correction (SmoothLorentzTetrad.lorentzData D),
        CliffordSpinCocycleCorrection.RemovesDefect P b :=
  (nonempty_lift_iff D).trans (CliffordSpinCocycleCorrection.exists_correction_iff P).symm

/-- On explicitly simply connected and locally path-connected nonempty pair overlaps, the actually constructed pair lifts give the exact sign-correction criterion for an actual geometric Spin structure adapted to the original tetrad cover. -/
theorem nonempty_lift_iff_constructed_correction
    (hsc : ∀ i j, Nonempty ↥(CliffordSpinPairLiftConstruction.pairOverlap
      (SmoothLorentzTetrad.lorentzData D) i j) → SimplyConnectedSpace
        ↥(CliffordSpinPairLiftConstruction.pairOverlap (SmoothLorentzTetrad.lorentzData D) i j))
    (hlpc : ∀ i j, Nonempty ↥(CliffordSpinPairLiftConstruction.pairOverlap
      (SmoothLorentzTetrad.lorentzData D) i j) → LocallyPathConnectedSpace
        ↥(CliffordSpinPairLiftConstruction.pairOverlap (SmoothLorentzTetrad.lorentzData D) i j)) :
    Nonempty (GeometricSpinStructure.Lift I (principalAtlas D) n) ↔
      ∃ b : CliffordSpinCocycleCorrection.Correction (SmoothLorentzTetrad.lorentzData D),
        CliffordSpinCocycleCorrection.RemovesDefect
          (CliffordSpinPairLiftConstruction.pairLifts (SmoothLorentzTetrad.lorentzData D) hsc hlpc) b :=
  (nonempty_lift_iff D).trans
    (CliffordSpinCocycleCorrection.hasSpinCocycleLift_iff_constructed_correction
      (SmoothLorentzTetrad.lorentzData D) hsc hlpc)

end FoliationQM.GeometricFrameSpinLift
