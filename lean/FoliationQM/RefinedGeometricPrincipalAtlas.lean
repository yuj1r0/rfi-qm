module
public import FoliationQM.GeometricSpinStructure
public import FoliationQM.CliffordSpinCoverRefinement

/-!
# Restricting an independently charted geometric principal atlas

Source scope: the geometric Spin lifting component of v13 `prop:takabayasi`.
On each refined open, both maps of its parent trivialization are retained.
The restricted atlas therefore has the parent transitions on the original
total space. For a Lorentz atlas this identifies geometric restriction
with restriction of the extracted Lorentz cocycle. The physical map of
a Spin lift adapted to the refined opens lands in the original atlas.
-/

@[expose] public section
noncomputable section
open Set Bundle Topology
open scoped Manifold
namespace FoliationQM.RefinedGeometricPrincipalAtlas
open CliffordSpinCoverRefinement

section Atlas
variable {B P G ι κ : Type*} [TopologicalSpace B] [TopologicalSpace P]
  [TopologicalSpace G] [Group G] {proj : P → B}
  (A : GeometricPrincipalAtlas.Data (G := G) proj ι)

/-- The original base sets of a geometric atlas, packaged as open subsets. -/
def domains (i : ι) : TopologicalSpace.Opens B := ⟨(A.triv i).baseSet, (A.triv i).open_baseSet⟩

/-- Restrict the original trivialization and its inverse to the precise refined open set. -/
def restrictedTriv (R : Refinement (domains A) κ) (a : κ) : Trivialization G proj := by
  let e := A.triv (R.parent a)
  have sub : (R.domain a : Set B) ⊆ e.baseSet := R.subset a
  exact
    { toFun := e
      invFun := e.toOpenPartialHomeomorph.symm
      source := proj ⁻¹' R.domain a
      target := (R.domain a : Set B) ×ˢ univ
      map_source' := fun p hp => by
        refine ⟨?_, mem_univ _⟩
        rw [e.coe_fst' (sub hp)]
        exact hp
      map_target' := fun z hz => by
        change proj (e.toOpenPartialHomeomorph.symm z) ∈ R.domain a
        rw [e.proj_symm_apply' (sub hz.1)]
        exact hz.1
      left_inv' := fun _ hp => e.toOpenPartialHomeomorph.left_inv (e.mem_source.mpr (sub hp))
      right_inv' := fun _ hz => e.apply_symm_apply' (sub hz.1)
      open_source := (R.domain a).isOpen.preimage A.continuous_proj
      open_target := (R.domain a).isOpen.prod isOpen_univ
      continuousOn_toFun := e.toOpenPartialHomeomorph.continuousOn.mono
        (fun _ hp => e.mem_source.mpr (sub hp))
      continuousOn_invFun := e.toOpenPartialHomeomorph.continuousOn_symm.mono
        (fun _ hz => e.mem_target.mpr (sub hz.1))
      baseSet := R.domain a
      open_baseSet := (R.domain a).isOpen
      source_eq := rfl
      target_eq := rfl
      proj_toFun := fun _ hp => e.coe_fst' (sub hp) }

/-- The refined principal atlas uses the original projection and right action. -/
def restrictedAtlas (R : Refinement (domains A) κ) : GeometricPrincipalAtlas.Data (G := G) proj κ where
  triv := restrictedTriv A R
  covers := R.covers
  right := A.right
  proj_right := A.proj_right
  right_local a p g hp := A.right_local (R.parent a) p g (R.subset a hp)

/-- The chart base sets of the restricted actual atlas are exactly the prescribed refined opens. -/
theorem domains_restrictedAtlas (R : Refinement (domains A) κ) :
    domains (restrictedAtlas A R) = R.domain := rfl

/-- The restricted chart uses the literal forward map of its parent chart. -/
theorem restrictedAtlas_triv_apply (R : Refinement (domains A) κ) (a : κ) (p : P) :
    (restrictedAtlas A R).triv a p = A.triv (R.parent a) p := rfl

/-- The restricted inverse chart uses the literal inverse map of its parent. -/
theorem restrictedAtlas_symm_apply (R : Refinement (domains A) κ) (a : κ) (z : B × G) :
    ((restrictedAtlas A R).triv a).toOpenPartialHomeomorph.symm z =
      (A.triv (R.parent a)).toOpenPartialHomeomorph.symm z := rfl

/-- The group acts on the actual total space by the original right action after restriction. -/
theorem restrictedAtlas_right (R : Refinement (domains A) κ) :
    (restrictedAtlas A R).right = A.right := rfl

/-- In each smaller chart its canonical local section is the original parent's section. -/
theorem restrictedAtlas_localSection (R : Refinement (domains A) κ) (a : κ) :
    (restrictedAtlas A R).localSection a = A.localSection (R.parent a) := rfl

/-- The transition representatives of the restricted geometric atlas are the original parent transitions. -/
theorem restrictedAtlas_transition (R : Refinement (domains A) κ) (a b : κ) :
    (restrictedAtlas A R).transition a b = A.transition (R.parent a) (R.parent b) := rfl
end Atlas

section Smooth
variable {EB EG EP HB HG HP B G P ι κ : Type*}
  [NormedAddCommGroup EB] [NormedSpace ℝ EB] [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [NormedAddCommGroup EP] [NormedSpace ℝ EP]
  [TopologicalSpace HB] [TopologicalSpace HG] [TopologicalSpace HP]
  [TopologicalSpace B] [ChartedSpace HB B] [TopologicalSpace G] [ChartedSpace HG G] [Group G]
  [TopologicalSpace P] [ChartedSpace HP P]
  {I : ModelWithCorners ℝ EB HB} {J : ModelWithCorners ℝ EG HG} {K : ModelWithCorners ℝ EP HP}
  {proj : P → B} {A : GeometricPrincipalAtlas.Data (G := G) proj ι} {n : WithTop ℕ∞}

/-- Restricting the true source and target of each parent chart preserves its original smoothness order. -/
theorem restrictedSmoothAtlas (AM : GeometricPrincipalSmoothAtlas.Data I J K A n)
    (R : Refinement (domains A) κ) :
    GeometricPrincipalSmoothAtlas.Data I J K (restrictedAtlas A R) n where
  smooth_triv a := (AM.smooth_triv (R.parent a)).mono
    (fun _ hp => (A.triv (R.parent a)).mem_source.mpr (R.subset a hp))
  smooth_symm a := (AM.smooth_symm (R.parent a)).mono
    (fun _ hz => (A.triv (R.parent a)).mem_target.mpr (R.subset a hz.1))
end Smooth

section Lorentz
open CliffordSpinLorentzSmooth LorentzMatrixGroup
universe u
variable {E H EP HP P ι κ : Type*} {B : Type u}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  [NormedAddCommGroup EP] [NormedSpace ℝ EP] [TopologicalSpace HP]
  [TopologicalSpace B] [ChartedSpace H B] [TopologicalSpace P] [ChartedSpace HP P]
  {I : ModelWithCorners ℝ E H} {KP : ModelWithCorners ℝ EP HP}
  {proj : P → B} {L : GeometricPrincipalAtlas.Data (G := ProperFutureLorentz) proj ι} {n : WithTop ℕ∞}

/-- Extracting Lorentz transitions after geometric atlas restriction gives exactly the restricted original cocycle. -/
theorem lorentzData_restricted (LM : GeometricPrincipalSmoothAtlas.Data I lorentzModel KP L n)
    (R : Refinement (domains L) κ) :
    AdaptedGeometricSpinLift.lorentzData (restrictedSmoothAtlas LM R) =
      CliffordSpinCoverRefinement.lorentzData (AdaptedGeometricSpinLift.lorentzData LM) R := rfl

/-- A geometric Spin lift adapted to these refined charts exists exactly when their restricted Lorentz cocycle lifts. -/
theorem nonempty_lift_iff [IsManifold I n B]
    (LM : GeometricPrincipalSmoothAtlas.Data I lorentzModel KP L n) (R : Refinement (domains L) κ) :
    Nonempty (GeometricSpinStructure.Lift I (restrictedAtlas L R) n) ↔
      CliffordSpinCocycleCorrection.HasSpinCocycleLift
        (CliffordSpinCoverRefinement.lorentzData (AdaptedGeometricSpinLift.lorentzData LM) R) :=
  GeometricSpinStructure.nonempty_lift_iff (restrictedSmoothAtlas LM R)

/-- An adapted lift on a refinement supplies a physical equivariant map to the original geometric target. -/
def originalMap (R : Refinement (domains L) κ)
    (A : GeometricSpinStructure.Lift I (restrictedAtlas L R) n) : GeometricSpinLift.Map A.atlas L where
  toFun := A.map
  continuous_toFun := A.map.continuous_toFun
  proj := A.map.proj
  equivariant := A.map.equivariant

/-- The physical map into the original target agrees pointwise with the actual map of the adapted lift. -/
theorem originalMap_apply (R : Refinement (domains L) κ)
    (A : GeometricSpinStructure.Lift I (restrictedAtlas L R) n) (q : A.Carrier) :
    originalMap R A q = A.map q := rfl

/-- The physical map into the original total space is smooth at the given order. -/
theorem originalMap_smooth (LM : GeometricPrincipalSmoothAtlas.Data I lorentzModel KP L n)
    (R : Refinement (domains L) κ) (A : GeometricSpinStructure.Lift I (restrictedAtlas L R) n) :
    ContMDiff (I.prod spinModel) KP n (originalMap R A) :=
  A.contMDiff (restrictedSmoothAtlas LM R)

/-- This map to the original target is a covering and a local diffeomorphism with two points in each fiber. -/
theorem originalMap_two_sheeted (LM : GeometricPrincipalSmoothAtlas.Data I lorentzModel KP L n)
    (R : Refinement (domains L) κ) (A : GeometricSpinStructure.Lift I (restrictedAtlas L R) n) :
    IsCoveringMap (originalMap R A) ∧
      IsLocalDiffeomorph (I.prod spinModel) KP n (originalMap R A) ∧
      ∀ p : P, Nat.card {q : A.Carrier // originalMap R A q = p} = 2 :=
  ⟨A.isCoveringMap, A.isLocalDiffeomorph (restrictedSmoothAtlas LM R), A.fiber_card⟩
end Lorentz
end FoliationQM.RefinedGeometricPrincipalAtlas
