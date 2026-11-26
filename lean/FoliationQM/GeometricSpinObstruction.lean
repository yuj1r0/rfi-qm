module
public import FoliationQM.SmoothSpinLiftRefinement
public import FoliationQM.RefinedGeometricPrincipalAtlas
public import FoliationQM.SignEventualObstruction

/-!
# Smooth geometric Spin lifts and vanishing after refinement

Source scope: the geometric Spin-frame component of v13 `prop:takabayasi`.
A geometric lift has its own smooth principal charts and a smooth map
into the original Lorentz total space. Its charts may be chosen
independently of the target cover. The criterion first constructs a
genuine cocycle on refined opens, then compares this construction to
the actual sign class when normalized pair lifts are available.
-/

@[expose] public section
noncomputable section
open scoped Manifold
namespace FoliationQM.GeometricSpinObstruction
open CliffordSpinMap CliffordSpinLorentzSmooth LorentzMatrixGroup
open CliffordSpinCoverRefinement CliffordSpinCocycleCorrection

universe u
variable {E EP H HP : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup EP] [NormedSpace ℝ EP] [TopologicalSpace H] [TopologicalSpace HP]
  {B : Type u} [TopologicalSpace B] [ChartedSpace H B]
  {P ι : Type*} [TopologicalSpace P] [ChartedSpace HP P] {frameProj : P → B}

/-- A smooth principal Spin lift over the original Lorentz total space, with independently indexed source charts. -/
structure SmoothLift (I : ModelWithCorners ℝ E H) (KP : ModelWithCorners ℝ EP HP)
    (L : GeometricPrincipalAtlas.Data (G := ProperFutureLorentz) frameProj ι) (n : WithTop ℕ∞) where
  /-- The carrier of the principal Spin bundle. -/
  Carrier : Type u
  /-- The source charts have their own index family. -/
  Index : Type u
  /-- The original source topology. -/
  [topology : TopologicalSpace Carrier]
  /-- The source uses the local model of a principal Spin bundle. -/
  [charted : ChartedSpace (ModelProd H CliffordSpinManifold.Model) Carrier]
  /-- Regularity of the source manifold at the specified order. -/
  [manifold : IsManifold (I.prod spinModel) n Carrier]
  /-- The base projection of the Spin bundle. -/
  proj : Carrier → B
  /-- Actual principal Spin charts and right action. -/
  atlas : GeometricPrincipalAtlas.Data (G := Spin) proj Index
  /-- The forward charts and their inverses are smooth on their domains. -/
  smoothAtlas : GeometricPrincipalSmoothAtlas.Data I spinModel (I.prod spinModel) atlas n
  /-- The physical equivariant map preserves the base of the original Lorentz bundle. -/
  map : GeometricSpinLift.Map atlas L
  /-- Smoothness of the geometric map in its original source and target structures. -/
  smooth_map : ContMDiff (I.prod spinModel) KP n map

attribute [instance] SmoothLift.topology SmoothLift.charted SmoothLift.manifold

variable {I : ModelWithCorners ℝ E H} {KP : ModelWithCorners ℝ EP HP}
  {L : GeometricPrincipalAtlas.Data (G := ProperFutureLorentz) frameProj ι} {n : WithTop ℕ∞}
  (LM : GeometricPrincipalSmoothAtlas.Data I lorentzModel KP L n)

/-- A lift adapted to a base-indexed refinement gives a smooth physical lift into the original target with its independently indexed source atlas. -/
def ofRefined (R : Refinement (AdaptedGeometricSpinLift.lorentzData LM).domain B)
    (A : GeometricSpinStructure.Lift I (RefinedGeometricPrincipalAtlas.restrictedAtlas L R) n) :
    SmoothLift I KP L n where
  Carrier := A.Carrier
  Index := B
  proj := A.proj
  atlas := A.atlas
  smoothAtlas := A.smoothAtlas
  map := RefinedGeometricPrincipalAtlas.originalMap R A
  smooth_map := RefinedGeometricPrincipalAtlas.originalMap_smooth LM R A

include LM in
/-- The physical map of a smooth Spin lift is a two-sheeted covering and a local diffeomorphism of the original total spaces. -/
theorem smoothLift_two_sheeted (A : SmoothLift I KP L n) :
    IsCoveringMap A.map ∧ IsLocalDiffeomorph (I.prod spinModel) KP n A.map ∧
      ∀ p : P, Nat.card {q : A.Carrier // A.map q = p} = 2 :=
  ⟨A.map.isCoveringMap, A.map.isLocalDiffeomorph A.smoothAtlas LM A.smooth_map, A.map.fiber_card⟩

variable [IsManifold I n B]

/-- An independently charted smooth geometric Spin lift exists exactly when the original Lorentz cocycle lifts on some refinement indexed by base points. -/
theorem nonempty_iff_refinement_lift :
    Nonempty (SmoothLift I KP L n) ↔
      ∃ R : Refinement (AdaptedGeometricSpinLift.lorentzData LM).domain B,
        HasSpinCocycleLift (lorentzData (AdaptedGeometricSpinLift.lorentzData LM) R) := by
  constructor
  · rintro ⟨A⟩
    exact SmoothSpinLiftRefinement.exists_refinement_of_map A.map LM A.smoothAtlas A.smooth_map
  · rintro ⟨R, hR⟩
    obtain ⟨A⟩ := (RefinedGeometricPrincipalAtlas.nonempty_lift_iff LM R).mpr hR
    exact ⟨ofRefined LM R A⟩

/-- For normalized pair lifts of the extracted Lorentz transitions, geometric Spin existence is equivalent to their fixed-cover sign class becoming neutral after refinement. -/
theorem nonempty_iff_vanishes
    (P₀ : CliffordSpinTransitionLifts.PairLifts (AdaptedGeometricSpinLift.lorentzData LM)) :
    Nonempty (SmoothLift I KP L n) ↔
      SignEventualObstruction.Vanishes (SpinSignCohomology.classOf
        (SpinSignDefectRepresentative.representative P₀)) :=
  (nonempty_iff_refinement_lift LM).trans
    (SignEventualObstruction.vanishes_iff_exists_refinement_lift P₀).symm

end FoliationQM.GeometricSpinObstruction
