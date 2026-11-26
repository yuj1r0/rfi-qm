module
public import FoliationQM.AtlasPathTransfer
public import FoliationQM.PresentedLorentzBundle
public import FoliationQM.SpinLiftAtlasChange
public import FoliationQM.GeometricIntrinsicSpinObstruction

/-!
# Spin lifts of an independently presented smooth Lorentz target

For the frame component of v13 `prop:takabayasi`, a topological
presentation of the underlying projection and action computes the
obstruction for any smooth atlas on that space. The comparison constructs
transition paths on a refinement of the given smooth charts and transports
the resulting physical lift criterion back to the original target.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.PresentedSpinCriterion
open LorentzMatrixGroup CliffordSpinLorentzSmooth GeometricSpinObstruction
open PresentedLorentzBundle RefinedGeometricPrincipalAtlas

variable {E H ET HT B T ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] [NormedAddCommGroup ET] [NormedSpace ℝ ET] [TopologicalSpace HT]
  [TopologicalSpace B] [ChartedSpace H B] [TopologicalSpace T] [ChartedSpace HT T]
  {I : ModelWithCorners ℝ E H} {K : ModelWithCorners ℝ ET HT} {n : WithTop ℕ∞} {proj : T → B}
  {C : GeometricPrincipalAtlas.Data (G := ProperFutureLorentz) proj ι}
  (CM : GeometricPrincipalSmoothAtlas.Data I lorentzModel K C n) (h : HasPresentation proj C.right)

include CM

/-- Restrict the supplied smooth charts to the domains found by comparing the two atlases. -/
theorem refinedSmoothAtlas : GeometricPrincipalSmoothAtlas.Data I lorentzModel K
    (AtlasPathTransfer.atlas h.some.atlas C) n := restrictedSmoothAtlas CM (AtlasPathTransfer.refinement h.some.atlas C)

/-- Normalized transition paths for the actual refined smooth charts, obtained from the presentation. -/
def refinedPaths :
    LorentzTransitionPaths.Family (AdaptedGeometricSpinLift.lorentzData (refinedSmoothAtlas CM h)) :=
  LorentzIntrinsicObstruction.lorentzFamily (AtlasPathTransfer.family h.some.atlas C h.some.right_eq h.some.family)

variable [LocallyPathConnectedSpace B]

/-- The refined smooth paths compute the class of the underlying presented principal space. -/
theorem obstruction_refined :
    obstruction h = LorentzIntrinsicObstruction.obstruction (refinedPaths CM h) :=
  obstruction_eq h (AtlasPathTransfer.atlas h.some.atlas C) (AtlasPathTransfer.atlas_right h.some.atlas C) _

/-- Any physical pair lifts on the original smooth atlas compute the same bundle class. -/
theorem obstruction_physical (S : CliffordSpinTransitionLifts.PairLifts (AdaptedGeometricSpinLift.lorentzData CM)) :
    obstruction h = ModTwoSpinObstruction.obstruction S := by
  let R := AtlasPathTransfer.refinement h.some.atlas C
  let U := CliffordSpinCoverRefinement.pairLifts S R
  exact (obstruction_refined CM h).trans
    ((LorentzIntrinsicObstruction.obstruction_eq_of_pairLifts (refinedPaths CM h) U).trans
      (ModTwoSpinObstruction.obstruction_refine S R U))

variable [IsManifold I n B]

/-- A genuine smooth Spin lift exists exactly when the independently presented bundle class vanishes. -/
theorem nonempty_iff : Nonempty (SmoothLift I K C n) ↔ obstruction h = 0 := by
  let e := SpinLiftAtlasChange.liftEquiv (I := I) (K := K) (n := n) (AtlasPathTransfer.atlas_right h.some.atlas C).symm
  rw [obstruction_refined CM h]
  exact e.nonempty_congr.trans (GeometricIntrinsicSpinObstruction.nonempty_iff (refinedSmoothAtlas CM h) (refinedPaths CM h))

/-- Vanishing equips the physical lift classes of the original target with their all-cover degree-one torsor. -/
@[instance_reducible] def torsor_of_zero (hz : obstruction h = 0) :
    Torsor (SpinAllCoverHOne.GlobalH1 I B n) (SmoothSpinRelativeClass.PhysicalClass I K C n) :=
  SmoothSpinHOneTorsor.torsor CM ((nonempty_iff CM h).mpr hz)

/-- The class is unique precisely when the presented obstruction vanishes and global degree one is trivial. -/
theorem unique_iff : (∃! _p : SmoothSpinRelativeClass.PhysicalClass I K C n, True) ↔
    obstruction h = 0 ∧ Subsingleton (SpinAllCoverHOne.GlobalH1 I B n) :=
  (GlobalSpinClassificationCriterion.unique_iff CM).trans (and_congr (nonempty_iff CM h) Iff.rfl)

end FoliationQM.PresentedSpinCriterion
