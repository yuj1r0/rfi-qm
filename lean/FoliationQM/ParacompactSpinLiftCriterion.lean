module
public import FoliationQM.ParacompactBundleObstruction
public import FoliationQM.ParacompactSmoothAtlasPaths
public import FoliationQM.PresentedSpinCriterion

/-!
# Physical smooth Spin lifts of an ordinary Lorentz atlas

For the frame component of v13 `prop:takabayasi`, the native class
constructed from the ordinary principal atlas detects genuine smooth Spin
lifts. Independent pair lifts, when available, compute the same class.
Vanishing gives the all-cover degree-one torsor. The criterion also
compares existence between two atlas regularities on the same projected
Lorentz space.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.ParacompactSpinLiftCriterion
open LorentzMatrixGroup CliffordSpinLorentzSmooth GeometricSpinObstruction SmoothSpinRelativeClass
open ParacompactBundleObstruction SpinAllCoverHOne

variable {E H ET HT B T ι κ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] [NormedAddCommGroup ET] [NormedSpace ℝ ET] [TopologicalSpace HT]
  [TopologicalSpace B] [ChartedSpace H B] [TopologicalSpace T] [ChartedSpace HT T]
  [ParacompactSpace B] [NormalSpace B] [LocallyPathConnectedSpace B]
  {I : ModelWithCorners ℝ E H} {K : ModelWithCorners ℝ ET HT} {n m : WithTop ℕ∞} {proj : T → B}
  {A : GeometricPrincipalAtlas.Data (G := ProperFutureLorentz) proj ι}
  (AM : GeometricPrincipalSmoothAtlas.Data I lorentzModel K A n)

include AM

/-- The normalized paths of the actual restricted smooth charts compute the native class of the atlas. -/
theorem eq_refined_paths : obstruction A =
    LorentzIntrinsicObstruction.obstruction (ParacompactSmoothAtlasPaths.paths AM) :=
  eq_constructed A

/-- Physical Spin pair lifts on the original chart overlaps compute the same native obstruction. -/
theorem obstruction_physical
    (S : CliffordSpinTransitionLifts.PairLifts (AdaptedGeometricSpinLift.lorentzData AM)) :
    obstruction A = ModTwoSpinObstruction.obstruction S :=
  PresentedSpinCriterion.obstruction_physical AM (ParacompactLorentzPresentation.hasPresentation A) S

variable [hB : IsManifold I n B]
include hB

/-- A genuine smooth Spin lift of the original geometric target exists precisely when its native class vanishes. -/
theorem nonempty_iff : Nonempty (SmoothLift I K A n) ↔ obstruction A = 0 :=
  PresentedSpinCriterion.nonempty_iff AM (ParacompactLorentzPresentation.hasPresentation A)

/-- Nonvanishing is exactly emptiness of the physical class space. -/
theorem isEmpty_iff : IsEmpty (PhysicalClass I K A n) ↔ obstruction A ≠ 0 :=
  not_nonempty_iff.symm.trans
    ((GlobalSpinClassificationCriterion.nonempty_physical_iff.trans (nonempty_iff AM)).not)

/-- The physical classes form a torsor under all-cover degree one when the native class vanishes. -/
@[instance_reducible] def torsor_of_zero (hz : obstruction A = 0) :
    Torsor (GlobalH1 I B n) (PhysicalClass I K A n) :=
  PresentedSpinCriterion.torsor_of_zero AM (ParacompactLorentzPresentation.hasPresentation A) hz

/-- Choosing a lift from vanishing gives coordinates for the physical classes in the all-cover sign group. -/
def equiv_of_zero (hz : obstruction A = 0) : GlobalH1 I B n ≃ PhysicalClass I K A n :=
  GlobalSpinClassificationCriterion.equiv_of_nonempty AM ((nonempty_iff AM).mpr hz)

/-- There is exactly one physical class precisely when the obstruction vanishes and all-cover degree one is trivial. -/
theorem unique_iff : (∃! _p : PhysicalClass I K A n, True) ↔
    obstruction A = 0 ∧ Subsingleton (GlobalH1 I B n) :=
  PresentedSpinCriterion.unique_iff AM (ParacompactLorentzPresentation.hasPresentation A)

/-- Smooth existence agrees between independent atlas regularities on the same projected right-action space. -/
theorem nonempty_iff_other_order [IsManifold I m B]
    {C : GeometricPrincipalAtlas.Data (G := ProperFutureLorentz) proj κ}
    (CM : GeometricPrincipalSmoothAtlas.Data I lorentzModel K C m) (hr : A.right = C.right) :
    Nonempty (SmoothLift I K A n) ↔ Nonempty (SmoothLift I K C m) := by
  rw [nonempty_iff AM, nonempty_iff CM, eq_of_right_eq A C hr]

end FoliationQM.ParacompactSpinLiftCriterion
