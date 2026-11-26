module
public import FoliationQM.ParacompactSpinLiftCriterion
public import FoliationQM.MetricSpinHOneClassification

/-!
# The native obstruction of a metric-derived frame bundle

For the geometric frame component of v13 `prop:takabayasi`, the actual metric,
orientation and future data determine a smooth frame atlas. On a paracompact
normal locally path connected base its native degree-two class detects smooth
Spin lifts, and the physical classes form the all-cover degree-one torsor when
that class vanishes.
-/

@[expose] public section
noncomputable section
open Bundle
open scoped Manifold
namespace FoliationQM.ParacompactMetricSpinCriterion
open GeometricLorentzFrameBundle SmoothLorentzFrameBundle MetricLorentzTetradCover
open CliffordSpinTransitionLifts CliffordSpinCoverRefinement CliffordSpinCocycleCorrection
open SpinAllCoverHOne

variable {E H B F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace B] [ChartedSpace H B]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {V : B → Type*}
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)]
  [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle ℝ F V]
  {n : WithTop ℕ∞} [ContMDiffVectorBundle n F V I]
  [ParacompactSpace B] [NormalSpace B] [LocallyPathConnectedSpace B]
  (D : SmoothLorentzMetricGeometry.Data (F := F) I V n)

/-- The native degree-two class of the actual bundle of oriented future metric frames. -/
def obstruction : ModTwoAllCover.GlobalH2 B :=
  ParacompactBundleObstruction.obstruction (principalAtlas (tetradData D))

variable [IsManifold I n B]

/-- The actual tetrad pair lifts also lift the transitions extracted from the frame
atlas, since the two Lorentz representatives agree on each true overlap. -/
def framePairLifts (P : PairLifts (SmoothLorentzTetrad.lorentzData (tetradData D))) :
    PairLifts (AdaptedGeometricSpinLift.lorentzData (smoothAtlas (tetradData D))) where
  transition := P.transition
  smooth_transition := P.smooth_transition
  identity := P.identity
  projection i j x hi hj :=
    (P.projection i j x hi hj).trans (principalAtlas_transition (tetradData D) i j x hi hj).symm

/-- Any normalized Spin pairs on the original metric tetrads compute the native class. -/
theorem obstruction_physical (P : PairLifts (SmoothLorentzTetrad.lorentzData (tetradData D))) :
    obstruction D = ModTwoSpinObstruction.obstruction P :=
  ParacompactSpinLiftCriterion.obstruction_physical (smoothAtlas (tetradData D)) (framePairLifts D P)

/-- Smooth lifts into the actual metric-frame space exist exactly when its native class vanishes. -/
theorem nonempty_iff :
    Nonempty (MetricSpinHOneClassification.SpinLift D) ↔ obstruction D = 0 :=
  ParacompactSpinLiftCriterion.nonempty_iff (smoothAtlas (tetradData D))

/-- Vanishing detects a cocycle lift of the metric tetrads on a point-indexed refinement. -/
theorem zero_iff_refinement_lift : obstruction D = 0 ↔
    ∃ R : Refinement (tetradData D).domain B,
      HasSpinCocycleLift (lorentzData (SmoothLorentzTetrad.lorentzData (tetradData D)) R) :=
  (nonempty_iff D).symm.trans (MetricSpinObstructionCriterion.nonempty_iff_refinement_lift D)

/-- The native zero class supplies the all-cover sign torsor of physical metric-frame lifts. -/
@[instance_reducible] def torsor_of_zero (hz : obstruction D = 0) :
    Torsor (GlobalH1 I B n) (MetricSpinHOneClassification.Class D) :=
  ParacompactSpinLiftCriterion.torsor_of_zero (smoothAtlas (tetradData D)) hz

/-- The metric frame bundle has exactly one physical Spin class precisely when its
native obstruction vanishes and the all-cover sign group is trivial. -/
theorem unique_iff :
    (∃! _p : MetricSpinHOneClassification.Class D, True) ↔
      obstruction D = 0 ∧ Subsingleton (GlobalH1 I B n) :=
  ParacompactSpinLiftCriterion.unique_iff (smoothAtlas (tetradData D))

/-- Choosing a lift supplied by vanishing gives degree-one coordinates for all physical lifts. -/
def basedEquiv_of_zero (hz : obstruction D = 0) :
    GlobalH1 I B n ≃ MetricSpinHOneClassification.Class D :=
  MetricSpinHOneClassification.basedEquiv D ((nonempty_iff D).mpr hz).some

/-- The neutral sign corresponds to the chosen reference lift in these coordinates. -/
theorem basedEquiv_of_zero_one (hz : obstruction D = 0) :
    basedEquiv_of_zero D hz 1 = SmoothSpinRelativeClass.physicalClass ((nonempty_iff D).mpr hz).some :=
  MetricSpinHOneClassification.basedEquiv_one D _

end FoliationQM.ParacompactMetricSpinCriterion
