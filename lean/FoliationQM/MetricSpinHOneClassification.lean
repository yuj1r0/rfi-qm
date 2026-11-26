module
public import FoliationQM.MetricSpinObstructionCriterion
public import FoliationQM.GlobalSpinClassificationCriterion

/-!
# Smooth Spin lifts of the frame bundle determined by metric data

For the geometric Spin-frame component of v13 `prop:takabayasi`, the
independent bilinear metric, signature, orientation, and future data
determine a smooth tetrad cover. Existence of a smooth Spin lift of its
frame bundle is detected after refinement. Once a lift exists, the
all-cover degree-one group acts on every physical isomorphism class.
-/

@[expose] public section
noncomputable section
open Bundle
open scoped Manifold
namespace FoliationQM.MetricSpinHOneClassification
open CliffordSpinCoverRefinement CliffordSpinTransitionLifts CliffordSpinCocycleCorrection
open GeometricLorentzFrameBundle SmoothLorentzFrameBundle MetricLorentzTetradCover
open GeometricSpinObstruction SmoothSpinRelativeClass SpinAllCoverHOne
open SignEventualObstruction SpinSignCohomology SpinSignDefectRepresentative

variable {E H B F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace B] [ChartedSpace H B]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {V : B → Type*}
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)]
  [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle ℝ F V]
  {n : WithTop ℕ∞} [ContMDiffVectorBundle n F V I] [IsManifold I n B]
  (D : SmoothLorentzMetricGeometry.Data (F := F) I V n)

/-- Independently charted smooth Spin lifts into the actual metric-derived frame bundle. -/
abbrev SpinLift := SmoothLift I (I.prod LorentzManifold.model) (principalAtlas (tetradData D)) n

/-- Physical isomorphism classes of those lifts, over the original metric-derived target. -/
abbrev Class := PhysicalClass I (I.prod LorentzManifold.model) (principalAtlas (tetradData D)) n

/-- A chosen smooth lift identifies global sign cohomology with all physical lifts modulo isomorphism. -/
def basedEquiv (A : SpinLift D) : GlobalH1 I B n ≃ Class D :=
  SmoothSpinHOneTorsor.basedEquiv (smoothAtlas (tetradData D)) (physicalClass A)

/-- The inverse coordinate of a metric-frame lift class is its global transition difference from the reference. -/
theorem basedEquiv_symm_apply (A : SpinLift D) (q : Class D) :
    (basedEquiv D A).symm q =
      GlobalSpinDisplacement.displacement (smoothAtlas (tetradData D)) (physicalClass A) q := rfl

/-- The neutral sign gives the original reference lift up to physical isomorphism. -/
theorem basedEquiv_one (A : SpinLift D) : basedEquiv D A 1 = physicalClass A :=
  SmoothSpinHOneTorsor.basedEquiv_one _ _

/-- Exactly one all-cover class takes any given metric-frame Spin class to another. -/
theorem existsUnique_act (p q : Class D) :
    ∃! g : GlobalH1 I B n, SmoothSpinHOneTorsor.act (smoothAtlas (tetradData D)) g p = q :=
  SmoothSpinHOneTorsor.existsUnique_act _ _ _

/-- A genuine Spin lift of the derived tetrad transitions on some refinement supplies the metric-frame torsor. -/
@[instance_reducible] def torsor_of_refinement
    (h : ∃ R : Refinement (tetradData D).domain B,
      HasSpinCocycleLift (lorentzData (SmoothLorentzTetrad.lorentzData (tetradData D)) R)) :
    Torsor (GlobalH1 I B n) (Class D) :=
  SmoothSpinHOneTorsor.torsor (smoothAtlas (tetradData D))
    ((MetricSpinObstructionCriterion.nonempty_iff_refinement_lift D).mpr h)

/-- Eventual vanishing of the degree-two sign for supplied metric-tetrad pair lifts gives the degree-one torsor. -/
@[instance_reducible] def torsor_of_vanishes
    (P : PairLifts (SmoothLorentzTetrad.lorentzData (tetradData D)))
    (h : Vanishes (classOf (representative P))) : Torsor (GlobalH1 I B n) (Class D) :=
  SmoothSpinHOneTorsor.torsor (smoothAtlas (tetradData D))
    ((MetricSpinObstructionCriterion.nonempty_iff_vanishes D P).mpr h)

/-- A unique physical class exists precisely when a refinement lifts and the global first sign group is trivial. -/
theorem unique_iff_refinement :
    (∃! _p : Class D, True) ↔
      (∃ R : Refinement (tetradData D).domain B,
        HasSpinCocycleLift (lorentzData (SmoothLorentzTetrad.lorentzData (tetradData D)) R)) ∧
        Subsingleton (GlobalH1 I B n) :=
  (GlobalSpinClassificationCriterion.unique_iff (smoothAtlas (tetradData D))).trans
    (and_congr_left fun _ => MetricSpinObstructionCriterion.nonempty_iff_refinement_lift D)

/-- For given normalized pair lifts, unique existence is eventual degree-two vanishing together with trivial degree one. -/
theorem unique_iff_vanishes (P : PairLifts (SmoothLorentzTetrad.lorentzData (tetradData D))) :
    (∃! _p : Class D, True) ↔
      Vanishes (classOf (representative P)) ∧ Subsingleton (GlobalH1 I B n) :=
  (GlobalSpinClassificationCriterion.unique_iff (smoothAtlas (tetradData D))).trans
    (and_congr_left fun _ => MetricSpinObstructionCriterion.nonempty_iff_vanishes D P)

/-- Construct the normalized pair lifts when each nonempty tetrad pair overlap is simply connected
and locally path connected, yielding the exact unique-existence test from the metric geometry. -/
theorem unique_iff_constructed_vanishes :
    let L := SmoothLorentzTetrad.lorentzData (tetradData D)
    ∀ (hsc : ∀ i j, Nonempty ↥(CliffordSpinPairLiftConstruction.pairOverlap L i j) →
          SimplyConnectedSpace ↥(CliffordSpinPairLiftConstruction.pairOverlap L i j))
      (hlpc : ∀ i j, Nonempty ↥(CliffordSpinPairLiftConstruction.pairOverlap L i j) →
          LocallyPathConnectedSpace ↥(CliffordSpinPairLiftConstruction.pairOverlap L i j)),
      (∃! _p : Class D, True) ↔ Vanishes (classOf (representative
        (CliffordSpinPairLiftConstruction.pairLifts L hsc hlpc))) ∧ Subsingleton (GlobalH1 I B n) := by
  intro L hsc hlpc
  exact unique_iff_vanishes D (CliffordSpinPairLiftConstruction.pairLifts L hsc hlpc)

end FoliationQM.MetricSpinHOneClassification
