module
public import FoliationQM.ContractibleLorentzObstruction
public import FoliationQM.MetricSpinHOneClassification

/-!
# A constructed intrinsic obstruction for metric-derived frame bundles

For the geometric component of v13 `prop:takabayasi`, independent
metric, signature, orientation and future data determine actual smooth
tetrads in the original vector bundle. Standard contractibility of their
nonempty pair overlaps constructs the required joint Lorentz paths and
hence an independent native Cech class. Its vanishing detects smooth
Spin lifts of the original metric frame target, and supplies the proved
all-cover H1 torsor. No path family or pair lift is supplied separately.
Suitable-cover existence and the conventional real-bundle w2 remain
outside this statement; base local path connectedness is explicit.
-/

@[expose] public section
noncomputable section
open Bundle
open scoped Manifold
namespace FoliationQM.MetricContractibleSpinObstruction
open GeometricLorentzFrameBundle SmoothLorentzFrameBundle MetricLorentzTetradCover
open GeometricSpinObstruction SpinAllCoverHOne

variable {E H B F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace B] [ChartedSpace H B]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {V : B → Type*}
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)]
  [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle ℝ F V]
  {n : WithTop ℕ∞} [ContMDiffVectorBundle n F V I]
  (D : SmoothLorentzMetricGeometry.Data (F := F) I V n)

/-- The actual smooth Lorentz transitions of the independently constructed metric tetrads. -/
abbrev transitions : CliffordSpinLorentzTransitions.Data I B B n :=
  SmoothLorentzTetrad.lorentzData (tetradData D)

/-- The geometric hypothesis concerns exactly the nonempty pair overlaps of the computed metric cover. -/
abbrev PairContractible : Prop := ContractibleLorentzObstruction.PairContractible (transitions D)

/-- Actual joint Lorentz paths are constructed from metric-overlap contractibility. -/
def paths (h : PairContractible D) : LorentzTransitionPaths.Family (transitions D) :=
  ContractibleLorentzObstruction.paths (transitions D) h

variable [LocallyPathConnectedSpace B]

/-- The native intrinsic class on the original metric-derived tetrad cover. -/
def fixedClass (h : PairContractible D) : ModTwoCohomology.H2 (transitions D).domain :=
  ContractibleLorentzObstruction.fixedClass (transitions D) h

/-- The independent all-cover mod-two class of the actual metric-derived transitions. -/
def obstruction (h : PairContractible D) : ModTwoAllCover.GlobalH2 B :=
  ContractibleLorentzObstruction.obstruction (transitions D) h

/-- Any supplied normalized joint paths compute the same constructed metric obstruction. -/
theorem obstruction_eq_family (h : PairContractible D)
    (P : LorentzTransitionPaths.Family (transitions D)) :
    obstruction D h = LorentzIntrinsicObstruction.obstruction P :=
  ContractibleLorentzObstruction.obstruction_eq (transitions D) h P

/-- Any actual normalized Spin pair lifts compute the independent constructed metric class. -/
theorem obstruction_eq_physical (h : PairContractible D)
    (S : CliffordSpinTransitionLifts.PairLifts (transitions D)) :
    obstruction D h = ModTwoSpinObstruction.obstruction S :=
  ContractibleLorentzObstruction.obstruction_eq_physical (transitions D) h S

variable [IsManifold I n B]

/-- Vanishing on the original cover is exactly existence of an adapted geometric
Spin lift into the actual metric-derived frame bundle. -/
theorem adapted_nonempty_iff (h : PairContractible D) :
    Nonempty (GeometricSpinStructure.Lift I (principalAtlas (tetradData D)) n) ↔
      fixedClass D h = 0 :=
  (MetricGeometricSpinStructure.nonempty_lift_iff D).trans
    (ContractibleLorentzObstruction.fixed_zero_iff (transitions D) h).symm

/-- The global constructed class vanishes precisely when the actual metric frame
bundle admits a smooth Spin lift with its own source charts. -/
theorem nonempty_iff (h : PairContractible D) :
    Nonempty (MetricSpinHOneClassification.SpinLift D) ↔ obstruction D h = 0 :=
  (MetricSpinObstructionCriterion.nonempty_iff_refinement_lift D).trans
    (ContractibleLorentzObstruction.zero_iff_refinement (transitions D) h).symm

/-- The original metric-frame physical Spin classes form the all-cover H1 torsor
as soon as the constructed independent degree-two class vanishes. -/
@[instance_reducible] def torsor_of_zero (h : PairContractible D) (hz : obstruction D h = 0) :
    Torsor (GlobalH1 I B n) (MetricSpinHOneClassification.Class D) :=
  SmoothSpinHOneTorsor.torsor (smoothAtlas (tetradData D)) ((nonempty_iff D h).mpr hz)

/-- Exactly one metric-frame physical Spin class exists iff the constructed obstruction
vanishes and the independent all-cover degree-one group is trivial. -/
theorem unique_iff (h : PairContractible D) :
    (∃! _p : MetricSpinHOneClassification.Class D, True) ↔
      obstruction D h = 0 ∧ Subsingleton (GlobalH1 I B n) :=
  (GlobalSpinClassificationCriterion.unique_iff (smoothAtlas (tetradData D))).trans
    (and_congr_left fun _ => nonempty_iff D h)

end FoliationQM.MetricContractibleSpinObstruction
