module
public import FoliationQM.GeometricSpinObstruction
public import FoliationQM.TangentLorentzTetradCover

/-!
# The refinement obstruction for metric-derived geometric frames

Source scope: the geometric Spin-frame component of v13 `prop:takabayasi`
(A/C/D, component only). The independent metric, signature, orientation
and future data determine a tetrad cover. On each refined overlap its
Lorentz transitions agree with those extracted from the geometric frame
atlas. This identifies eventual vanishing for the tetrad pair lifts with
existence of a smooth geometric Spin lift with its own source charts.
The tangent specialization derives the tangent-bundle regularity from a
base with one additional derivative.
-/

@[expose] public section
noncomputable section
open Bundle Set
open scoped Manifold Topology
namespace FoliationQM.MetricSpinObstructionCriterion
open CliffordSpinCoverRefinement CliffordSpinTransitionLifts CliffordSpinCocycleCorrection
open GeometricLorentzFrameBundle SmoothLorentzFrameBundle GeometricSpinObstruction
open SignEventualObstruction SpinSignCohomology SpinSignDefectRepresentative

section Metric

variable {E H B F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace B] [ChartedSpace H B]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {V : B → Type*}
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)]
  [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle ℝ F V]
  {n : WithTop ℕ∞} [ContMDiffVectorBundle n F V I] [IsManifold I n B]

/-- On any refined tetrad cover, the extracted frame-atlas transitions and the original tetrad transitions have equivalent Spin lifting conditions because they agree on every true refined pair overlap. -/
theorem refinement_lift_congr {ι κ : Type*} (T : SmoothLorentzTetrad.Data (F := F) I V ι n)
    (R : Refinement T.domain κ) :
    HasSpinCocycleLift (lorentzData (AdaptedGeometricSpinLift.lorentzData (smoothAtlas T)) R) ↔
      HasSpinCocycleLift (lorentzData (SmoothLorentzTetrad.lorentzData T) R) :=
  GeometricSpinStructure.hasSpinCocycleLift_congr rfl (fun i j x hi hj =>
    principalAtlas_transition T (R.parent i) (R.parent j) x (R.subset i hi) (R.subset j hj))

variable (D : SmoothLorentzMetricGeometry.Data (F := F) I V n)
open MetricLorentzTetradCover

/-- The geometric frame bundle of an independent smooth metric geometry has a smooth Spin lift with its own charts exactly when the metric-derived tetrad transitions lift on some point-indexed open refinement. -/
theorem nonempty_iff_refinement_lift :
    Nonempty (SmoothLift I (I.prod LorentzManifold.model) (principalAtlas (tetradData D)) n) ↔
      ∃ R : Refinement (tetradData D).domain B,
        HasSpinCocycleLift (lorentzData (SmoothLorentzTetrad.lorentzData (tetradData D)) R) := by
  apply (GeometricSpinObstruction.nonempty_iff_refinement_lift (smoothAtlas (tetradData D))).trans
  exact exists_congr (fun R => refinement_lift_congr (tetradData D) R)

/-- For normalized pair lifts of the metric-derived tetrad transitions, a smooth geometric Spin lift exists exactly when their sign class vanishes after refinement. -/
theorem nonempty_iff_vanishes (P : PairLifts (SmoothLorentzTetrad.lorentzData (tetradData D))) :
    Nonempty (SmoothLift I (I.prod LorentzManifold.model) (principalAtlas (tetradData D)) n) ↔
      Vanishes (classOf (representative P)) :=
  (nonempty_iff_refinement_lift D).trans (vanishes_iff_exists_refinement_lift P).symm

/-- Simple connectivity and local path connectivity of every nonempty derived pair overlap construct the pair lifts used in the eventual sign-vanishing criterion for the geometric frame bundle. -/
theorem nonempty_iff_constructed_vanishes
    (hsc : ∀ i j, Nonempty ↥(CliffordSpinPairLiftConstruction.pairOverlap
      (SmoothLorentzTetrad.lorentzData (tetradData D)) i j) → SimplyConnectedSpace
        ↥(CliffordSpinPairLiftConstruction.pairOverlap (SmoothLorentzTetrad.lorentzData (tetradData D)) i j))
    (hlpc : ∀ i j, Nonempty ↥(CliffordSpinPairLiftConstruction.pairOverlap
      (SmoothLorentzTetrad.lorentzData (tetradData D)) i j) → LocallyPathConnectedSpace
        ↥(CliffordSpinPairLiftConstruction.pairOverlap (SmoothLorentzTetrad.lorentzData (tetradData D)) i j)) :
    Nonempty (SmoothLift I (I.prod LorentzManifold.model) (principalAtlas (tetradData D)) n) ↔
      Vanishes (classOf (representative (CliffordSpinPairLiftConstruction.pairLifts
        (SmoothLorentzTetrad.lorentzData (tetradData D)) hsc hlpc))) :=
  nonempty_iff_vanishes D _

end Metric

section Tangent

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [TopologicalSpace M] [ChartedSpace H M]
  (n : WithTop ℕ∞) [IsManifold I (n + 1) M] (D : TangentLorentzTetradCover.Data (M := M) I n)
open TangentLorentzTetradCover

/-- On a C^(n+1) base with independent tangent metric geometry, a C^n smooth geometric Spin lift exists exactly when the constructed tangent tetrad transitions lift on a refinement. -/
theorem tangent_nonempty_iff_refinement_lift :
    letI : IsManifold I 1 M := .of_le (n := n + 1) le_add_self
    letI : ContMDiffVectorBundle n E (TangentSpace I : M → Type _) I :=
      TangentBundle.contMDiffVectorBundle
    Nonempty (SmoothLift I (I.prod LorentzManifold.model) (principalAtlas (tetradData I n D)) n) ↔
      ∃ R : Refinement (tetradData I n D).domain M,
        HasSpinCocycleLift (lorentzData (SmoothLorentzTetrad.lorentzData (tetradData I n D)) R) := by
  let : IsManifold I 1 M := .of_le (n := n + 1) le_add_self
  let : IsManifold I n M := .of_le (n := n + 1) le_self_add
  let : ContMDiffVectorBundle n E (TangentSpace I : M → Type _) I :=
    TangentBundle.contMDiffVectorBundle
  exact nonempty_iff_refinement_lift D

/-- A smooth Spin lift of the actual tangent frame bundle exists exactly when the sign class of its normalized tetrad pair lifts vanishes after refinement, deriving C^n tangent-bundle regularity from the C^(n+1) base. -/
theorem tangent_nonempty_iff_vanishes :
    letI : IsManifold I 1 M := .of_le (n := n + 1) le_add_self
    letI : ContMDiffVectorBundle n E (TangentSpace I : M → Type _) I :=
      TangentBundle.contMDiffVectorBundle
    ∀ P : PairLifts (SmoothLorentzTetrad.lorentzData (tetradData I n D)),
      Nonempty (SmoothLift I (I.prod LorentzManifold.model) (principalAtlas (tetradData I n D)) n) ↔
        Vanishes (classOf (representative P)) := by
  let : IsManifold I 1 M := .of_le (n := n + 1) le_add_self
  let : IsManifold I n M := .of_le (n := n + 1) le_self_add
  let : ContMDiffVectorBundle n E (TangentSpace I : M → Type _) I :=
    TangentBundle.contMDiffVectorBundle
  intro P
  exact nonempty_iff_vanishes D P

/-- On the actual tangent bundle, simple connectivity and local path connectivity of all nonempty metric-derived pair overlaps give a constructed sign class whose eventual vanishing is equivalent to smooth Spin existence. -/
theorem tangent_nonempty_iff_constructed_vanishes :
    letI : IsManifold I 1 M := .of_le (n := n + 1) le_add_self
    letI : ContMDiffVectorBundle n E (TangentSpace I : M → Type _) I :=
      TangentBundle.contMDiffVectorBundle
    let L := SmoothLorentzTetrad.lorentzData (tetradData I n D)
    ∀ (hsc : ∀ i j, Nonempty ↥(CliffordSpinPairLiftConstruction.pairOverlap L i j) →
          SimplyConnectedSpace ↥(CliffordSpinPairLiftConstruction.pairOverlap L i j))
      (hlpc : ∀ i j, Nonempty ↥(CliffordSpinPairLiftConstruction.pairOverlap L i j) →
          LocallyPathConnectedSpace ↥(CliffordSpinPairLiftConstruction.pairOverlap L i j)),
      Nonempty (SmoothLift I (I.prod LorentzManifold.model) (principalAtlas (tetradData I n D)) n) ↔
        Vanishes (classOf (representative (CliffordSpinPairLiftConstruction.pairLifts L hsc hlpc))) := by
  let : IsManifold I 1 M := .of_le (n := n + 1) le_add_self
  let : IsManifold I n M := .of_le (n := n + 1) le_self_add
  let : ContMDiffVectorBundle n E (TangentSpace I : M → Type _) I :=
    TangentBundle.contMDiffVectorBundle
  intro _ hsc hlpc
  exact nonempty_iff_constructed_vanishes D hsc hlpc

end Tangent
end FoliationQM.MetricSpinObstructionCriterion
