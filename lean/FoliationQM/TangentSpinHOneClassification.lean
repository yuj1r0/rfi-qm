module
public import FoliationQM.MetricSpinHOneClassification

/-!
# The degree-one classification for actual tangent Spin structures

For the geometric Spin-frame component of v13 `prop:takabayasi`, the
original tangent bundle of a C^(n+1) manifold has C^n bundle charts.
The independent tangent metric, signature, orientation, and future data
therefore determine a C^n frame target. On this target the existence
test for the degree-two sign and the classification by degree-one signs
use the same geometric Spin lifts.
-/

@[expose] public section
noncomputable section
open Bundle
open scoped Manifold
namespace FoliationQM.TangentSpinHOneClassification
open CliffordSpinCoverRefinement CliffordSpinTransitionLifts CliffordSpinCocycleCorrection
open TangentLorentzTetradCover GeometricLorentzFrameBundle SmoothLorentzFrameBundle
open SpinAllCoverHOne SmoothSpinRelativeClass GeometricSpinObstruction
open SignEventualObstruction SpinSignCohomology SpinSignDefectRepresentative

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [TopologicalSpace M] [ChartedSpace H M]
  (n : WithTop ℕ∞) [IsManifold I (n + 1) M] (D : Data (M := M) I n)

/-- Smooth Spin lifts of the oriented future frame bundle of the original tangent spaces. -/
abbrev SpinLift :=
  letI : IsManifold I 1 M := .of_le (n := n + 1) le_add_self
  letI : IsManifold I n M := .of_le (n := n + 1) le_self_add
  letI : ContMDiffVectorBundle n E (TangentSpace I : M → Type _) I :=
    TangentBundle.contMDiffVectorBundle
  SmoothLift I (I.prod LorentzManifold.model) (principalAtlas (tetradData I n D)) n

/-- Physical isomorphism classes of the geometric lifts of this tangent-frame target. -/
abbrev Class :=
  letI : IsManifold I 1 M := .of_le (n := n + 1) le_add_self
  letI : IsManifold I n M := .of_le (n := n + 1) le_self_add
  letI : ContMDiffVectorBundle n E (TangentSpace I : M → Type _) I :=
    TangentBundle.contMDiffVectorBundle
  PhysicalClass I (I.prod LorentzManifold.model) (principalAtlas (tetradData I n D)) n

/-- The Lorentz transitions of the tetrads constructed from the tangent metric geometry. -/
abbrev transitions : CliffordSpinLorentzTransitions.Data I M M n :=
  letI : IsManifold I 1 M := .of_le (n := n + 1) le_add_self
  letI : IsManifold I n M := .of_le (n := n + 1) le_self_add
  letI : ContMDiffVectorBundle n E (TangentSpace I : M → Type _) I :=
    TangentBundle.contMDiffVectorBundle
  SmoothLorentzTetrad.lorentzData (tetradData I n D)

/-- Choosing one actual tangent Spin lift identifies all physical lift classes with
the base's all-cover sign group at the derived regularity. -/
def basedEquiv (A : SpinLift I n D) : GlobalH1 I M n ≃ Class I n D :=
  letI : IsManifold I 1 M := .of_le (n := n + 1) le_add_self
  letI : IsManifold I n M := .of_le (n := n + 1) le_self_add
  letI : ContMDiffVectorBundle n E (TangentSpace I : M → Type _) I :=
    TangentBundle.contMDiffVectorBundle
  MetricSpinHOneClassification.basedEquiv D A

/-- In the tangent classification the inverse measures the global displacement over
the geometric frame target, using its metric-derived charts. -/
theorem basedEquiv_symm_apply (A : SpinLift I n D) (q : Class I n D) :
    letI : IsManifold I 1 M := .of_le (n := n + 1) le_add_self
    letI : IsManifold I n M := .of_le (n := n + 1) le_self_add
    letI : ContMDiffVectorBundle n E (TangentSpace I : M → Type _) I :=
      TangentBundle.contMDiffVectorBundle
    (basedEquiv I n D A).symm q = GlobalSpinDisplacement.displacement
      (smoothAtlas (tetradData I n D)) (physicalClass A) q := rfl

/-- A lifting refinement of the genuine tangent tetrad transitions supplies a torsor
of physical classes over the original frame space. -/
@[instance_reducible] def torsor_of_refinement
    (h : ∃ R : Refinement (transitions I n D).domain M,
      HasSpinCocycleLift (lorentzData (transitions I n D) R)) :
    Torsor (GlobalH1 I M n) (Class I n D) :=
  letI : IsManifold I 1 M := .of_le (n := n + 1) le_add_self
  letI : IsManifold I n M := .of_le (n := n + 1) le_self_add
  letI : ContMDiffVectorBundle n E (TangentSpace I : M → Type _) I :=
    TangentBundle.contMDiffVectorBundle
  MetricSpinHOneClassification.torsor_of_refinement D h

/-- Eventual vanishing for normalized tangent tetrad pair lifts gives the all-cover
sign torsor of tangent Spin structures. -/
@[instance_reducible] def torsor_of_vanishes (P : PairLifts (transitions I n D))
    (h : Vanishes (classOf (representative P))) : Torsor (GlobalH1 I M n) (Class I n D) :=
  letI : IsManifold I 1 M := .of_le (n := n + 1) le_add_self
  letI : IsManifold I n M := .of_le (n := n + 1) le_self_add
  letI : ContMDiffVectorBundle n E (TangentSpace I : M → Type _) I :=
    TangentBundle.contMDiffVectorBundle
  MetricSpinHOneClassification.torsor_of_vanishes D P h

/-- A single physical tangent Spin isomorphism class exists exactly when the
tetrad cocycle lifts on a refinement and the all-cover sign group is trivial. -/
theorem unique_iff_refinement :
    (∃! _p : Class I n D, True) ↔
      (∃ R : Refinement (transitions I n D).domain M,
        HasSpinCocycleLift (lorentzData (transitions I n D) R)) ∧ Subsingleton (GlobalH1 I M n) :=
  letI : IsManifold I 1 M := .of_le (n := n + 1) le_add_self
  letI : IsManifold I n M := .of_le (n := n + 1) le_self_add
  letI : ContMDiffVectorBundle n E (TangentSpace I : M → Type _) I :=
    TangentBundle.contMDiffVectorBundle
  MetricSpinHOneClassification.unique_iff_refinement D

/-- For normalized tangent tetrad pair lifts, exactly one physical class exists iff
their degree-two sign vanishes after refinement and degree one is trivial. -/
theorem unique_iff_vanishes (P : PairLifts (transitions I n D)) :
    (∃! _p : Class I n D, True) ↔
      Vanishes (classOf (representative P)) ∧ Subsingleton (GlobalH1 I M n) :=
  letI : IsManifold I 1 M := .of_le (n := n + 1) le_add_self
  letI : IsManifold I n M := .of_le (n := n + 1) le_self_add
  letI : ContMDiffVectorBundle n E (TangentSpace I : M → Type _) I :=
    TangentBundle.contMDiffVectorBundle
  MetricSpinHOneClassification.unique_iff_vanishes D P

/-- If every nonempty tangent tetrad pair overlap is simply connected and locally
path connected, the constructed pair lifts give a unique-existence test. -/
theorem unique_iff_constructed_vanishes :
    let T := transitions I n D
    ∀ (hsc : ∀ i j, Nonempty ↥(CliffordSpinPairLiftConstruction.pairOverlap T i j) →
          SimplyConnectedSpace ↥(CliffordSpinPairLiftConstruction.pairOverlap T i j))
      (hlpc : ∀ i j, Nonempty ↥(CliffordSpinPairLiftConstruction.pairOverlap T i j) →
          LocallyPathConnectedSpace ↥(CliffordSpinPairLiftConstruction.pairOverlap T i j)),
      (∃! _p : Class I n D, True) ↔ Vanishes (classOf (representative
        (CliffordSpinPairLiftConstruction.pairLifts T hsc hlpc))) ∧ Subsingleton (GlobalH1 I M n) := by
  intro T hsc hlpc
  exact unique_iff_vanishes I n D (CliffordSpinPairLiftConstruction.pairLifts T hsc hlpc)

end FoliationQM.TangentSpinHOneClassification
