module
public import FoliationQM.ParacompactMetricSpinCriterion
public import FoliationQM.TangentSpinHOneClassification

/-!
# The native obstruction of the actual tangent frame bundle

For the geometric frame component of v13 `prop:takabayasi`, an order-`n+1`
manifold supplies its order-`n` tangent vector bundle. The Lorentz metric,
orientation and future geometry on that bundle determine an oriented future
frame atlas. Its native degree-two obstruction detects its smooth Spin lifts
on a paracompact normal locally path connected base.
-/

@[expose] public section
noncomputable section
open Bundle
open scoped Manifold
namespace FoliationQM.ParacompactTangentSpinCriterion
open TangentLorentzTetradCover TangentSpinHOneClassification
open CliffordSpinCoverRefinement CliffordSpinCocycleCorrection SpinAllCoverHOne

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [TopologicalSpace M] [ChartedSpace H M]
  [ParacompactSpace M] [NormalSpace M] [LocallyPathConnectedSpace M]
  (n : WithTop ℕ∞) [IsManifold I (n + 1) M] (D : Data (M := M) I n)

/-- The canonical all-cover class of the physical tangent frames, with tangent regularity derived from the base. -/
def obstruction : ModTwoAllCover.GlobalH2 M :=
  letI : IsManifold I 1 M := .of_le (n := n + 1) le_add_self
  letI : ContMDiffVectorBundle n E (TangentSpace I : M → Type _) I := TangentBundle.contMDiffVectorBundle
  ParacompactMetricSpinCriterion.obstruction D

/-- Any normalized Spin pairs lifting the original tangent tetrad transitions compute this class. -/
theorem obstruction_physical (P : CliffordSpinTransitionLifts.PairLifts (transitions I n D)) :
    obstruction I n D = ModTwoSpinObstruction.obstruction P := by
  let : IsManifold I 1 M := .of_le (n := n + 1) le_add_self
  let : IsManifold I n M := .of_le (n := n + 1) le_self_add
  let : ContMDiffVectorBundle n E (TangentSpace I : M → Type _) I := TangentBundle.contMDiffVectorBundle
  exact ParacompactMetricSpinCriterion.obstruction_physical D P

/-- The original tangent frame space has a smooth Spin lift exactly when its obstruction vanishes. -/
theorem nonempty_iff : Nonempty (SpinLift I n D) ↔ obstruction I n D = 0 := by
  let : IsManifold I 1 M := .of_le (n := n + 1) le_add_self
  let : IsManifold I n M := .of_le (n := n + 1) le_self_add
  let : ContMDiffVectorBundle n E (TangentSpace I : M → Type _) I := TangentBundle.contMDiffVectorBundle
  exact ParacompactMetricSpinCriterion.nonempty_iff D

/-- Zero of the native tangent class detects a lifting refinement of its actual order-n tetrad transitions. -/
theorem zero_iff_refinement_lift : obstruction I n D = 0 ↔
    ∃ R : Refinement (transitions I n D).domain M,
      HasSpinCocycleLift (lorentzData (transitions I n D) R) := by
  let : IsManifold I 1 M := .of_le (n := n + 1) le_add_self
  let : IsManifold I n M := .of_le (n := n + 1) le_self_add
  let : ContMDiffVectorBundle n E (TangentSpace I : M → Type _) I := TangentBundle.contMDiffVectorBundle
  exact ParacompactMetricSpinCriterion.zero_iff_refinement_lift D

/-- Vanishing supplies the degree-one torsor of physical tangent Spin lifts at the derived order. -/
@[instance_reducible] def torsor_of_zero (hz : obstruction I n D = 0) :
    Torsor (GlobalH1 I M n) (Class I n D) :=
  letI : IsManifold I 1 M := .of_le (n := n + 1) le_add_self
  letI : IsManifold I n M := .of_le (n := n + 1) le_self_add
  letI : ContMDiffVectorBundle n E (TangentSpace I : M → Type _) I := TangentBundle.contMDiffVectorBundle
  ParacompactMetricSpinCriterion.torsor_of_zero D hz

/-- Exactly one physical tangent Spin class exists precisely when its native obstruction vanishes
and the all-cover first sign group at the tangent regularity is trivial. -/
theorem unique_iff : (∃! _p : Class I n D, True) ↔
    obstruction I n D = 0 ∧ Subsingleton (GlobalH1 I M n) := by
  let : IsManifold I 1 M := .of_le (n := n + 1) le_add_self
  let : IsManifold I n M := .of_le (n := n + 1) le_self_add
  let : ContMDiffVectorBundle n E (TangentSpace I : M → Type _) I := TangentBundle.contMDiffVectorBundle
  exact ParacompactMetricSpinCriterion.unique_iff D

/-- Choosing a reference lift given by vanishing identifies all tangent Spin classes with degree one. -/
def basedEquiv_of_zero (hz : obstruction I n D = 0) : GlobalH1 I M n ≃ Class I n D :=
  basedEquiv I n D ((nonempty_iff I n D).mpr hz).some

end FoliationQM.ParacompactTangentSpinCriterion
