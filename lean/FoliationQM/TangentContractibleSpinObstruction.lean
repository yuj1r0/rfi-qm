module
public import FoliationQM.MetricContractibleSpinObstruction
public import FoliationQM.TangentSpinHOneClassification

/-!
# Constructed intrinsic obstruction for the original tangent frame bundle

For the geometric component of v13 `prop:takabayasi`, a C^(n+1) base
provides the original C^n tangent vector bundle. Independent tangent
metric geometry determines its genuine oriented future tetrad cover.
Contractibility of the actual nonempty pair overlaps constructs the
intrinsic native mod-two class, whose zero is equivalent to an actual
smooth tangent Spin lift. The associated H1 torsor and uniqueness test
retain the one-derivative loss and an explicit locally path connected
base. No conventional real-bundle w2 or automatic good cover is claimed.
-/

@[expose] public section
noncomputable section
open Bundle
open scoped Manifold
namespace FoliationQM.TangentContractibleSpinObstruction
open TangentLorentzTetradCover GeometricLorentzFrameBundle
open SpinAllCoverHOne TangentSpinHOneClassification

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [TopologicalSpace M] [ChartedSpace H M]
  (n : WithTop ℕ∞) [IsManifold I (n + 1) M] (D : Data (M := M) I n)

/-- Standard contractibility is required only on nonempty pairs of the actual
metric-derived tangent tetrad domains. -/
abbrev PairContractible : Prop :=
  ContractibleLorentzObstruction.PairContractible (transitions I n D)

/-- Joint Lorentz transition paths are constructed for the original tangent geometry. -/
def paths (h : PairContractible I n D) : LorentzTransitionPaths.Family (transitions I n D) :=
  ContractibleLorentzObstruction.paths (transitions I n D) h

variable [LocallyPathConnectedSpace M]

/-- The independent native class on the original derived tangent tetrad cover. -/
def fixedClass (h : PairContractible I n D) : ModTwoCohomology.H2 (transitions I n D).domain :=
  ContractibleLorentzObstruction.fixedClass (transitions I n D) h

/-- The constructed all-cover class uses the actual tangent transitions at the
derived C^n regularity, with no separately supplied path or Spin pair lifts. -/
def obstruction (h : PairContractible I n D) : ModTwoAllCover.GlobalH2 M :=
  ContractibleLorentzObstruction.obstruction (transitions I n D) h

/-- Every normalized joint path family for these original tangent transitions
computes the same independent constructed global class. -/
theorem obstruction_eq_family (h : PairContractible I n D)
    (P : LorentzTransitionPaths.Family (transitions I n D)) :
    obstruction I n D h = LorentzIntrinsicObstruction.obstruction P :=
  ContractibleLorentzObstruction.obstruction_eq (transitions I n D) h P

/-- Actual normalized tangent Spin pair lifts agree with the independently
constructed intrinsic global class. -/
theorem obstruction_eq_physical (h : PairContractible I n D)
    (S : CliffordSpinTransitionLifts.PairLifts (transitions I n D)) :
    obstruction I n D h = ModTwoSpinObstruction.obstruction S :=
  ContractibleLorentzObstruction.obstruction_eq_physical (transitions I n D) h S

/-- A same-cover geometric Spin lift of the original tangent frame bundle exists
exactly when the constructed native fixed-cover class vanishes. -/
theorem adapted_nonempty_iff (h : PairContractible I n D) :
    letI : IsManifold I 1 M := .of_le (n := n + 1) le_add_self
    letI : ContMDiffVectorBundle n E (TangentSpace I : M → Type _) I :=
      TangentBundle.contMDiffVectorBundle
    Nonempty (GeometricSpinStructure.Lift I (principalAtlas (tetradData I n D)) n) ↔
      fixedClass I n D h = 0 := by
  let : IsManifold I 1 M := .of_le (n := n + 1) le_add_self
  let : IsManifold I n M := .of_le (n := n + 1) le_self_add
  let : ContMDiffVectorBundle n E (TangentSpace I : M → Type _) I :=
    TangentBundle.contMDiffVectorBundle
  exact MetricContractibleSpinObstruction.adapted_nonempty_iff D h

/-- A genuine smooth tangent Spin lift exists precisely when the constructed
global class vanishes, deriving the original tangent regularity from the base. -/
theorem nonempty_iff (h : PairContractible I n D) :
    Nonempty (SpinLift I n D) ↔ obstruction I n D h = 0 := by
  let : IsManifold I 1 M := .of_le (n := n + 1) le_add_self
  let : IsManifold I n M := .of_le (n := n + 1) le_self_add
  let : ContMDiffVectorBundle n E (TangentSpace I : M → Type _) I :=
    TangentBundle.contMDiffVectorBundle
  exact MetricContractibleSpinObstruction.nonempty_iff D h

/-- Zero of the constructed tangent class supplies the all-cover H1 torsor of
physical lifts into the original tangent frame space. -/
@[instance_reducible] def torsor_of_zero (h : PairContractible I n D)
    (hz : obstruction I n D h = 0) : Torsor (GlobalH1 I M n) (Class I n D) :=
  letI : IsManifold I 1 M := .of_le (n := n + 1) le_add_self
  letI : IsManifold I n M := .of_le (n := n + 1) le_self_add
  letI : ContMDiffVectorBundle n E (TangentSpace I : M → Type _) I :=
    TangentBundle.contMDiffVectorBundle
  MetricContractibleSpinObstruction.torsor_of_zero D h hz

/-- Precisely one physical tangent Spin class exists iff the constructed degree-two
class vanishes and the all-cover first group at the derived regularity is trivial. -/
theorem unique_iff (h : PairContractible I n D) :
    (∃! _p : Class I n D, True) ↔
      obstruction I n D h = 0 ∧ Subsingleton (GlobalH1 I M n) := by
  let : IsManifold I 1 M := .of_le (n := n + 1) le_add_self
  let : IsManifold I n M := .of_le (n := n + 1) le_self_add
  let : ContMDiffVectorBundle n E (TangentSpace I : M → Type _) I :=
    TangentBundle.contMDiffVectorBundle
  exact MetricContractibleSpinObstruction.unique_iff D h

end FoliationQM.TangentContractibleSpinObstruction
