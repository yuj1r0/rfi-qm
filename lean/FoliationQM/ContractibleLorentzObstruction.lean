module
public import FoliationQM.ContractibleTransitionPaths
public import FoliationQM.GeometricIntrinsicSpinObstruction

/-!
# The intrinsic Lorentz obstruction constructed from contractible overlaps

For the geometric component of v13 `prop:takabayasi`, standard
contractibility of each nonempty pair overlap constructs normalized
joint transition paths. The native coefficient and all-cover class
are then defined by the independent intrinsic path construction.
The physical Spin comparisons and lifting criteria are subsequent
proofs. No joint path family or physical pair lift is an input to this
construction. Local path connectedness of the base remains explicit.
This does not assert existence of suitable refinements or conventional w2.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.ContractibleLorentzObstruction
open CliffordSpinCoverRefinement CliffordSpinCocycleCorrection
open CliffordSpinLorentzSmooth LorentzMatrixGroup GeometricSpinObstruction

variable {E H B ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] [TopologicalSpace B] [ChartedSpace H B]
  {I : ModelWithCorners ℝ E H} {n : WithTop ℕ∞}

/-- Standard contractibility is required only for nonempty true pair overlaps. -/
abbrev PairContractible (D : CliffordSpinLorentzTransitions.Data I B ι n) : Prop :=
  ContractibleTransitionPaths.PairContractible (LorentzIntrinsicObstruction.data D)

/-- Construct original normalized Lorentz transition paths from overlap topology,
using the proved path connectivity of the actual Lorentz group. -/
def paths (D : CliffordSpinLorentzTransitions.Data I B ι n) (h : PairContractible D) :
    LorentzTransitionPaths.Family D :=
  LorentzIntrinsicObstruction.lorentzFamily
    (ContractibleTransitionPaths.family (LorentzIntrinsicObstruction.data D) h)

/-- The original Lorentz interface retains the entire generically constructed joint family. -/
theorem paths_family (D : CliffordSpinLorentzTransitions.Data I B ι n) (h : PairContractible D) :
    LorentzIntrinsicObstruction.family (paths D h) =
      ContractibleTransitionPaths.family (LorentzIntrinsicObstruction.data D) h :=
  LorentzIntrinsicObstruction.family_lorentzFamily _

variable [LocallyPathConnectedSpace B]

/-- The native fixed-cover class of the paths constructed from contractible overlaps. -/
def fixedClass (D : CliffordSpinLorentzTransitions.Data I B ι n) (h : PairContractible D) :
    ModTwoCohomology.H2 D.domain :=
  ModTwoCohomology.classOf (IntrinsicPathCocycle.cocycle LorentzPathCoefficient.character
    (ContractibleTransitionPaths.family (LorentzIntrinsicObstruction.data D) h))

/-- The independent all-cover class constructed from the original transitions and overlap topology. -/
def obstruction (D : CliffordSpinLorentzTransitions.Data I B ι n) (h : PairContractible D) :
    ModTwoAllCover.GlobalH2 B :=
  GlobalIntrinsicPathObstruction.obstruction LorentzPathCoefficient.character
    (ContractibleTransitionPaths.family (LorentzIntrinsicObstruction.data D) h)

/-- Every other normalized joint Lorentz path family computes the same native fixed-cover class. -/
theorem fixedClass_eq (D : CliffordSpinLorentzTransitions.Data I B ι n) (h : PairContractible D)
    (P : LorentzTransitionPaths.Family D) :
    fixedClass D h = LorentzIntrinsicObstruction.fixedClass P :=
  IntrinsicPathChoice.class_independent LorentzPathCoefficient.character
    (ContractibleTransitionPaths.family (LorentzIntrinsicObstruction.data D) h)
    (LorentzIntrinsicObstruction.family P)

/-- The constructed all-cover class agrees with every other normalized joint path family,
by intrinsic coboundary algebra without a physical comparison. -/
theorem obstruction_eq (D : CliffordSpinLorentzTransitions.Data I B ι n) (h : PairContractible D)
    (P : LorentzTransitionPaths.Family D) :
    obstruction D h = LorentzIntrinsicObstruction.obstruction P :=
  GlobalIntrinsicPathObstruction.independent LorentzPathCoefficient.character
    (ContractibleTransitionPaths.family (LorentzIntrinsicObstruction.data D) h)
    (LorentzIntrinsicObstruction.family P)

/-- Any normalized smooth Clifford pair lifts compute the constructed independent global class. -/
theorem obstruction_eq_physical (D : CliffordSpinLorentzTransitions.Data I B ι n)
    (h : PairContractible D) (S : CliffordSpinTransitionLifts.PairLifts D) :
    obstruction D h = ModTwoSpinObstruction.obstruction S :=
  (obstruction_eq D h (paths D h)).trans
    (LorentzIntrinsicObstruction.obstruction_eq_of_pairLifts (paths D h) S)

/-- The constructed fixed-cover class vanishes precisely when the original Lorentz
transitions have a genuine smooth Spin cocycle on that cover. -/
theorem fixed_zero_iff (D : CliffordSpinLorentzTransitions.Data I B ι n) (h : PairContractible D) :
    fixedClass D h = 0 ↔ HasSpinCocycleLift D := by
  rw [fixedClass_eq D h (paths D h)]
  exact GeometricIntrinsicSpinObstruction.fixed_zero_iff (paths D h)

/-- The constructed global class vanishes precisely when a genuine smooth Spin cocycle
exists on some further point-indexed open refinement. -/
theorem zero_iff_refinement (D : CliffordSpinLorentzTransitions.Data I B ι n)
    (h : PairContractible D) :
    obstruction D h = 0 ↔
      ∃ R : Refinement D.domain B, HasSpinCocycleLift (lorentzData D R) := by
  rw [obstruction_eq D h (paths D h)]
  exact GeometricIntrinsicSpinObstruction.zero_iff_refinement (paths D h)

variable {EP HP T : Type*} [NormedAddCommGroup EP] [NormedSpace ℝ EP]
  [TopologicalSpace HP] [TopologicalSpace T] [ChartedSpace HP T]
  {KT : ModelWithCorners ℝ EP HP} {proj : T → B}
  {L : GeometricPrincipalAtlas.Data (G := ProperFutureLorentz) proj ι}
  (LM : GeometricPrincipalSmoothAtlas.Data I lorentzModel KT L n) [IsManifold I n B]

/-- Contractible pair overlaps yield a constructed independent class whose vanishing
is exactly existence of a smooth Spin lift into the original geometric target. -/
theorem nonempty_iff (h : PairContractible (AdaptedGeometricSpinLift.lorentzData LM)) :
    Nonempty (SmoothLift I KT L n) ↔
      obstruction (AdaptedGeometricSpinLift.lorentzData LM) h = 0 := by
  rw [obstruction_eq _ h (paths _ h)]
  exact GeometricIntrinsicSpinObstruction.nonempty_iff LM (paths _ h)

/-- Vanishing of the constructed intrinsic class supplies the actual all-cover
first-cohomology torsor of physical smooth Spin lift classes. -/
@[instance_reducible] def torsor_of_zero
    (h : PairContractible (AdaptedGeometricSpinLift.lorentzData LM))
    (hz : obstruction (AdaptedGeometricSpinLift.lorentzData LM) h = 0) :
    Torsor (SpinAllCoverHOne.GlobalH1 I B n) (SmoothSpinRelativeClass.PhysicalClass I KT L n) :=
  SmoothSpinHOneTorsor.torsor LM ((nonempty_iff LM h).mpr hz)

/-- Exactly one physical smooth Spin class exists iff the constructed obstruction
vanishes and the independent all-cover first-cohomology group is trivial. -/
theorem unique_iff (h : PairContractible (AdaptedGeometricSpinLift.lorentzData LM)) :
    (∃! _p : SmoothSpinRelativeClass.PhysicalClass I KT L n, True) ↔
      obstruction (AdaptedGeometricSpinLift.lorentzData LM) h = 0 ∧
        Subsingleton (SpinAllCoverHOne.GlobalH1 I B n) := by
  rw [obstruction_eq _ h (paths _ h)]
  exact GeometricIntrinsicSpinObstruction.unique_iff LM (paths _ h)

end FoliationQM.ContractibleLorentzObstruction
