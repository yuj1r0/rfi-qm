module
public import FoliationQM.LorentzPathCoefficient
public import FoliationQM.GlobalIntrinsicPathObstruction
public import FoliationQM.TransitionLoopCocycle

/-!
# The intrinsic Lorentz path obstruction and the physical Spin defect

For the geometric characteristic-class comparison supporting v13
`prop:takabayasi`, the original smooth Lorentz transitions and their
joint paths determine the independent topological path construction.
The canonical intrinsic character defines the coefficient and native
cohomology classes. Actual covering endpoints then prove equality with
the original Clifford Spin obstruction. Both conversions of path
families retain their entire joint maps and are inverse.
Local path connectedness and a supplied joint family remain explicit.
No conventional real-bundle Stiefel--Whitney class is asserted here.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.LorentzIntrinsicObstruction
open LorentzMatrixGroup CliffordSpinMap CliffordSpinLorentz
open SpinTransitionPathLifts SpinSignDefectRepresentative SpinSignLocalCoefficients

variable {E H B ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] [TopologicalSpace B] [ChartedSpace H B]
  {I : ModelWithCorners ℝ E H} {n : WithTop ℕ∞}

/-- Forget only differentiability: the original Lorentz transitions give
independent continuous transition data on their identical open cover. -/
def data (D : CliffordSpinLorentzTransitions.Data I B ι n) :
    PathTransitionData.Data ProperFutureLorentz B ι where
  domain := D.domain
  covers := D.covers
  transition := D.transition
  continuous_transition i j := (D.smooth_transition i j).continuousOn
  identity := D.identity
  comp := D.comp

variable {D : CliffordSpinLorentzTransitions.Data I B ι n}

/-- Extraction preserves the literal original open domains. -/
theorem data_domain : (data D).domain = D.domain := rfl

/-- Extraction preserves the actual Lorentz transitions at every point. -/
theorem data_transition (i j : ι) (x : B) :
    (data D).transition i j x = D.transition i j x := rfl

/-- The original joint Lorentz paths are a family for the extracted purely
topological transition data, without any change to their maps. -/
def family (P : LorentzTransitionPaths.Family D) : PathTransitionData.Family (data D) where
  homotopy := P.homotopy
  source := P.source
  target := P.target
  diagonal := P.diagonal

/-- A generic joint path family for the extracted transitions is also an
original Lorentz path family; no separate family is presumed to exist. -/
def lorentzFamily (P : PathTransitionData.Family (data D)) : LorentzTransitionPaths.Family D where
  homotopy := P.homotopy
  source := P.source
  target := P.target
  diagonal := P.diagonal

/-- Converting an original family to generic data and back retains the entire family. -/
theorem lorentzFamily_family (P : LorentzTransitionPaths.Family D) :
    lorentzFamily (family P) = P := rfl

/-- Converting a generic family through the original Lorentz interface is also the identity. -/
theorem family_lorentzFamily (P : PathTransitionData.Family (data D)) :
    family (lorentzFamily P) = P := rfl

/-- The extracted pointwise path is precisely the original actual time slice. -/
theorem family_path (P : LorentzTransitionPaths.Family D) (i j : ι) (x : B)
    (hi : x ∈ D.domain i) (hj : x ∈ D.domain j) :
    PathTransitionData.path (family P) i j x hi hj = LorentzTransitionPaths.path P i j x hi hj := rfl

/-- The quotient-to-Spin homomorphism sends each intrinsic transition
path class to the actual smooth transition obtained by path lifting. -/
theorem lift_toSpin (P : LorentzTransitionPaths.Family D) (i j : ι) (x : B)
    (hi : x ∈ D.domain i) (hj : x ∈ D.domain j) :
    LorentzPathEndpoint.toSpin (PathTransitionData.lift (family P) i j x hi hj) =
      (pairLifts P).transition i j x := by
  change LorentzPathEndpoint.toSpin (BasedPathGroup.classOf
    (BasedPathGroup.fromPath (LorentzTransitionPaths.path P i j x hi hj))) = _
  rw [LorentzPathEndpoint.toSpin_classOf, LorentzPathEndpoint.endpoint_fromPath]
  exact (pairLifts_transition P i j x hi hj).symm

/-- The intrinsic kernel defect maps to the literal physical ordered
Clifford defect on every genuine triple intersection. -/
theorem defect_toSpin (P : LorentzTransitionPaths.Family D) (i j k : ι) (x : B)
    (hi : x ∈ D.domain i) (hj : x ∈ D.domain j) (hk : x ∈ D.domain k) :
    LorentzPathSpinEquivalence.kernelEquiv (IntrinsicPathCocycle.defect (family P) i j k x hi hj hk) =
      (representative (pairLifts P)).value i j k x := by
  apply Subtype.ext
  rw [LorentzPathSpinEquivalence.kernelEquiv_val]
  change LorentzPathEndpoint.toSpin
    (PathTransitionData.lift (family P) j k x hj hk * PathTransitionData.lift (family P) i j x hi hj *
      (PathTransitionData.lift (family P) i k x hi hk)⁻¹) = _
  rw [map_mul, map_mul, map_inv, lift_toSpin P j k x hj hk, lift_toSpin P i j x hi hj,
    lift_toSpin P i k x hi hk, representative_val _ i j k x hi hj hk]
  rfl

/-- The independently defined intrinsic Lorentz coefficient on a true
triple overlap, using the canonical zero-versus-nonzero kernel character. -/
def coefficient (P : LorentzTransitionPaths.Family D) (i j k : ι) (x : B)
    (hi : x ∈ D.domain i) (hj : x ∈ D.domain j) (hk : x ∈ D.domain k) : ZMod 2 :=
  IntrinsicPathCocycle.coefficient LorentzPathCoefficient.character (family P) i j k x hi hj hk

/-- Actual endpoint comparison identifies the intrinsic coefficient with
the encoding of the original physical Clifford sign defect. -/
theorem coefficient_eq_encode (P : LorentzTransitionPaths.Family D) (i j k : ι) (x : B)
    (hi : x ∈ D.domain i) (hj : x ∈ D.domain j) (hk : x ∈ D.domain k) :
    coefficient P i j k x hi hj hk = encode ((representative (pairLifts P)).value i j k x) := by
  change Multiplicative.toAdd (LorentzPathCoefficient.character
    (IntrinsicPathCocycle.defect (family P) i j k x hi hj hk)) = _
  rw [LorentzPathCoefficient.character_apply, LorentzPathCoefficient.value_eq_encode,
    defect_toSpin P i j k x hi hj hk]
  rfl

/-- The intrinsic coefficient also agrees with the coefficient of the
previously constructed actual concatenated triangular Lorentz loop. -/
theorem coefficient_eq_triangle (P : LorentzTransitionPaths.Family D) (i j k : ι) (x : B)
    (hi : x ∈ D.domain i) (hj : x ∈ D.domain j) (hk : x ∈ D.domain k) :
    coefficient P i j k x hi hj hk = TransitionLoopCocycle.coefficient P i j k x hi hj hk := by
  rw [coefficient_eq_encode]
  exact (TransitionLoopCocycle.value_eq_encode P i j k x hi hj hk).symm.trans
    (TransitionLoopCocycle.value_mem P i j k x hi hj hk)

variable [LocallyPathConnectedSpace B]

/-- The native intrinsic cocycle is constructed by generic path homotopy,
centrality, and local constancy, before any physical Spin comparison. -/
def cocycle (P : LorentzTransitionPaths.Family D) : ModTwoCohomology.TwoCocycle D.domain :=
  IntrinsicPathCocycle.cocycle LorentzPathCoefficient.character (family P)

/-- The native cocycle retains its intrinsic coefficient on every actual triple overlap. -/
theorem cocycle_value (P : LorentzTransitionPaths.Family D) (i j k : ι) (x : B)
    (hi : x ∈ D.domain i) (hj : x ∈ D.domain j) (hk : x ∈ D.domain k) :
    (cocycle P).value i j k x = coefficient P i j k x hi hj hk :=
  IntrinsicPathCocycle.cocycle_value LorentzPathCoefficient.character (family P) i j k x hi hj hk

/-- The native fixed-cover class of the independent intrinsic Lorentz cocycle. -/
def fixedClass (P : LorentzTransitionPaths.Family D) : ModTwoCohomology.H2 D.domain :=
  ModTwoCohomology.classOf (cocycle P)

/-- The independently constructed native class equals the existing
physical Spin obstruction on the same cover. -/
theorem fixedClass_eq (P : LorentzTransitionPaths.Family D) :
    fixedClass P = ModTwoSpinObstruction.fixedClass (pairLifts P) := by
  change ModTwoCohomology.classOf (cocycle P) =
    ModTwoCohomology.classOf (SpinModTwoComparison.toTwo (representative (pairLifts P)))
  apply ModTwoCohomology.classOf_eq_of_eqOn
  intro i j k x hi hj hk
  rw [cocycle_value P i j k x hi hj hk]
  exact coefficient_eq_encode P i j k x hi hj hk

/-- The global class is the independent all-cover path obstruction
with the canonical intrinsic Lorentz kernel character. -/
def obstruction (P : LorentzTransitionPaths.Family D) : ModTwoAllCover.GlobalH2 B :=
  GlobalIntrinsicPathObstruction.obstruction LorentzPathCoefficient.character (family P)

/-- Actual Spin endpoint comparison identifies the independent global
path obstruction with the original global physical lifting obstruction. -/
theorem obstruction_eq (P : LorentzTransitionPaths.Family D) :
    obstruction P = ModTwoSpinObstruction.obstruction (pairLifts P) := by
  change ModTwoAllCover.ofCover D.domain D.covers (fixedClass P) =
    ModTwoAllCover.ofCover D.domain D.covers (ModTwoSpinObstruction.fixedClass (pairLifts P))
  rw [fixedClass_eq]

/-- Any original normalized smooth Spin pair lifts compute this same
independently defined global class. -/
theorem obstruction_eq_of_pairLifts (P : LorentzTransitionPaths.Family D)
    (S : CliffordSpinTransitionLifts.PairLifts D) :
    obstruction P = ModTwoSpinObstruction.obstruction S :=
  (obstruction_eq P).trans (ModTwoSpinObstruction.obstruction_independent (pairLifts P) S)

/-- The independent global class is unchanged by any normalized jointly
continuous Lorentz path choices, directly by intrinsic coboundary algebra. -/
theorem obstruction_independent (P Q : LorentzTransitionPaths.Family D) :
    obstruction P = obstruction Q :=
  GlobalIntrinsicPathObstruction.independent LorentzPathCoefficient.character (family P) (family Q)

end FoliationQM.LorentzIntrinsicObstruction
