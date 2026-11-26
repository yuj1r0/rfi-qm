module
public import FoliationQM.CliffordSpinEquivalence
public import FoliationQM.SpinLorentzOrientation
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Topology.Algebra.ContinuousMonoidHom

/-!
# The canonical Clifford topology and the actual Spin topological group

Source scope: the abstract Clifford-spin identification underlying v13
`prop:takabayasi` and `eq:tetrad_rotor_map`. The full real Minkowski
Clifford algebra is given its canonical real module topology, without
using a matrix representation to define that topology. Its independently
constructed finite basis proves Hausdorffness; finite-dimensional
bilinearity and real linearity prove continuity of multiplication and
actual Clifford conjugation.

The even algebra and Mathlib spinGroup retain the resulting natural
subtype topologies. The faithful even Pauli equivalence is continuous in
both directions by finite-dimensional linear continuity. Its exact
restriction and previously proved inverse formula upgrade the genuine
Spin-to-SL group equivalence to a topological group isomorphism. Actual
Spin inversion is Clifford conjugation, and path connectedness follows
from the established special-linear-group topology. No smooth atlas,
simple-connectedness, or universal-cover assertion is made here.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.CliffordSpinTopology
open CliffordMinkowski CliffordEvenDimension CliffordEvenPauli CliffordSpinMap
open CliffordSpinEquivalence SourcePolarDatum SpinorMatrix

/-- The full Clifford algebra carries its canonical real module topology, defined independently of every matrix representation. -/
instance instTopologicalSpaceClifford : TopologicalSpace CliffordMinkowski.Algebra :=
  moduleTopology ℝ CliffordMinkowski.Algebra

/-- The actual topology on the full Clifford algebra is precisely the canonical module topology. -/
instance instIsModuleTopologyClifford : IsModuleTopology ℝ CliffordMinkowski.Algebra := ⟨rfl⟩

/-- Finite-dimensional Clifford multiplication and addition are continuous for the canonical topology. -/
instance instIsTopologicalRingClifford : IsTopologicalRing CliffordMinkowski.Algebra :=
  IsModuleTopology.isTopologicalRing ℝ CliffordMinkowski.Algebra

/-- Coordinates in the independently constructed Clifford basis are continuous for the canonical topology. -/
theorem continuous_cliffordBasis_coordinates : Continuous cliffordBasis.equivFun :=
  IsModuleTopology.continuous_of_linearMap cliffordBasis.equivFun.toLinearMap

/-- The canonical Clifford topology is Hausdorff by its injective actual basis coordinates. -/
instance instT2SpaceClifford : T2Space CliffordMinkowski.Algebra :=
  T2Space.of_injective_continuous cliffordBasis.equivFun.injective
    continuous_cliffordBasis_coordinates

/-- The actual Clifford basis is a continuous real coordinate equivalence for the already specified canonical topology. -/
def cliffordCoordinates : CliffordMinkowski.Algebra ≃L[ℝ] (Finset (Fin 4) → ℝ) :=
  cliffordBasis.equivFun.toContinuousLinearEquiv

/-- The continuous coordinate equivalence retains the independently constructed Clifford basis map. -/
theorem cliffordCoordinates_apply (x : CliffordMinkowski.Algebra) :
    cliffordCoordinates x = cliffordBasis.equivFun x := rfl

/-- Actual Clifford conjugation is a real linear map on the full Clifford algebra. -/
def cliffordStarLM : CliffordMinkowski.Algebra →ₗ[ℝ] CliffordMinkowski.Algebra where
  toFun := star
  map_add' := star_add
  map_smul' := CliffordAlgebra.star_smul

/-- The genuine ambient Clifford conjugation is continuous for the canonical module topology. -/
instance instContinuousStarClifford : ContinuousStar CliffordMinkowski.Algebra :=
  ⟨IsModuleTopology.continuous_of_linearMap cliffordStarLM⟩

/-- The actual Spin group with its inherited Clifford-subtype topology is a topological group. -/
instance instIsTopologicalGroupSpin : IsTopologicalGroup Spin where
  continuous_mul := continuous_mul
  continuous_inv := by
    apply continuous_induced_rng.mpr
    change Continuous (fun s : Spin => star (s : CliffordMinkowski.Algebra))
    exact continuous_star.comp continuous_subtype_val

/-- The even algebra has the topological ring structure inherited from the full Clifford algebra. -/
instance instIsTopologicalRingEven : IsTopologicalRing (CliffordAlgebra.even quadratic) :=
  inferInstanceAs (IsTopologicalRing (CliffordAlgebra.even quadratic).toSubring)

/-- The faithful even Pauli equivalence is continuous in both directions for the inherited even topology and existing matrix topology. -/
def evenContinuousLinearEquiv : CliffordAlgebra.even quadratic ≃L[ℝ] Mat2 :=
  evenPauliEquiv.toLinearEquiv.toContinuousLinearEquiv

/-- The continuous even equivalence has exactly the universal Pauli map as its function. -/
theorem evenContinuousLinearEquiv_apply (x : CliffordAlgebra.even quadratic) :
    evenContinuousLinearEquiv x = evenPauli x := rfl

/-- Its continuous inverse is exactly the established even-algebra inverse. -/
theorem evenContinuousLinearEquiv_symm_apply (A : Mat2) :
    evenContinuousLinearEquiv.symm A = evenPauliEquiv.symm A := rfl

/-- The actual inclusion of Spin into the even algebra is continuous for both inherited subtype topologies. -/
theorem continuous_toEven : Continuous toEven := by
  exact continuous_subtype_val.subtype_mk _

/-- The genuine Clifford Spin-to-matrix homomorphism is continuous for the independent canonical and matrix topologies. -/
theorem continuous_toMatrix : Continuous CliffordSpinMap.toMatrix := by
  exact (evenContinuousLinearEquiv.continuous.comp continuous_toEven).subtype_mk _

/-- The inverse Spin-to-matrix equivalence is continuous by its proved actual even-algebra inverse formula. -/
theorem continuous_spinEquiv_symm : Continuous spinEquiv.symm := by
  apply continuous_induced_rng.mpr
  change Continuous (fun A : SpecialLinearMatrix =>
    (spinEquiv.symm A : CliffordMinkowski.Algebra))
  simp_rw [spinEquiv_symm_coe]
  exact continuous_subtype_val.comp
    (evenContinuousLinearEquiv.symm.continuous.comp continuous_subtype_val)

/-- The actual Clifford Spin group and determinant-one complex matrices are isomorphic as topological groups for their existing topologies. -/
def spinMulHomeomorph : Spin ≃ₜ* SpecialLinearMatrix where
  toMulEquiv := spinEquiv
  continuous_toFun := continuous_toMatrix
  continuous_invFun := continuous_spinEquiv_symm

/-- The topological group equivalence retains exactly the proved algebraic Spin equivalence. -/
theorem spinMulHomeomorph_toMulEquiv : spinMulHomeomorph.toMulEquiv = spinEquiv := rfl

/-- The topological group equivalence evaluates to the actual Pauli Spin homomorphism. -/
theorem spinMulHomeomorph_apply (s : Spin) :
    spinMulHomeomorph s = CliffordSpinMap.toMatrix s := rfl

/-- The same natural Spin-to-matrix identification with only its topological structure retained. -/
def spinHomeomorph : Spin ≃ₜ SpecialLinearMatrix := spinMulHomeomorph.toHomeomorph

/-- The actual homeomorphism evaluates to the unchanged Pauli Spin homomorphism. -/
theorem spinHomeomorph_apply (s : Spin) :
    spinHomeomorph s = CliffordSpinMap.toMatrix s := rfl

/-- The homeomorphism inverse is precisely the existing algebraic inverse on determinant-one matrices. -/
theorem spinHomeomorph_symm_apply (A : SpecialLinearMatrix) :
    spinHomeomorph.symm A = spinEquiv.symm A := rfl

/-- The actual Minkowski Spin group is path connected in its inherited canonical topology. -/
instance instPathConnectedSpin : PathConnectedSpace Spin :=
  spinHomeomorph.symm.pathConnectedSpace

end FoliationQM.CliffordSpinTopology
