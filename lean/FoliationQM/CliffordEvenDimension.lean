module
public import FoliationQM.CliffordMinkowski
public import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Dimensions of the genuine Minkowski Clifford algebra and its even part

Source scope: v13 `prop:takabayasi` and the Clifford realization underlying
`eq:tetrad_rotor_map`. The full real Clifford algebra has its actual basis
transported from the exterior algebra. Left multiplication by the time
basis vector, whose Clifford square is one, identifies the actual even
and odd graded subspaces. Their complementarity then gives dimension
eight for the even subalgebra, independently of any matrix representation
or assumed faithfulness of that representation.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.CliffordEvenDimension
open CliffordMinkowski

/-- The actual sixteen-element Clifford basis transported from the exterior algebra basis. -/
def cliffordBasis : Module.Basis (Finset (Fin 4)) ℝ CliffordMinkowski.Algebra :=
  ((Pi.basisFun ℝ (Fin 4)).ExteriorAlgebra).map
    (CliffordAlgebra.equivExterior quadratic).symm

/-- The genuine Minkowski Clifford algebra is finite-dimensional over the reals. -/
instance instFiniteDimensionalClifford : FiniteDimensional ℝ CliffordMinkowski.Algebra :=
  cliffordBasis.finiteDimensional_of_finite

/-- The actual real dimension of the full Minkowski Clifford algebra is sixteen. -/
theorem finrank_clifford : Module.finrank ℝ CliffordMinkowski.Algebra = 16 := by
  rw [Module.finrank_eq_card_basis cliffordBasis]
  norm_num

/-- The time coordinate vector embedded in the genuine Clifford algebra. -/
def timeVector : CliffordMinkowski.Algebra :=
  CliffordAlgebra.ι quadratic (basisVector 0)

/-- The embedded time vector has Clifford square one for the (+---) quadratic form. -/
theorem timeVector_sq : timeVector * timeVector = 1 := by
  rw [timeVector, CliffordAlgebra.ι_sq_scalar, quadratic_basisVector]
  norm_num [RealLorentzFrame.sign]

/-- Left multiplication by the time vector identifies the actual even and odd subspaces. -/
def evenOddEquiv : CliffordAlgebra.evenOdd quadratic 0 ≃ₗ[ℝ]
    CliffordAlgebra.evenOdd quadratic 1 where
  toFun x := ⟨timeVector * x.val, by
    simpa only [timeVector, add_zero] using SetLike.mul_mem_graded
      (CliffordAlgebra.ι_mem_evenOdd_one quadratic (basisVector 0)) x.property⟩
  invFun x := ⟨timeVector * x.val, by
    have h := SetLike.mul_mem_graded
      (CliffordAlgebra.ι_mem_evenOdd_one quadratic (basisVector 0)) x.property
    have hgrade : (1 + 1 : ZMod 2) = 0 := by decide
    simpa only [timeVector, hgrade] using h⟩
  left_inv x := by
    apply Subtype.ext
    change timeVector * (timeVector * x.val) = x.val
    rw [← mul_assoc, timeVector_sq, one_mul]
  right_inv x := by
    apply Subtype.ext
    change timeVector * (timeVector * x.val) = x.val
    rw [← mul_assoc, timeVector_sq, one_mul]
  map_add' x y := by
    apply Subtype.ext
    exact mul_add _ _ _
  map_smul' r x := by
    apply Subtype.ext
    exact mul_smul_comm _ _ _

/-- The even-to-odd equivalence is literal left Clifford multiplication by the time vector. -/
theorem evenOddEquiv_apply (x : CliffordAlgebra.evenOdd quadratic 0) :
    (evenOddEquiv x : CliffordMinkowski.Algebra) = timeVector * x.val := rfl

/-- Its inverse is the same literal left Clifford multiplication. -/
theorem evenOddEquiv_symm_apply (x : CliffordAlgebra.evenOdd quadratic 1) :
    (evenOddEquiv.symm x : CliffordMinkowski.Algebra) = timeVector * x.val := rfl

/-- The genuine even Minkowski Clifford subalgebra has real dimension eight. -/
theorem finrank_even : Module.finrank ℝ (CliffordAlgebra.even quadratic) = 8 := by
  have hsum := Submodule.finrank_add_eq_of_isCompl
    (CliffordAlgebra.evenOdd_isCompl quadratic)
  have heq := evenOddEquiv.finrank_eq
  rw [finrank_clifford] at hsum
  change Module.finrank ℝ (CliffordAlgebra.evenOdd quadratic 0) = 8
  omega

end FoliationQM.CliffordEvenDimension
