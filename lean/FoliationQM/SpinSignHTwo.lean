module
public import FoliationQM.SignEventualObstruction
public import Mathlib.GroupTheory.Congruence.Defs

/-!
# The commutative group of degree-two smooth Clifford signs

For the Spin-frame component of v13 `prop:takabayasi`, pointwise products
and inverses of normalized cocycles descend through the existing
fixed-cover relation by smooth pair coboundaries. This equips the
original obstruction class space with its degree-two group structure.
-/

@[expose] public section
noncomputable section
open scoped IsMulCommutative
namespace FoliationQM.SpinSignHTwo
open SpinSignCohomology SignClassRestriction CliffordSpinCoverRefinement

variable {E H B ι κ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace B] [ChartedSpace H B] {U : ι → TopologicalSpace.Opens B} {n : WithTop ℕ∞}

/-- Equality of all total triple coefficients determines the normalized cocycle. -/
theorem cocycle_ext {z w : TwoCocycle I U n}
    (h : ∀ i j k x, z.value i j k x = w.value i j k x) : z = w := by
  have hv : z.value = w.value := funext fun i => funext fun j => funext fun k => funext (h i j k)
  cases z
  cases w
  cases hv
  rfl

/-- Multiply two normalized degree-two cocycles using the actual physical signs. -/
def mulCocycle (z w : TwoCocycle I U n) : TwoCocycle I U n where
  value i j k x := z.value i j k x * w.value i j k x
  smooth_value i j k := (CliffordSpinManifold.contMDiff_mul n).comp_contMDiffOn
    ((z.smooth_value i j k).prodMk (w.smooth_value i j k))
  self_left i k x hi hk := by rw [z.self_left i k x hi hk, w.self_left i k x hi hk, one_mul]
  self_right i k x hi hk := by rw [z.self_right i k x hi hk, w.self_right i k x hi hk, one_mul]
  quadruple i j k l x hi hj hk hl := by
    rw [mul_mul_mul_comm, z.quadruple i j k l x hi hj hk hl, w.quadruple i j k l x hi hj hk hl,
      mul_mul_mul_comm]

/-- Invert every physical sign coefficient, retaining the smooth cocycle equations. -/
def invCocycle (z : TwoCocycle I U n) : TwoCocycle I U n where
  value i j k x := (z.value i j k x)⁻¹
  smooth_value i j k := (CliffordSpinManifold.contMDiff_inv n).comp_contMDiffOn (z.smooth_value i j k)
  self_left i k x hi hk := by rw [z.self_left i k x hi hk, inv_one]
  self_right i k x hi hk := by rw [z.self_right i k x hi hk, inv_one]
  quadruple i j k l x hi hj hk hl := by
    simpa only [mul_inv] using congrArg Inv.inv (z.quadruple i j k l x hi hj hk hl)

instance : CommGroup (TwoCocycle I U n) where
  one := neutralCocycle I U n
  mul := mulCocycle
  inv := invCocycle
  mul_assoc _ _ _ := cocycle_ext (fun _ _ _ _ => mul_assoc _ _ _)
  mul_comm _ _ := cocycle_ext (fun _ _ _ _ => mul_comm _ _)
  one_mul _ := cocycle_ext (fun _ _ _ _ => one_mul _)
  mul_one _ := cocycle_ext (fun _ _ _ _ => mul_one _)
  inv_mul_cancel _ := cocycle_ext (fun _ _ _ _ => inv_mul_cancel _)

/-- The original coboundary relation respects multiplication of representatives. -/
theorem related_mul {z z' w w' : TwoCocycle I U n} (hz : Related z z') (hw : Related w w') :
    Related (z * w) (z' * w') := by
  obtain ⟨a, ha⟩ := hz
  obtain ⟨b, hb⟩ := hw
  refine ⟨mulCochain a b, fun i j k x hi hj hk => ?_⟩
  change z'.value i j k x * w'.value i j k x = boundary (mulCochain a b) i j k x *
    (z.value i j k x * w.value i j k x)
  rw [boundary_mul, ha i j k x hi hj hk, hb i j k x hi hj hk, mul_mul_mul_comm]

/-- The multiplicative congruence has exactly the original fixed-cover setoid. -/
def signCon (I : ModelWithCorners ℝ E H) (U : ι → TopologicalSpace.Opens B) (n : WithTop ℕ∞) :
    Con (TwoCocycle I U n) where
  toSetoid := signSetoid I U n
  mul' := related_mul

instance : CommGroup (ObstructionClass I U n) := inferInstanceAs (CommGroup (signCon I U n).Quotient)

/-- The old distinguished neutral class is the identity of the obstruction group. -/
theorem neutralClass_eq_one : neutralClass I U n = (1 : ObstructionClass I U n) := rfl

/-- Multiplying two cocycles multiplies their original obstruction classes. -/
theorem classOf_mul (z w : TwoCocycle I U n) : classOf (z * w) = classOf z * classOf w := rfl

/-- Inversion of triple coefficients represents inversion in degree two. -/
theorem classOf_inv (z : TwoCocycle I U n) : classOf z⁻¹ = (classOf z)⁻¹ := rfl

/-- Every fixed-cover degree-two class has a normalized smooth cocycle representative. -/
theorem classOf_surjective : Function.Surjective (classOf (I := I) (U := U) (n := n)) :=
  fun c => Quotient.inductionOn c (fun z => ⟨z, rfl⟩)

/-- The existing restriction map is a homomorphism for the degree-two groups. -/
def restrictHom (R : Refinement U κ) : ObstructionClass I U n →* ObstructionClass I R.domain n where
  toFun := restrictClass R
  map_one' := rfl
  map_mul' c d := Quotient.inductionOn₂ c d (fun _ _ => rfl)

/-- This homomorphism is the original map on obstruction classes. -/
theorem restrictHom_apply (R : Refinement U κ) (c : ObstructionClass I U n) :
    restrictHom R c = restrictClass R c := rfl

end FoliationQM.SpinSignHTwo
