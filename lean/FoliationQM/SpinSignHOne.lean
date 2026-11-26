module
public import FoliationQM.SpinSignOneCocycle
public import Mathlib.GroupTheory.Congruence.Defs

/-!
# The first sign cohomology group of a fixed open family

For the Spin-frame component of v13 `prop:takabayasi`, a change of sign
in each chart acts on the ordered pair coefficient by its chartwise
coboundary. This defines a multiplicative congruence using values on the
actual overlaps. Its quotient is an abelian group.
-/

@[expose] public section
noncomputable section
open Set
open scoped Manifold IsMulCommutative
namespace FoliationQM.SpinSignHOne
open CliffordSpinSignKernel SpinSignCohomology SpinSignOneCocycle

variable {E H B ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace B] [ChartedSpace H B] {U : ι → TopologicalSpace.Opens B}
  {n : WithTop ℕ∞}

private theorem cochain_ext {b c : OneCochain I U n} (h : b.value = c.value) : b = c := by
  cases b
  cases c
  cases h
  rfl

/-- Equality of all total sign coefficient functions gives equality of raw cocycle records. -/
theorem cocycle_ext {z w : Cocycle I U n}
    (h : ∀ i j x, z.val.value i j x = w.val.value i j x) : z = w :=
  Subtype.ext (cochain_ext (funext fun i => funext fun j => funext (h i j)))

/-- Multiplication and inversion of cocycle representatives are the pointwise sign operations. -/
instance instCocycleCommGroup : CommGroup (Cocycle I U n) where
  one := unit I U n
  mul := SpinSignOneCocycle.mul
  inv := SpinSignOneCocycle.inv
  mul_assoc _ _ _ := cocycle_ext (fun _ _ _ => mul_assoc _ _ _)
  mul_comm _ _ := cocycle_ext (fun _ _ _ => mul_comm _ _)
  one_mul _ := cocycle_ext (fun _ _ _ => one_mul _)
  mul_one _ := cocycle_ext (fun _ _ _ => mul_one _)
  inv_mul_cancel _ := cocycle_ext (fun _ _ _ => inv_mul_cancel _)

/-- A chartwise change of sign valued in the physical kernel, smooth on the associated chart. -/
structure ZeroCochain (I : ModelWithCorners ℝ E H) (U : ι → TopologicalSpace.Opens B)
    (n : WithTop ℕ∞) where
  /-- The sign coefficient assigned to each chart. -/
  value : ι → B → Kernel
  /-- Smoothness of the ambient physical sign on the actual chart domain. -/
  smooth_value : ∀ i, ContMDiffOn I 𝓘(ℝ, CliffordSpinManifold.Model) n
    (fun x => (value i x).val) (U i : Set B)

/-- A chart sign is locally constant on its open domain because its Clifford kernel is discrete. -/
theorem isLocallyConstant_zeroOn (a : ZeroCochain I U n) (i : ι) :
    IsLocallyConstant (fun x : U i => a.value i x.val) :=
  (IsLocallyConstant.iff_continuous _).mpr ((a.smooth_value i).continuousOn.domRestrict.subtype_mk _)

/-- A chartwise gauge has the same sign at any two points of a preconnected chart. -/
theorem zero_eq_of_isPreconnected (a : ZeroCochain I U n) (i : ι)
    (h : IsPreconnected (U i : Set B)) (x y : U i) : a.value i x.val = a.value i y.val := by
  let _ : PreconnectedSpace (U i) := isPreconnected_iff_preconnectedSpace.mp h
  exact (isLocallyConstant_zeroOn a i).apply_eq_of_preconnectedSpace x y

/-- The neutral chartwise gauge is the constant physical sign one. -/
def zeroUnit (I : ModelWithCorners ℝ E H) (U : ι → TopologicalSpace.Opens B)
    (n : WithTop ℕ∞) : ZeroCochain I U n where
  value _ _ := 1
  smooth_value _ := contMDiffOn_const

/-- The product of two chartwise gauges multiplies their signs in each chart. -/
def zeroMul (a b : ZeroCochain I U n) : ZeroCochain I U n where
  value i x := a.value i x * b.value i x
  smooth_value i := (CliffordSpinManifold.contMDiff_mul n).comp_contMDiffOn
    ((a.smooth_value i).prodMk (b.smooth_value i))

/-- Reversing a chartwise gauge inverts its sign at every point. -/
def zeroInv (a : ZeroCochain I U n) : ZeroCochain I U n where
  value i x := (a.value i x)⁻¹
  smooth_value i := (CliffordSpinManifold.contMDiff_inv n).comp_contMDiffOn (a.smooth_value i)

/-- The coboundary taking source chart i to target chart j is the ratio of their chart signs. -/
def coboundary (a : ZeroCochain I U n) : Cocycle I U n := by
  refine ⟨{ value := fun i j x => a.value j x * (a.value i x)⁻¹,
            smooth_value := ?_, identity := ?_ }, ?_⟩
  · intro i j
    exact (CliffordSpinManifold.contMDiff_mul n).comp_contMDiffOn
      (((a.smooth_value j).mono inter_subset_right).prodMk
        ((CliffordSpinManifold.contMDiff_inv n).comp_contMDiffOn
          ((a.smooth_value i).mono inter_subset_left)))
  · intro i x _
    exact mul_inv_cancel _
  · intro i j k x _ _ _
    change (a.value k x * (a.value j x)⁻¹) * (a.value j x * (a.value i x)⁻¹) = _
    simp [mul_assoc]

/-- The neutral chart gauge has the unit degree-one coboundary. -/
theorem coboundary_zeroUnit :
    coboundary (zeroUnit I U n) = (1 : Cocycle I U n) := by
  apply cocycle_ext
  intro i j x
  change (1 : Kernel) * 1⁻¹ = 1
  simp

/-- Taking the coboundary commutes with multiplying two chartwise gauges. -/
theorem coboundary_zeroMul (a b : ZeroCochain I U n) :
    coboundary (zeroMul a b) = coboundary a * coboundary b := by
  apply cocycle_ext
  intro i j x
  change (a.value j x * b.value j x) * (a.value i x * b.value i x)⁻¹ =
    (a.value j x * (a.value i x)⁻¹) * (b.value j x * (b.value i x)⁻¹)
  simp [mul_comm, mul_left_comm, mul_assoc]

/-- Taking the coboundary commutes with inversion of the chartwise gauge. -/
theorem coboundary_zeroInv (a : ZeroCochain I U n) :
    coboundary (zeroInv a) = (coboundary a)⁻¹ := by
  apply cocycle_ext
  intro i j x
  change (a.value j x)⁻¹ * ((a.value i x)⁻¹)⁻¹ = (a.value j x * (a.value i x)⁻¹)⁻¹
  simp [mul_comm]

/-- Gauge-related cocycles differ by a chartwise sign coboundary on each pair overlap. -/
def GaugeRelated (z w : Cocycle I U n) : Prop :=
  ∃ a : ZeroCochain I U n, OverlapEq w (coboundary a * z)

/-- Agreement on the actual pair overlaps gives gauge equivalence with the unit chart signs. -/
theorem gaugeRelated_of_overlap {z w : Cocycle I U n} (h : OverlapEq z w) : GaugeRelated z w := by
  refine ⟨zeroUnit I U n, ?_⟩
  rw [coboundary_zeroUnit, one_mul]
  exact overlapEq_equivalence.symm h

/-- The inverse chart signs reverse a gauge equivalence of cocycles. -/
theorem gaugeRelated_symm {z w : Cocycle I U n} (h : GaugeRelated z w) : GaugeRelated w z := by
  obtain ⟨a, ha⟩ := h
  refine ⟨zeroInv a, ?_⟩
  rw [coboundary_zeroInv]
  have hk : OverlapEq ((coboundary a)⁻¹ * w) ((coboundary a)⁻¹ * (coboundary a * z)) :=
    overlapEq_mul (overlapEq_equivalence.refl _) ha
  rw [inv_mul_cancel_left] at hk
  exact overlapEq_equivalence.symm hk

/-- Products of the chart signs compose consecutive gauge equivalences. -/
theorem gaugeRelated_trans {z w v : Cocycle I U n} (h : GaugeRelated z w) (k : GaugeRelated w v) :
    GaugeRelated z v := by
  obtain ⟨a, ha⟩ := h
  obtain ⟨b, hb⟩ := k
  refine ⟨zeroMul b a, ?_⟩
  rw [coboundary_zeroMul, mul_assoc]
  exact overlapEq_equivalence.trans hb (overlapEq_mul (overlapEq_equivalence.refl _) ha)

/-- Multiplying two gauge-related pairs gives a gauge-related pair of products. -/
theorem gaugeRelated_mul {z z' w w' : Cocycle I U n} (h : GaugeRelated z z') (k : GaugeRelated w w') :
    GaugeRelated (z * w) (z' * w') := by
  obtain ⟨a, ha⟩ := h
  obtain ⟨b, hb⟩ := k
  refine ⟨zeroMul a b, ?_⟩
  rw [coboundary_zeroMul, mul_mul_mul_comm]
  exact overlapEq_mul ha hb

/-- Multiplicative congruence by actual smooth chartwise signs on a fixed open family. -/
def gaugeCon (I : ModelWithCorners ℝ E H) (U : ι → TopologicalSpace.Opens B)
    (n : WithTop ℕ∞) : Con (Cocycle I U n) where
  r := GaugeRelated
  iseqv := ⟨fun z => gaugeRelated_of_overlap (overlapEq_equivalence.refl z), gaugeRelated_symm,
    gaugeRelated_trans⟩
  mul' := gaugeRelated_mul

/-- The first cohomology group of smooth physical sign cochains on this fixed open family. -/
abbrev H1 (I : ModelWithCorners ℝ E H) (U : ι → TopologicalSpace.Opens B)
    (n : WithTop ℕ∞) := (gaugeCon I U n).Quotient

/-- The first cohomology class of a normalized smooth degree-one cocycle. -/
def classOf (z : Cocycle I U n) : H1 I U n := (z : (gaugeCon I U n).Quotient)

/-- Equality of fixed-cover degree-one classes means that a smooth chartwise gauge relates the representatives on true overlaps. -/
theorem classOf_eq_iff (z w : Cocycle I U n) : classOf z = classOf w ↔ GaugeRelated z w :=
  (gaugeCon I U n).eq

/-- Representatives with identical pair-overlap values determine the same first cohomology class. -/
theorem classOf_eq_of_overlap {z w : Cocycle I U n} (h : OverlapEq z w) : classOf z = classOf w :=
  (classOf_eq_iff z w).mpr (gaugeRelated_of_overlap h)

/-- The class map sends the neutral degree-one sign cocycle to the group identity. -/
theorem classOf_unit (I : ModelWithCorners ℝ E H) (U : ι → TopologicalSpace.Opens B)
    (n : WithTop ℕ∞) : classOf (unit I U n) = 1 := rfl

/-- Pointwise products of sign cocycles represent products of first cohomology classes. -/
theorem classOf_mul (z w : Cocycle I U n) : classOf (SpinSignOneCocycle.mul z w) = classOf z * classOf w := rfl

/-- Inverting the signs in a representative gives the inverse first cohomology class. -/
theorem classOf_inv (z : Cocycle I U n) : classOf (SpinSignOneCocycle.inv z) = (classOf z)⁻¹ := rfl

/-- Every smooth chartwise sign coboundary represents the neutral class. -/
theorem classOf_coboundary (a : ZeroCochain I U n) : classOf (coboundary a) = 1 := by
  rw [← classOf_unit I U n]
  symm
  apply (classOf_eq_iff _ _).mpr
  refine ⟨a, ?_⟩
  change OverlapEq (coboundary a) (coboundary a * 1)
  rw [mul_one]
  exact overlapEq_equivalence.refl _

/-- A degree-one class is neutral exactly when a smooth chart gauge has its pair coefficients on the true overlaps. -/
theorem classOf_eq_one_iff (z : Cocycle I U n) :
    classOf z = 1 ↔ ∃ a : ZeroCochain I U n, OverlapEq z (coboundary a) := by
  rw [← classOf_unit I U n, eq_comm, classOf_eq_iff]
  change (∃ a : ZeroCochain I U n, OverlapEq z (coboundary a * 1)) ↔ _
  simp only [mul_one]

/-- A property of first cohomology classes follows from checking it for every representative. -/
theorem induction_on {p : H1 I U n → Prop} (c : H1 I U n) (h : ∀ z, p (classOf z)) : p c :=
  Con.induction_on c h

/-- Each degree-one class has a normalized smooth cocycle representative. -/
theorem classOf_surjective : Function.Surjective (classOf (I := I) (U := U) (n := n)) :=
  fun c => induction_on (p := fun d => ∃ z, classOf z = d) c (fun z => ⟨z, rfl⟩)

end FoliationQM.SpinSignHOne
