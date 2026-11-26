module
public import FoliationQM.SpinSignCohomology

/-!
# Smooth degree-one cocycles of physical Clifford signs

The global Spin-frame component of v13 `prop:takabayasi` compares lifts
of the same Lorentz transitions. Its coefficients lie in the actual
Clifford sign kernel. The degree-one law composes the transition from
chart i to chart j with that from j to k on their triple intersection.
-/

@[expose] public section
noncomputable section
open Set
open scoped Manifold IsMulCommutative
namespace FoliationQM.SpinSignOneCocycle
open CliffordSpinSignKernel SpinSignCohomology

variable {E H B ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace B] [ChartedSpace H B] {U : ι → TopologicalSpace.Opens B}
  {n : WithTop ℕ∞}

/-- A normalized smooth pair cochain is a cocycle when its signs compose in chart order on each triple overlap. -/
def IsCocycle (b : OneCochain I U n) : Prop :=
  ∀ i j k x, x ∈ U i → x ∈ U j → x ∈ U k →
    b.value j k x * b.value i j x = b.value i k x

/-- Smooth normalized Clifford-sign one-cocycles on the given open family. -/
abbrev Cocycle (I : ModelWithCorners ℝ E H) (U : ι → TopologicalSpace.Opens B)
    (n : WithTop ℕ∞) := {b : OneCochain I U n // IsCocycle b}

/-- The ordered coboundary at a point equals the unit exactly when the corresponding pair coefficients compose. -/
theorem boundary_eq_one_iff (b : OneCochain I U n) (i j k : ι) (x : B) :
    boundary b i j k x = 1 ↔ b.value j k x * b.value i j x = b.value i k x :=
  mul_inv_eq_one

/-- The degree-one cocycle law is equivalent to unit coboundary on every actual triple overlap. -/
theorem isCocycle_iff_boundary (b : OneCochain I U n) :
    IsCocycle b ↔ ∀ i j k x, x ∈ U i → x ∈ U j → x ∈ U k → boundary b i j k x = 1 := by
  constructor
  · intro h i j k x hi hj hk
    exact (boundary_eq_one_iff b i j k x).mpr (h i j k x hi hj hk)
  · intro h i j k x hi hj hk
    exact (boundary_eq_one_iff b i j k x).mp (h i j k x hi hj hk)

/-- The constant unit sign gives the neutral smooth degree-one cocycle. -/
def unit (I : ModelWithCorners ℝ E H) (U : ι → TopologicalSpace.Opens B)
    (n : WithTop ℕ∞) : Cocycle I U n :=
  ⟨unitCochain I U n, (isCocycle_iff_boundary _).mpr (fun i j k x _ _ _ => boundary_unit i j k x)⟩

/-- Products of degree-one sign cocycles retain the cocycle law because their coboundaries multiply. -/
def mul (z w : Cocycle I U n) : Cocycle I U n := by
  refine ⟨mulCochain z.val w.val, (isCocycle_iff_boundary _).mpr ?_⟩
  intro i j k x hi hj hk
  rw [boundary_mul, (isCocycle_iff_boundary _).mp z.property i j k x hi hj hk,
    (isCocycle_iff_boundary _).mp w.property i j k x hi hj hk, one_mul]

/-- Inverting the smooth sign coefficients gives the inverse degree-one cocycle. -/
def inv (z : Cocycle I U n) : Cocycle I U n := by
  refine ⟨invCochain z.val, (isCocycle_iff_boundary _).mpr ?_⟩
  intro i j k x hi hj hk
  rw [boundary_inv, (isCocycle_iff_boundary _).mp z.property i j k x hi hj hk, inv_one]

/-- Reversing an actual chart pair inverts its coefficient, by composition through the repeated first chart. -/
theorem reverse (z : Cocycle I U n) (i j : ι) (x : B) (hi : x ∈ U i) (hj : x ∈ U j) :
    z.val.value j i x = (z.val.value i j x)⁻¹ :=
  eq_inv_of_mul_eq_one_left ((z.property i j i x hi hj hi).trans (z.val.identity i x hi))

/-- The sign coefficient is continuous into the actual discrete Clifford kernel on the pair-overlap subtype. -/
theorem continuous_onPair (z : Cocycle I U n) (i j : ι) :
    Continuous (fun x : ↥((U i : Set B) ∩ U j) => z.val.value i j x.val) :=
  (z.val.smooth_value i j).continuousOn.domRestrict.subtype_mk _

/-- A smooth sign cocycle has locally constant coefficients on the true pair overlaps. -/
theorem isLocallyConstant_onPair (z : Cocycle I U n) (i j : ι) :
    IsLocallyConstant (fun x : ↥((U i : Set B) ∩ U j) => z.val.value i j x.val) :=
  (IsLocallyConstant.iff_continuous _).mpr (continuous_onPair z i j)

/-- Two degree-one representatives agree geometrically when their coefficients agree on every pair overlap. -/
def OverlapEq (z w : Cocycle I U n) : Prop :=
  ∀ i j x, x ∈ U i → x ∈ U j → z.val.value i j x = w.val.value i j x

/-- Pair-overlap equality is an equivalence relation on normalized smooth sign cocycles. -/
theorem overlapEq_equivalence : Equivalence (OverlapEq (I := I) (U := U) (n := n)) :=
  ⟨fun _ _ _ _ _ _ => rfl,
    fun h i j x hi hj => (h i j x hi hj).symm,
    fun h k i j x hi hj => (h i j x hi hj).trans (k i j x hi hj)⟩

/-- Equality on the actual overlaps is preserved by pointwise multiplication of cocycles. -/
theorem overlapEq_mul {z z' w w' : Cocycle I U n}
    (hz : OverlapEq z z') (hw : OverlapEq w w') : OverlapEq (mul z w) (mul z' w') :=
  fun i j x hi hj => congrArg₂ (· * ·) (hz i j x hi hj) (hw i j x hi hj)

/-- Equality on the actual overlaps is preserved by inversion. -/
theorem overlapEq_inv {z w : Cocycle I U n} (h : OverlapEq z w) : OverlapEq (inv z) (inv w) :=
  fun i j x hi hj => congrArg Inv.inv (h i j x hi hj)

end FoliationQM.SpinSignOneCocycle
