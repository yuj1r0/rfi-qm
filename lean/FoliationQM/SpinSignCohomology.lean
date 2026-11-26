module
public import FoliationQM.CliffordSpinCocycleCorrection
public import Mathlib.Algebra.Group.IsCommutative

/-!
# The normalized degree-two sign class on a fixed open cover

Source scope: a geometric component of v13 `prop:takabayasi`. The
coefficients belong to the kernel of the physical Clifford homomorphism.
Cochains have total representatives, with smoothness, normalization and
cocycle equations imposed on the indicated intersections of opens. Two
cocycles represent the same class when a smooth normalized pair cochain
changes one into the other on their triple overlaps.
-/

@[expose] public section
noncomputable section
open Set
open scoped Manifold IsMulCommutative
namespace FoliationQM.SpinSignCohomology
open CliffordSpinSignKernel

variable {E H B ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  [TopologicalSpace B] [ChartedSpace H B] (U : ι → TopologicalSpace.Opens B)
  (n : WithTop ℕ∞)

/-- A smooth normalized sign coefficient for each ordered pair of cover indices. -/
structure OneCochain where
  /-- The coefficient lies in the physical sign kernel. -/
  value : ι → ι → B → Kernel
  /-- Its ambient Clifford value is smooth on the actual pair overlap. -/
  smooth_value : ∀ i j, ContMDiffOn I 𝓘(ℝ, CliffordSpinManifold.Model) n
    (fun x => (value i j x).val) ((U i : Set B) ∩ U j)
  /-- The coefficient of an actual diagonal transition is the unit. -/
  identity : ∀ i x, x ∈ U i → value i i x = 1

/-- A smooth degree-two sign cocycle with adjacent degeneracies normalized on the cover. -/
structure TwoCocycle where
  /-- The ordered triple coefficient in the physical sign kernel. -/
  value : ι → ι → ι → B → Kernel
  /-- Its ambient Clifford value is smooth on the actual triple overlap. -/
  smooth_value : ∀ i j k, ContMDiffOn I 𝓘(ℝ, CliffordSpinManifold.Model) n
    (fun x => (value i j k x).val) (((U i : Set B) ∩ U j) ∩ U k)
  /-- The first adjacent repeat gives the unit. -/
  self_left : ∀ i k x, x ∈ U i → x ∈ U k → value i i k x = 1
  /-- The second adjacent repeat gives the unit. -/
  self_right : ∀ i k x, x ∈ U i → x ∈ U k → value i k k x = 1
  /-- The degree-two cocycle law holds on every genuine quadruple overlap. -/
  quadruple : ∀ i j k l x, x ∈ U i → x ∈ U j → x ∈ U k → x ∈ U l →
    value j k l x * value i j l x = value i j k x * value i k l x

variable {I U n}

/-- The ordered multiplicative coboundary of an actual pair cochain. -/
def boundary (b : OneCochain I U n) (i j k : ι) (x : B) : Kernel :=
  b.value j k x * b.value i j x * (b.value i k x)⁻¹

/-- The constant unit coefficients form a normalized smooth pair cochain. -/
def unitCochain (I : ModelWithCorners ℝ E H) (U : ι → TopologicalSpace.Opens B) (n : WithTop ℕ∞) : OneCochain I U n where
  value _ _ _ := 1
  smooth_value _ _ := contMDiffOn_const
  identity _ _ _ := rfl

/-- Pointwise inverse in the actual sign kernel preserves smoothness and diagonal normalization. -/
def invCochain (b : OneCochain I U n) : OneCochain I U n where
  value i j x := (b.value i j x)⁻¹
  smooth_value i j := (CliffordSpinManifold.contMDiff_inv n).comp_contMDiffOn (b.smooth_value i j)
  identity i x hi := by simp only [b.identity i x hi, inv_one]

/-- Pointwise product of sign coefficients gives a smooth normalized pair cochain. -/
def mulCochain (b c : OneCochain I U n) : OneCochain I U n where
  value i j x := b.value i j x * c.value i j x
  smooth_value i j := (CliffordSpinManifold.contMDiff_mul n).comp_contMDiffOn
    ((b.smooth_value i j).prodMk (c.smooth_value i j))
  identity i x hi := by simp only [b.identity i x hi, c.identity i x hi, one_mul]

/-- The neutral pair cochain has unit coboundary on every triple. -/
theorem boundary_unit (i j k : ι) (x : B) :
    boundary (unitCochain I U n) i j k x = 1 := by simp [boundary, unitCochain]

/-- The coboundary of the inverse cochain is the inverse of the coboundary. -/
theorem boundary_inv (b : OneCochain I U n) (i j k : ι) (x : B) :
    boundary (invCochain b) i j k x = (boundary b i j k x)⁻¹ := by
  simp [boundary, invCochain, mul_comm, mul_left_comm, mul_assoc]

/-- The coboundary carries pointwise products of smooth sign cochains to products. -/
theorem boundary_mul (b c : OneCochain I U n) (i j k : ι) (x : B) :
    boundary (mulCochain b c) i j k x = boundary b i j k x * boundary c i j k x := by
  simp [boundary, mulCochain, mul_comm, mul_left_comm, mul_assoc]

/-- The coboundary itself is a smooth normalized degree-two cocycle on the original opens. -/
def boundaryCocycle (b : OneCochain I U n) : TwoCocycle I U n where
  value := boundary b
  smooth_value i j k := by
    exact (CliffordSpinManifold.contMDiff_mul n).comp_contMDiffOn
      (((CliffordSpinManifold.contMDiff_mul n).comp_contMDiffOn
        (((b.smooth_value j k).mono (fun _ h => ⟨h.1.2, h.2⟩)).prodMk
          ((b.smooth_value i j).mono (fun _ h => h.1)))).prodMk
        ((CliffordSpinManifold.contMDiff_inv n).comp_contMDiffOn
          ((b.smooth_value i k).mono (fun _ h => ⟨h.1.1, h.2⟩))))
  self_left i k x hi _ := by simp [boundary, b.identity i x hi]
  self_right i k x _ hk := by simp [boundary, b.identity k x hk]
  quadruple i j k l x _ _ _ _ :=
    CentralTransitionDefect.defect_quadruple (fun a c => b.value a c x) i j k l (mul_comm _ _)

/-- Two smooth normalized degree-two cocycles differ by a smooth pair coboundary on the actual triple overlaps. -/
def Related (z w : TwoCocycle I U n) : Prop :=
  ∃ b : OneCochain I U n, ∀ i j k x, x ∈ U i → x ∈ U j → x ∈ U k →
    w.value i j k x = boundary b i j k x * z.value i j k x

/-- The neutral pair coefficient relates a normalized cocycle to itself. -/
theorem related_refl (z : TwoCocycle I U n) : Related z z := by
  refine ⟨unitCochain I U n, fun i j k x _ _ _ => ?_⟩
  rw [boundary_unit, one_mul]

/-- Inverting an actual smooth pair coefficient reverses a change of representative. -/
theorem related_symm {z w : TwoCocycle I U n} (h : Related z w) : Related w z := by
  obtain ⟨b, hb⟩ := h
  refine ⟨invCochain b, fun i j k x hi hj hk => ?_⟩
  rw [boundary_inv, hb i j k x hi hj hk, inv_mul_cancel_left]

/-- Composing smooth pair corrections gives transitivity for overlap representatives. -/
theorem related_trans {z w v : TwoCocycle I U n} (h : Related z w) (h' : Related w v) :
    Related z v := by
  obtain ⟨b, hb⟩ := h
  obtain ⟨c, hc⟩ := h'
  refine ⟨mulCochain c b, fun i j k x hi hj hk => ?_⟩
  rw [boundary_mul, hc i j k x hi hj hk, hb i j k x hi hj hk, mul_assoc]

/-- The fixed-cover equivalence relation by smooth central pair coboundaries. -/
def signSetoid (I : ModelWithCorners ℝ E H) (U : ι → TopologicalSpace.Opens B) (n : WithTop ℕ∞) : Setoid (TwoCocycle I U n) where
  r := Related
  iseqv := ⟨related_refl, fun h => related_symm h, fun h h' => related_trans h h'⟩

/-- The fixed-cover degree-two obstruction class space for the physical sign kernel. -/
def ObstructionClass (I : ModelWithCorners ℝ E H) (U : ι → TopologicalSpace.Opens B) (n : WithTop ℕ∞) := Quotient (signSetoid I U n)

/-- The equivalence class represented by a smooth normalized sign cocycle. -/
def classOf (z : TwoCocycle I U n) : ObstructionClass I U n := Quotient.mk _ z

/-- The constant unit sign is a smooth normalized degree-two cocycle. -/
def neutralCocycle (I : ModelWithCorners ℝ E H) (U : ι → TopologicalSpace.Opens B) (n : WithTop ℕ∞) : TwoCocycle I U n where
  value _ _ _ _ := 1
  smooth_value _ _ _ := contMDiffOn_const
  self_left _ _ _ _ _ := rfl
  self_right _ _ _ _ _ := rfl
  quadruple _ _ _ _ _ _ _ _ _ := rfl

/-- The distinguished neutral class on the fixed open cover. -/
def neutralClass (I : ModelWithCorners ℝ E H) (U : ι → TopologicalSpace.Opens B) (n : WithTop ℕ∞) : ObstructionClass I U n := classOf (neutralCocycle I U n)

/-- Equality of fixed-cover classes is equivalent to an actual smooth normalized pair coboundary between the representatives on genuine triple overlaps. -/
theorem classOf_eq_iff (z w : TwoCocycle I U n) : classOf z = classOf w ↔ Related z w :=
  Quotient.eq

/-- The class of the coboundary of a smooth normalized pair cochain is neutral. -/
theorem classOf_boundary (b : OneCochain I U n) :
    classOf (boundaryCocycle b) = neutralClass I U n := by
  symm
  apply (classOf_eq_iff _ _).mpr
  refine ⟨b, fun i j k x _ _ _ => ?_⟩
  change boundary b i j k x = boundary b i j k x * 1
  rw [mul_one]

end FoliationQM.SpinSignCohomology
