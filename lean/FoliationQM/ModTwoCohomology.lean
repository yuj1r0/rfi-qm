module
public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.Data.ZMod.Basic
public import Mathlib.GroupTheory.Congruence.Defs
public import Mathlib.Tactic.Abel

/-!
# Normalized locally constant degree-two cohomology with mod-two coefficients

For the Spin-frame component of v13 `prop:takabayasi`, this construction
uses the topology of a base and its open family. Values belong to the
additive group ZMod 2. Local constancy and all cocycle equations are
imposed on the actual intersections of the specified opens.
-/

@[expose] public section
noncomputable section
open Set
namespace FoliationQM.ModTwoCohomology

variable {B ι : Type*} [TopologicalSpace B] (U : ι → TopologicalSpace.Opens B)

/-- A normalized pair coefficient, locally constant on the actual pair overlap. -/
structure OneCochain where
  /-- The total representative of the pair coefficient. -/
  value : ι → ι → B → ZMod 2
  /-- Local constancy only on the original pair intersection. -/
  local_value : ∀ i j, IsLocallyConstant (fun x : ↥((U i : Set B) ∩ U j) => value i j x)
  /-- Normalization on a true diagonal. -/
  identity : ∀ i x, x ∈ U i → value i i x = 0

/-- A normalized two-cocycle with locally constant mod-two coefficients. -/
structure TwoCocycle where
  /-- The total representative of the triple coefficient. -/
  value : ι → ι → ι → B → ZMod 2
  /-- Local constancy on the true triple intersection. -/
  local_value : ∀ i j k, IsLocallyConstant (fun x : ↥(((U i : Set B) ∩ U j) ∩ U k) => value i j k x)
  /-- The first adjacent repeated index has zero coefficient. -/
  self_left : ∀ i k x, x ∈ U i → x ∈ U k → value i i k x = 0
  /-- The second adjacent repeated index has zero coefficient. -/
  self_right : ∀ i k x, x ∈ U i → x ∈ U k → value i k k x = 0
  /-- The degree-two equation holds on each actual quadruple intersection. -/
  quadruple : ∀ i j k l x, x ∈ U i → x ∈ U j → x ∈ U k → x ∈ U l →
    value j k l x + value i j l x = value i j k x + value i k l x

variable {U}

/-- Restricting the source subset preserves local constancy of a total coefficient. -/
theorem local_mono {s t : Set B} (h : s ⊆ t) {f : B → ZMod 2}
    (hf : IsLocallyConstant (fun x : t => f x)) : IsLocallyConstant (fun x : s => f x) :=
  hf.comp_continuous (continuous_subtype_val.subtype_mk (fun x => h x.property))

/-- Total equality of the pair coefficients determines the cochain. -/
theorem one_ext {b c : OneCochain U} (h : ∀ i j x, b.value i j x = c.value i j x) : b = c := by
  have hv : b.value = c.value := funext fun i => funext fun j => funext (h i j)
  cases b
  cases c
  cases hv
  rfl

/-- Total equality of the triple coefficients determines the cocycle. -/
theorem cocycle_ext {z w : TwoCocycle U} (h : ∀ i j k x, z.value i j k x = w.value i j k x) : z = w := by
  have hv : z.value = w.value := funext fun i => funext fun j => funext fun k => funext (h i j k)
  cases z
  cases w
  cases hv
  rfl

instance : Zero (OneCochain U) where
  zero := ⟨fun _ _ _ => 0, fun _ _ => IsLocallyConstant.const _, fun _ _ _ => rfl⟩

instance : Add (OneCochain U) where
  add b c := ⟨fun i j x => b.value i j x + c.value i j x,
    fun i j => (b.local_value i j).add (c.local_value i j),
    fun i x hx => by rw [b.identity i x hx, c.identity i x hx, zero_add]⟩

instance : Neg (OneCochain U) where
  neg b := ⟨fun i j x => -b.value i j x, fun i j => (b.local_value i j).neg,
    fun i x hx => by rw [b.identity i x hx, neg_zero]⟩

instance : AddCommGroup (OneCochain U) where
  add_assoc _ _ _ := one_ext (fun _ _ _ => add_assoc _ _ _)
  add_comm _ _ := one_ext (fun _ _ _ => add_comm _ _)
  zero_add _ := one_ext (fun _ _ _ => zero_add _)
  add_zero _ := one_ext (fun _ _ _ => add_zero _)
  neg_add_cancel _ := one_ext (fun _ _ _ => neg_add_cancel _)
  nsmul := nsmulRec
  zsmul := zsmulRec

instance : Zero (TwoCocycle U) where
  zero := ⟨fun _ _ _ _ => 0, fun _ _ _ => IsLocallyConstant.const _,
    fun _ _ _ _ _ => rfl, fun _ _ _ _ _ => rfl, fun _ _ _ _ _ _ _ _ _ => rfl⟩

instance : Add (TwoCocycle U) where
  add z w :=
    { value := fun i j k x => z.value i j k x + w.value i j k x
      local_value := fun i j k => (z.local_value i j k).add (w.local_value i j k)
      self_left := fun i k x hi hk => by rw [z.self_left i k x hi hk, w.self_left i k x hi hk, zero_add]
      self_right := fun i k x hi hk => by rw [z.self_right i k x hi hk, w.self_right i k x hi hk, zero_add]
      quadruple := fun i j k l x hi hj hk hl => by
        rw [add_add_add_comm, z.quadruple i j k l x hi hj hk hl,
          w.quadruple i j k l x hi hj hk hl, add_add_add_comm] }

instance : Neg (TwoCocycle U) where
  neg z :=
    { value := fun i j k x => -z.value i j k x
      local_value := fun i j k => (z.local_value i j k).neg
      self_left := fun i k x hi hk => by rw [z.self_left i k x hi hk, neg_zero]
      self_right := fun i k x hi hk => by rw [z.self_right i k x hi hk, neg_zero]
      quadruple := fun i j k l x hi hj hk hl => by
        simpa only [neg_add] using congrArg Neg.neg (z.quadruple i j k l x hi hj hk hl) }

instance : AddCommGroup (TwoCocycle U) where
  add_assoc _ _ _ := cocycle_ext (fun _ _ _ _ => add_assoc _ _ _)
  add_comm _ _ := cocycle_ext (fun _ _ _ _ => add_comm _ _)
  zero_add _ := cocycle_ext (fun _ _ _ _ => zero_add _)
  add_zero _ := cocycle_ext (fun _ _ _ _ => add_zero _)
  neg_add_cancel _ := cocycle_ext (fun _ _ _ _ => neg_add_cancel _)
  nsmul := nsmulRec
  zsmul := zsmulRec

/-- The additive pair coboundary on an ordered triple. -/
def boundary (b : OneCochain U) (i j k : ι) (x : B) : ZMod 2 :=
  b.value j k x + b.value i j x - b.value i k x

/-- The zero pair cochain has zero coboundary. -/
theorem boundary_zero (i j k : ι) (x : B) : boundary (0 : OneCochain U) i j k x = 0 := by
  change (0 : ZMod 2) + 0 - 0 = 0
  simp

/-- The coboundary respects addition of locally constant pair coefficients. -/
theorem boundary_add (b c : OneCochain U) (i j k : ι) (x : B) :
    boundary (b + c) i j k x = boundary b i j k x + boundary c i j k x := by
  change (b.value j k x + c.value j k x) + (b.value i j x + c.value i j x) -
    (b.value i k x + c.value i k x) = _
  simp only [boundary]
  abel

/-- The negative pair coefficient has the negative coboundary. -/
theorem boundary_neg (b : OneCochain U) (i j k : ι) (x : B) :
    boundary (-b) i j k x = -boundary b i j k x := by
  change -b.value j k x + -b.value i j x - -b.value i k x = _
  simp only [boundary]
  abel

/-- An actual locally constant pair coboundary is a normalized degree-two cocycle. -/
def boundaryCocycle (b : OneCochain U) : TwoCocycle U where
  value := boundary b
  local_value i j k :=
    ((local_mono (s := ((U i : Set B) ∩ U j) ∩ U k) (t := (U j : Set B) ∩ U k) (fun _ h => ⟨h.1.2, h.2⟩) (b.local_value j k)).add
      (local_mono (s := ((U i : Set B) ∩ U j) ∩ U k) (t := (U i : Set B) ∩ U j) (fun _ h => h.1) (b.local_value i j))).sub
      (local_mono (s := ((U i : Set B) ∩ U j) ∩ U k) (t := (U i : Set B) ∩ U k) (fun _ h => ⟨h.1.1, h.2⟩) (b.local_value i k))
  self_left i k x hi _ := by simp [boundary, b.identity i x hi]
  self_right i k x _ hk := by simp [boundary, b.identity k x hk]
  quadruple i j k l x _ _ _ _ := by simp only [boundary]; abel

/-- Representatives differ by a normalized locally constant pair coboundary on true triples. -/
def Related (z w : TwoCocycle U) : Prop :=
  ∃ b : OneCochain U, ∀ i j k x, x ∈ U i → x ∈ U j → x ∈ U k →
    w.value i j k x = boundary b i j k x + z.value i j k x

/-- The zero cochain relates a representative to itself. -/
theorem related_refl (z : TwoCocycle U) : Related z z := by
  refine ⟨0, fun i j k x _ _ _ => ?_⟩
  rw [boundary_zero, zero_add]

/-- Negating a pair correction reverses the relation. -/
theorem related_symm {z w : TwoCocycle U} (h : Related z w) : Related w z := by
  obtain ⟨b, hb⟩ := h
  refine ⟨-b, fun i j k x hi hj hk => ?_⟩
  rw [boundary_neg, hb i j k x hi hj hk, neg_add_cancel_left]

/-- Adding pair corrections composes the relation. -/
theorem related_trans {z w v : TwoCocycle U} (h : Related z w) (h' : Related w v) : Related z v := by
  obtain ⟨b, hb⟩ := h
  obtain ⟨c, hc⟩ := h'
  refine ⟨c + b, fun i j k x hi hj hk => ?_⟩
  rw [boundary_add, hc i j k x hi hj hk, hb i j k x hi hj hk, add_assoc]

/-- Adding two relations gives a relation of the sums of representatives. -/
theorem related_add {z z' w w' : TwoCocycle U} (h : Related z z') (k : Related w w') :
    Related (z + w) (z' + w') := by
  obtain ⟨a, ha⟩ := h
  obtain ⟨b, hb⟩ := k
  refine ⟨a + b, fun i j k x hi hj hk => ?_⟩
  change z'.value i j k x + w'.value i j k x = boundary (a + b) i j k x +
    (z.value i j k x + w.value i j k x)
  rw [boundary_add, ha i j k x hi hj hk, hb i j k x hi hj hk, add_add_add_comm]

/-- Congruence by actual normalized locally constant pair coboundaries. -/
def coboundaryCon (U : ι → TopologicalSpace.Opens B) : AddCon (TwoCocycle U) where
  r := Related
  iseqv := ⟨related_refl, related_symm, related_trans⟩
  add' := related_add

/-- The fixed-cover second cohomology group of locally constant mod-two coefficients. -/
abbrev H2 (U : ι → TopologicalSpace.Opens B) := (coboundaryCon U).Quotient

/-- The cohomology class represented by a normalized locally constant cocycle. -/
def classOf (z : TwoCocycle U) : H2 U := (z : (coboundaryCon U).Quotient)

/-- Class equality is the actual locally constant coboundary relation on triple overlaps. -/
theorem classOf_eq_iff (z w : TwoCocycle U) : classOf z = classOf w ↔ Related z w := Quotient.eq

/-- Agreement on the true triple overlaps gives equal classes. -/
theorem classOf_eq_of_eqOn {z w : TwoCocycle U}
    (h : ∀ i j k x, x ∈ U i → x ∈ U j → x ∈ U k → z.value i j k x = w.value i j k x) :
    classOf z = classOf w := by
  apply (classOf_eq_iff _ _).mpr
  refine ⟨0, fun i j k x hi hj hk => ?_⟩
  rw [boundary_zero, zero_add]
  exact (h i j k x hi hj hk).symm

/-- Every class has a normalized locally constant cocycle representative. -/
theorem classOf_surjective : Function.Surjective (classOf (U := U)) :=
  fun c => Quotient.inductionOn c (fun z => ⟨z, rfl⟩)

/-- The zero cocycle gives the additive identity class. -/
theorem classOf_zero : classOf (0 : TwoCocycle U) = 0 := rfl

/-- Addition of cocycles represents addition in the fixed-cover group. -/
theorem classOf_add (z w : TwoCocycle U) : classOf (z + w) = classOf z + classOf w := rfl

/-- Negation of a cocycle represents negation of its class. -/
theorem classOf_neg (z : TwoCocycle U) : classOf (-z) = -classOf z := rfl

/-- Every pair coboundary represents zero. -/
theorem classOf_boundary (b : OneCochain U) : classOf (boundaryCocycle b) = 0 := by
  symm
  apply (classOf_eq_iff _ _).mpr
  exact ⟨b, fun _ _ _ _ _ _ _ => (add_zero _).symm⟩

end FoliationQM.ModTwoCohomology
