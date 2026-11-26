module
public import FoliationQM.ModTwoCohomology
public import Mathlib.Topology.Sets.Opens

/-!
# Pullback of locally constant mod-two degree-two cohomology

For the characteristic-class comparison supporting v13 `prop:takabayasi`,
a continuous map pulls an open family back to its open preimages.
Composing the coefficients with this map preserves local constancy on the
actual overlaps, normalized cocycles and their additive coboundaries.
This defines the contravariant map on fixed-cover cohomology.
-/

@[expose] public section
open Set TopologicalSpace
namespace FoliationQM.ModTwoPullback
open ModTwoCohomology

variable {B X Y ι : Type*} [TopologicalSpace B] [TopologicalSpace X] [TopologicalSpace Y]

/-- Pull each original open back along the continuous base map, retaining the original indices. -/
def domain (f : C(X, B)) (U : ι → Opens B) (i : ι) : Opens X := Opens.comap f (U i)

/-- Membership in the pulled-back open is membership of the image in the original open. -/
theorem mem_domain (f : C(X, B)) (U : ι → Opens B) (i : ι) (x : X) :
    x ∈ domain f U i ↔ f x ∈ U i := Iff.rfl

/-- The preimages cover whenever the original domains do. -/
theorem covers (f : C(X, B)) {U : ι → Opens B} (hU : ∀ b, ∃ i, b ∈ U i) :
    ∀ x, ∃ i, x ∈ domain f U i := fun x => hU (f x)

/-- Pullback by the identity retains the original open family. -/
theorem domain_id (U : ι → Opens B) : domain (ContinuousMap.id B) U = U := rfl

/-- Two successive open preimages are the preimage by the composite. -/
theorem domain_comp (f : C(X, B)) (g : C(Y, X)) (U : ι → Opens B) :
    domain g (domain f U) = domain (f.comp g) U := rfl

/-- The base map on an actual pair overlap, valued in the corresponding original pair. -/
def pairMap (f : C(X, B)) (U : ι → Opens B) (i j : ι) :
    C(↥((domain f U i : Set X) ∩ domain f U j), ↥((U i : Set B) ∩ U j)) :=
  ⟨fun x => ⟨f x.val, x.property⟩,
    (f.continuous.comp continuous_subtype_val).subtype_mk _⟩

/-- The base map on an actual triple overlap, valued in the corresponding original triple. -/
def tripleMap (f : C(X, B)) (U : ι → Opens B) (i j k : ι) :
    C(↥(((domain f U i : Set X) ∩ domain f U j) ∩ domain f U k),
      ↥(((U i : Set B) ∩ U j) ∩ U k)) :=
  ⟨fun x => ⟨f x.val, x.property⟩,
    (f.continuous.comp continuous_subtype_val).subtype_mk _⟩

variable {U : ι → Opens B}

/-- Pull back a normalized pair cochain by composing its actual coefficients with the base map. -/
def one (f : C(X, B)) (b : OneCochain U) : OneCochain (domain f U) where
  value i j x := b.value i j (f x)
  local_value i j := (b.local_value i j).comp_continuous (pairMap f U i j).continuous
  identity i x hx := b.identity i (f x) hx

/-- The pulled-back pair coefficient has the original value at the image point. -/
theorem one_value (f : C(X, B)) (b : OneCochain U) (i j : ι) (x : X) :
    (one f b).value i j x = b.value i j (f x) := rfl

/-- Normalization and the quadruple equation pull back on the actual preimage intersections. -/
def two (f : C(X, B)) (z : TwoCocycle U) : TwoCocycle (domain f U) where
  value i j k x := z.value i j k (f x)
  local_value i j k := (z.local_value i j k).comp_continuous (tripleMap f U i j k).continuous
  self_left i k x hi hk := z.self_left i k (f x) hi hk
  self_right i k x hi hk := z.self_right i k (f x) hi hk
  quadruple i j k l x hi hj hk hl := z.quadruple i j k l (f x) hi hj hk hl

/-- The pulled-back triple coefficient has the original value at the image point. -/
theorem two_value (f : C(X, B)) (z : TwoCocycle U) (i j k : ι) (x : X) :
    (two f z).value i j k x = z.value i j k (f x) := rfl

/-- Pullback commutes with the full additive pair-coboundary cocycle. -/
theorem two_boundaryCocycle (f : C(X, B)) (b : OneCochain U) :
    two f (boundaryCocycle b) = boundaryCocycle (one f b) := rfl

/-- The pulled-back pair correction witnesses the coboundary relation of the pulled-back cocycles. -/
theorem related (f : C(X, B)) {z w : TwoCocycle U} (h : Related z w) : Related (two f z) (two f w) := by
  obtain ⟨b, hb⟩ := h
  exact ⟨one f b, fun i j k x hi hj hk => hb i j k (f x) hi hj hk⟩

/-- A continuous base map induces an additive pullback on fixed-cover cohomology. -/
def hom (f : C(X, B)) (U : ι → Opens B) : H2 U →+ H2 (domain f U) where
  toFun := Quotient.lift (fun z => classOf (two f z))
    (fun _ _ h => (classOf_eq_iff _ _).mpr (related f h))
  map_zero' := rfl
  map_add' c d := Quotient.inductionOn₂ c d (fun _ _ => rfl)

/-- The pullback of a represented class is represented by the actual pulled-back coefficients. -/
theorem hom_classOf (f : C(X, B)) (z : TwoCocycle U) :
    hom f U (classOf z) = classOf (two f z) := rfl

/-- Pullback by the identity fixes every fixed-cover cohomology class. -/
theorem hom_id (U : ι → Opens B) (c : H2 U) : hom (ContinuousMap.id B) U c = c := by
  obtain ⟨z, rfl⟩ := classOf_surjective c
  rfl

/-- Pullback of a composite acts by the two component pullbacks in reverse order. -/
theorem hom_comp (f : C(X, B)) (g : C(Y, X)) (U : ι → Opens B) (c : H2 U) :
    hom g (domain f U) (hom f U c) = hom (f.comp g) U c := by
  obtain ⟨z, rfl⟩ := classOf_surjective c
  rfl

end FoliationQM.ModTwoPullback
