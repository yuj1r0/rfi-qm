module
public import FoliationQM.ModTwoCohomology
public import FoliationQM.SpinRefinementComposition
public import Mathlib.Tactic.LinearCombination

/-!
# Restriction and parent independence for mod-two cohomology

For the Spin-frame component of v13 `prop:takabayasi`, restricting the
locally constant coefficients and their additive coboundaries gives group
homomorphisms. The mixed-triple prism compares two parent assignments on
the same refined opens using the additive quadruple equation.
-/

@[expose] public section
noncomputable section
open Set
namespace FoliationQM.ModTwoRestriction
open CliffordSpinCoverRefinement SpinRefinementComposition ModTwoCohomology

variable {B ι κ τ : Type*} [TopologicalSpace B] {U : ι → TopologicalSpace.Opens B}

/-- Restrict a pair coefficient using each refined chart's containing parent. -/
def restrictOne (R : Refinement U κ) (b : OneCochain U) : OneCochain R.domain where
  value i j := b.value (R.parent i) (R.parent j)
  local_value i j := local_mono
    (s := (R.domain i : Set B) ∩ R.domain j)
    (t := (U (R.parent i) : Set B) ∩ U (R.parent j))
    (fun _ hx => ⟨R.subset i hx.1, R.subset j hx.2⟩) (b.local_value _ _)
  identity i x hi := b.identity _ x (R.subset i hi)

/-- Restriction retains the literal parent pair coefficient. -/
theorem restrictOne_value (R : Refinement U κ) (b : OneCochain U) (i j : κ) (x : B) :
    (restrictOne R b).value i j x = b.value (R.parent i) (R.parent j) x := rfl

/-- Restrict a normalized two-cocycle using the original parent triple. -/
def restrictTwo (R : Refinement U κ) (z : TwoCocycle U) : TwoCocycle R.domain where
  value i j k := z.value (R.parent i) (R.parent j) (R.parent k)
  local_value i j k := local_mono
    (s := ((R.domain i : Set B) ∩ R.domain j) ∩ R.domain k)
    (t := ((U (R.parent i) : Set B) ∩ U (R.parent j)) ∩ U (R.parent k))
    (fun _ hx => ⟨⟨R.subset i hx.1.1, R.subset j hx.1.2⟩, R.subset k hx.2⟩) (z.local_value _ _ _)
  self_left i k x hi hk := z.self_left _ _ x (R.subset i hi) (R.subset k hk)
  self_right i k x hi hk := z.self_right _ _ x (R.subset i hi) (R.subset k hk)
  quadruple i j k l x hi hj hk hl := z.quadruple _ _ _ _ x
    (R.subset i hi) (R.subset j hj) (R.subset k hk) (R.subset l hl)

/-- Restriction retains the literal parent triple coefficient. -/
theorem restrictTwo_value (R : Refinement U κ) (z : TwoCocycle U) (i j k : κ) (x : B) :
    (restrictTwo R z).value i j k x = z.value (R.parent i) (R.parent j) (R.parent k) x := rfl

/-- Restriction commutes with the entire additive coboundary cocycle. -/
theorem restrictTwo_boundaryCocycle (R : Refinement U κ) (b : OneCochain U) :
    restrictTwo R (boundaryCocycle b) = boundaryCocycle (restrictOne R b) := rfl

/-- A locally constant pair correction restricts to a correction on the refined triples. -/
theorem restrict_related (R : Refinement U κ) {z w : TwoCocycle U} (h : Related z w) :
    Related (restrictTwo R z) (restrictTwo R w) := by
  obtain ⟨b, hb⟩ := h
  exact ⟨restrictOne R b, fun i j k x hi hj hk =>
    hb _ _ _ x (R.subset i hi) (R.subset j hj) (R.subset k hk)⟩

/-- Restricting normalized locally constant mod-two classes gives an additive homomorphism. -/
def restrictHom (R : Refinement U κ) : H2 U →+ H2 R.domain where
  toFun := Quotient.lift (fun z => classOf (restrictTwo R z))
    (fun _ _ h => (classOf_eq_iff _ _).mpr (restrict_related R h))
  map_zero' := rfl
  map_add' c d := Quotient.inductionOn₂ c d (fun _ _ => rfl)

/-- The restricted class is represented by the restricted parent coefficients. -/
theorem restrictHom_classOf (R : Refinement U κ) (z : TwoCocycle U) :
    restrictHom R (classOf z) = classOf (restrictTwo R z) := rfl

/-- The identity cover refinement preserves every mod-two class. -/
theorem restrictHom_identity (hU : ∀ x : B, ∃ i, x ∈ U i) (c : H2 U) :
    restrictHom (identity U hU) c = c := by
  obtain ⟨z, rfl⟩ := classOf_surjective c
  rfl

/-- Restriction along two consecutive refinements is restriction along their composite. -/
theorem restrictHom_compose (R : Refinement U κ) (S : Refinement R.domain τ) (c : H2 U) :
    restrictHom S (restrictHom R c) = restrictHom (compose R S) c := by
  obtain ⟨z, rfl⟩ := classOf_surjective c
  rfl

/-- A second containing-parent choice on the same refined opens. -/
def reparent (R : Refinement U κ) (q : κ → ι) (hq : ∀ i, (R.domain i : Set B) ⊆ U (q i)) :
    Refinement U κ where
  parent := q
  domain := R.domain
  covers := R.covers
  subset := hq

/-- Mixed parent triples define a normalized locally constant pair correction. -/
def prism (R : Refinement U κ) (q : κ → ι) (hq : ∀ i, (R.domain i : Set B) ⊆ U (q i))
    (z : TwoCocycle U) : OneCochain R.domain where
  value i j x := z.value (R.parent i) (q i) (q j) x - z.value (R.parent i) (R.parent j) (q j) x
  local_value i j :=
    (local_mono (s := (R.domain i : Set B) ∩ R.domain j)
      (t := ((U (R.parent i) : Set B) ∩ U (q i)) ∩ U (q j))
      (fun _ hx => ⟨⟨R.subset i hx.1, hq i hx.1⟩, hq j hx.2⟩)
      (z.local_value _ _ _)).sub
    (local_mono (s := (R.domain i : Set B) ∩ R.domain j)
      (t := ((U (R.parent i) : Set B) ∩ U (R.parent j)) ∩ U (q j))
      (fun _ hx => ⟨⟨R.subset i hx.1, R.subset j hx.2⟩, hq j hx.2⟩)
      (z.local_value _ _ _))
  identity i x hi := by
    rw [z.self_right _ _ x (R.subset i hi) (hq i hi),
      z.self_left _ _ x (R.subset i hi) (hq i hi), sub_self]

/-- The additive boundary of the mixed-triple correction changes one parent restriction to the other. -/
theorem prism_equation (R : Refinement U κ) (q : κ → ι)
    (hq : ∀ i, (R.domain i : Set B) ⊆ U (q i)) (z : TwoCocycle U)
    (i j k : κ) (x : B) (hi : x ∈ R.domain i) (hj : x ∈ R.domain j) (hk : x ∈ R.domain k) :
    (restrictTwo (reparent R q hq) z).value i j k x =
      boundary (prism R q hq z) i j k x + (restrictTwo R z).value i j k x := by
  have h₁ := z.quadruple (R.parent i) (R.parent j) (R.parent k) (q k) x
    (R.subset i hi) (R.subset j hj) (R.subset k hk) (hq k hk)
  have h₂ := z.quadruple (R.parent i) (R.parent j) (q j) (q k) x
    (R.subset i hi) (R.subset j hj) (hq j hj) (hq k hk)
  have h₃ := z.quadruple (R.parent i) (q i) (q j) (q k) x
    (R.subset i hi) (hq i hi) (hq j hj) (hq k hk)
  change z.value (q i) (q j) (q k) x = _
  simp only [boundary, prism, restrictTwo_value]
  linear_combination (norm := abel) h₁ - h₂ + h₃

/-- Parent choices give equal restricted cohomology classes on the same refined domains. -/
theorem restrictHom_reparent (R : Refinement U κ) (q : κ → ι)
    (hq : ∀ i, (R.domain i : Set B) ⊆ U (q i)) (c : H2 U) :
    restrictHom R c = restrictHom (reparent R q hq) c := by
  obtain ⟨z, rfl⟩ := classOf_surjective c
  exact (classOf_eq_iff _ _).mpr ⟨prism R q hq z, prism_equation R q hq z⟩

end FoliationQM.ModTwoRestriction
