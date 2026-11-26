module
public import FoliationQM.SpinSignCohomology
public import FoliationQM.SpinRefinementComposition

/-!
# Restriction of smooth sign classes along open refinements

Source scope: the Spin obstruction component of v13 `prop:takabayasi`
(A/C/D, component only). Restriction takes each refined pair or triple
to its chosen parent indices. The sign coboundary commutes with this
operation, so every smooth change of representative restricts to a
smooth change on the smaller overlaps. This gives a map of obstruction
classes for the specified refinement.
-/

@[expose] public section
noncomputable section
open Set
namespace FoliationQM.SignClassRestriction
open CliffordSpinCoverRefinement SpinSignCohomology

variable {E H B : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace B] [ChartedSpace H B]
  {ι κ τ : Type*} {U : ι → TopologicalSpace.Opens B} {n : WithTop ℕ∞}

/-- Restrict a smooth normalized pair cochain to the genuine refined overlaps by using the chosen parent indices. -/
def restrictOne (R : Refinement U κ) (b : OneCochain I U n) : OneCochain I R.domain n where
  value a c := b.value (R.parent a) (R.parent c)
  smooth_value a c := (b.smooth_value (R.parent a) (R.parent c)).mono (pair_subset R a c)
  identity a x ha := b.identity (R.parent a) x (R.subset a ha)

/-- The representative of a restricted pair cochain is its parent coefficient. -/
theorem restrictOne_value (R : Refinement U κ) (b : OneCochain I U n) (a c : κ) (x : B) :
    (restrictOne R b).value a c x = b.value (R.parent a) (R.parent c) x := rfl

/-- Restrict a smooth normalized sign cocycle, using the inclusions of the refined overlaps for smoothness, normalization and the quadruple law. -/
def restrictTwo (R : Refinement U κ) (z : TwoCocycle I U n) : TwoCocycle I R.domain n where
  value a b c := z.value (R.parent a) (R.parent b) (R.parent c)
  smooth_value a b c := (z.smooth_value (R.parent a) (R.parent b) (R.parent c)).mono
    (fun _ hx => ⟨⟨R.subset a hx.1.1, R.subset b hx.1.2⟩, R.subset c hx.2⟩)
  self_left a c x ha hc := z.self_left (R.parent a) (R.parent c) x (R.subset a ha) (R.subset c hc)
  self_right a c x ha hc := z.self_right (R.parent a) (R.parent c) x (R.subset a ha) (R.subset c hc)
  quadruple a b c d x ha hb hc hd := z.quadruple (R.parent a) (R.parent b) (R.parent c)
    (R.parent d) x (R.subset a ha) (R.subset b hb) (R.subset c hc) (R.subset d hd)

/-- The representative of a restricted sign cocycle is its original parent triple coefficient. -/
theorem restrictTwo_value (R : Refinement U κ) (z : TwoCocycle I U n) (a b c : κ) (x : B) :
    (restrictTwo R z).value a b c x = z.value (R.parent a) (R.parent b) (R.parent c) x := rfl

/-- The ordered pair coboundary computed after restriction equals the original parent coboundary. -/
theorem boundary_restrictOne (R : Refinement U κ) (b : OneCochain I U n) (a c d : κ) (x : B) :
    boundary (restrictOne R b) a c d x = boundary b (R.parent a) (R.parent c) (R.parent d) x := rfl

/-- Restricting the entire normalized boundary cocycle gives the boundary cocycle of the restricted pair cochain. -/
theorem restrictTwo_boundaryCocycle (R : Refinement U κ) (b : OneCochain I U n) :
    restrictTwo R (boundaryCocycle b) = boundaryCocycle (restrictOne R b) := rfl

/-- A coboundary relation on original triples restricts to a coboundary relation on the refined triples, witnessed by the restricted one-cochain. -/
theorem restrict_related (R : Refinement U κ) {z w : TwoCocycle I U n} (h : Related z w) :
    Related (restrictTwo R z) (restrictTwo R w) := by
  obtain ⟨b, hb⟩ := h
  exact ⟨restrictOne R b, fun a c d x ha hc hd =>
    hb (R.parent a) (R.parent c) (R.parent d) x (R.subset a ha) (R.subset c hc) (R.subset d hd)⟩

/-- Two cocycles that agree on every true triple overlap have the same obstruction class, by the normalized unit pair cochain. -/
theorem classOf_eq_of_eqOn {z w : TwoCocycle I U n}
    (h : ∀ i j k x, x ∈ U i → x ∈ U j → x ∈ U k → z.value i j k x = w.value i j k x) :
    classOf z = classOf w := by
  apply (classOf_eq_iff z w).mpr
  refine ⟨unitCochain I U n, fun i j k x hi hj hk => ?_⟩
  rw [boundary_unit, one_mul]
  exact (h i j k x hi hj hk).symm

/-- The quotient map on sign classes induced by restricting representatives and their coboundary witnesses. -/
def restrictClass (R : Refinement U κ) (c : ObstructionClass I U n) : ObstructionClass I R.domain n :=
  Quotient.liftOn c (fun z => classOf (restrictTwo R z))
    (fun z w h => (classOf_eq_iff (restrictTwo R z) (restrictTwo R w)).mpr (restrict_related R h))

/-- Restricting a represented class gives the class of its restricted two-cocycle. -/
theorem restrictClass_classOf (R : Refinement U κ) (z : TwoCocycle I U n) :
    restrictClass R (classOf z) = classOf (restrictTwo R z) := rfl

/-- The neutral fixed-cover sign class restricts to the neutral class of the refined cover. -/
theorem restrictClass_neutral (R : Refinement U κ) :
    restrictClass R (neutralClass I U n) = neutralClass I R.domain n := rfl

/-- Restricting an obstruction class along the identity refinement returns the original class. -/
theorem restrictClass_identity (hU : ∀ x : B, ∃ i, x ∈ U i) (c : ObstructionClass I U n) :
    restrictClass (SpinRefinementComposition.identity U hU) c = c := by
  induction c using Quotient.inductionOn with
  | h z => rfl

/-- Restriction along a composite refinement agrees on obstruction classes with successive restriction through the intermediate cover. -/
theorem restrictClass_compose (R : Refinement U κ) (T : Refinement R.domain τ)
    (c : ObstructionClass I U n) :
    restrictClass T (restrictClass R c) = restrictClass (SpinRefinementComposition.compose R T) c := by
  induction c using Quotient.inductionOn with
  | h z => rfl

end FoliationQM.SignClassRestriction
