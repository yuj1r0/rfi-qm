module
public import FoliationQM.SpinSignHOne
public import FoliationQM.SignRefinementPrism

/-!
# Restriction of smooth degree-one Clifford sign classes

For the geometric Spin-frame component of v13 `prop:takabayasi`,
refining the opens restricts the chart gauges and the signs between
charts. On unchanged refined opens, two different parent assignments
differ by the explicit sign of the transition between those parents.
-/

@[expose] public section
noncomputable section
open Set
open scoped IsMulCommutative
namespace FoliationQM.SpinHOneRestriction
open CliffordSpinCoverRefinement SpinSignOneCocycle SpinSignHOne
open SignRefinementPrism SpinRefinementComposition

variable {E H B ι κ τ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace B] [ChartedSpace H B] {U : ι → TopologicalSpace.Opens B}
  {n : WithTop ℕ∞}

/-- Restrict the smooth sign of a containing parent chart to its refined open. -/
def restrictZero (R : Refinement U κ) (a : ZeroCochain I U n) : ZeroCochain I R.domain n where
  value i := a.value (R.parent i)
  smooth_value i := (a.smooth_value (R.parent i)).mono (R.subset i)

/-- The restricted sign cocycle obeys ordered composition on each refined triple overlap. -/
def restrictCocycle (R : Refinement U κ) (z : Cocycle I U n) : Cocycle I R.domain n :=
  ⟨SignClassRestriction.restrictOne R z.val, fun i j k x hi hj hk =>
    z.property (R.parent i) (R.parent j) (R.parent k) x (R.subset i hi) (R.subset j hj) (R.subset k hk)⟩

/-- The sign attached to a refined transition is the literal sign for the assigned parent pair. -/
theorem restrictCocycle_value (R : Refinement U κ) (z : Cocycle I U n) (i j : κ) (x : B) :
    (restrictCocycle R z).val.value i j x = z.val.value (R.parent i) (R.parent j) x := rfl

/-- Taking a chartwise coboundary commutes with restriction of the entire sign cocycle. -/
theorem restrictCocycle_coboundary (R : Refinement U κ) (a : ZeroCochain I U n) :
    restrictCocycle R (coboundary a) = coboundary (restrictZero R a) := rfl

/-- A chart gauge relating two cocycles on the original cover restricts to one relating the refined cocycles. -/
theorem restrict_gaugeRelated (R : Refinement U κ) {z w : Cocycle I U n} (h : GaugeRelated z w) :
    GaugeRelated (restrictCocycle R z) (restrictCocycle R w) := by
  obtain ⟨a, ha⟩ := h
  exact ⟨restrictZero R a, fun i j x hi hj => ha (R.parent i) (R.parent j) x (R.subset i hi) (R.subset j hj)⟩

/-- Restriction along an open refinement induces a homomorphism of the two sign cohomology groups. -/
def restrictHom (R : Refinement U κ) : H1 I U n →* H1 I R.domain n where
  toFun c := Con.liftOn c (fun z => classOf (restrictCocycle R z))
    (fun _ _ h => (classOf_eq_iff _ _).mpr (restrict_gaugeRelated R h))
  map_one' := rfl
  map_mul' c d := by
    obtain ⟨z, rfl⟩ := classOf_surjective c
    obtain ⟨w, rfl⟩ := classOf_surjective d
    rfl

/-- The restricted cohomology class is represented by the parent-indexed restriction of any representative. -/
theorem restrictHom_classOf (R : Refinement U κ) (z : Cocycle I U n) :
    restrictHom R (classOf z) = classOf (restrictCocycle R z) := rfl

/-- The identity refinement acts by the identity on fixed-cover degree-one sign classes. -/
theorem restrictHom_identity (hU : ∀ x : B, ∃ i, x ∈ U i) (c : H1 I U n) :
    restrictHom (identity U hU) c = c := by
  obtain ⟨z, rfl⟩ := classOf_surjective c
  rfl

/-- Restriction through an intermediate open cover equals restriction along the composite refinement. -/
theorem restrictHom_compose (R : Refinement U κ) (T : Refinement R.domain τ) (c : H1 I U n) :
    restrictHom T (restrictHom R c) = restrictHom (compose R T) c := by
  obtain ⟨z, rfl⟩ := classOf_surjective c
  rfl

/-- A second parent assignment gives a smooth chart gauge by taking the sign from the old parent to the new one. -/
def parentGauge (R : Refinement U κ) (q : κ → ι) (hq : ∀ i, (R.domain i : Set B) ⊆ U (q i))
    (z : Cocycle I U n) : ZeroCochain I R.domain n where
  value i := z.val.value (R.parent i) (q i)
  smooth_value i := (z.val.smooth_value (R.parent i) (q i)).mono (fun _ hx => ⟨R.subset i hx, hq i hx⟩)

/-- Two mixed triple-overlap laws give the coboundary relating the old and new parent signs on the refined pair. -/
theorem parentGauge_equation (R : Refinement U κ) (q : κ → ι) (hq : ∀ i, (R.domain i : Set B) ⊆ U (q i))
    (z : Cocycle I U n) (i j : κ) (x : B) (hi : x ∈ R.domain i) (hj : x ∈ R.domain j) :
    (restrictCocycle (reparent R q hq) z).val.value i j x =
      (coboundary (parentGauge R q hq z)).val.value i j x * (restrictCocycle R z).val.value i j x := by
  have h₁ := z.property (R.parent i) (q i) (q j) x (R.subset i hi) (hq i hi) (hq j hj)
  have h₂ := z.property (R.parent i) (R.parent j) (q j) x (R.subset i hi) (R.subset j hj) (hq j hj)
  change z.val.value (q i) (q j) x = z.val.value (R.parent j) (q j) x *
    (z.val.value (R.parent i) (q i) x)⁻¹ * z.val.value (R.parent i) (R.parent j) x
  calc
    _ = (z.val.value (q i) (q j) x * z.val.value (R.parent i) (q i) x) *
        (z.val.value (R.parent i) (q i) x)⁻¹ := (mul_inv_cancel_right _ _).symm
    _ = _ := by rw [h₁, ← h₂]; ac_rfl

/-- Changing each refined chart's containing parent preserves its degree-one cohomology class. -/
theorem restrictHom_reparent (R : Refinement U κ) (q : κ → ι) (hq : ∀ i, (R.domain i : Set B) ⊆ U (q i))
    (c : H1 I U n) : restrictHom R c = restrictHom (reparent R q hq) c := by
  obtain ⟨z, rfl⟩ := classOf_surjective c
  exact (classOf_eq_iff _ _).mpr ⟨parentGauge R q hq z, parentGauge_equation R q hq z⟩

end FoliationQM.SpinHOneRestriction
