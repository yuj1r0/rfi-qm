module
public import FoliationQM.SignClassRestriction
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.LinearCombination

/-!
# Changing the parent assignment of a sign-class restriction

Source scope: a global Spin-frame component of v13 `prop:takabayasi`.
Two parent assignments can place the same refined opens in different
original charts. The two mixed triples over each refined pair define a
normalized smooth correction. Three instances of the original quadruple
law show that its boundary changes the first restricted representative
into the second on every refined triple overlap.
-/

@[expose] public section
noncomputable section
open Set
open scoped Manifold IsMulCommutative
namespace FoliationQM.SignRefinementPrism
open CliffordSpinCoverRefinement SpinSignCohomology SignClassRestriction

variable {B ι κ : Type*} [TopologicalSpace B] {U : ι → TopologicalSpace.Opens B}

/-- Choose a second containing chart for each of the same refined open domains. -/
def reparent (R : Refinement U κ) (q : κ → ι)
    (hq : ∀ a, (R.domain a : Set B) ⊆ U (q a)) : Refinement U κ where
  parent := q
  domain := R.domain
  covers := R.covers
  subset := hq

/-- The reparented refinement has exactly the original family of refined opens. -/
theorem reparent_domain (R : Refinement U κ) (q : κ → ι)
    (hq : ∀ a, (R.domain a : Set B) ⊆ U (q a)) : (reparent R q hq).domain = R.domain := rfl

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [ChartedSpace H B] {n : WithTop ℕ∞}

/-- The ratio of the two mixed parent triples forms a smooth normalized pair coefficient on the refined opens. -/
def prism (R : Refinement U κ) (q : κ → ι) (hq : ∀ a, (R.domain a : Set B) ⊆ U (q a))
    (z : TwoCocycle I U n) : OneCochain I R.domain n where
  value a b x := z.value (R.parent a) (q a) (q b) x * (z.value (R.parent a) (R.parent b) (q b) x)⁻¹
  smooth_value a b := (CliffordSpinManifold.contMDiff_mul n).comp_contMDiffOn
    (((z.smooth_value (R.parent a) (q a) (q b)).mono
      (fun _ h => ⟨⟨R.subset a h.1, hq a h.1⟩, hq b h.2⟩)).prodMk
      ((CliffordSpinManifold.contMDiff_inv n).comp_contMDiffOn
        ((z.smooth_value (R.parent a) (R.parent b) (q b)).mono
          (fun _ h => ⟨⟨R.subset a h.1, R.subset b h.2⟩, hq b h.2⟩))))
  identity a x hx := by
    rw [z.self_right (R.parent a) (q a) x (R.subset a hx) (hq a hx),
      z.self_left (R.parent a) (q a) x (R.subset a hx) (hq a hx), inv_one, one_mul]

/-- The explicit prism coefficient is the ordered ratio of the original cocycle's two mixed triple values. -/
theorem prism_value (R : Refinement U κ) (q : κ → ι) (hq : ∀ a, (R.domain a : Set B) ⊆ U (q a))
    (z : TwoCocycle I U n) (a b : κ) (x : B) :
    (prism R q hq z).value a b x =
      z.value (R.parent a) (q a) (q b) x * (z.value (R.parent a) (R.parent b) (q b) x)⁻¹ := rfl

/-- On a true refined triple overlap, the boundary of the explicit prism changes the original parent defect to the new parent defect. -/
theorem prism_equation (R : Refinement U κ) (q : κ → ι)
    (hq : ∀ a, (R.domain a : Set B) ⊆ U (q a)) (z : TwoCocycle I U n) (a b c : κ)
    (x : B) (ha : x ∈ R.domain a) (hb : x ∈ R.domain b) (hc : x ∈ R.domain c) :
    (restrictTwo (reparent R q hq) z).value a b c x =
      boundary (prism R q hq z) a b c x * (restrictTwo R z).value a b c x := by
  have first := congrArg Additive.ofMul (z.quadruple (R.parent a) (R.parent b) (R.parent c) (q c) x
    (R.subset a ha) (R.subset b hb) (R.subset c hc) (hq c hc))
  have second := congrArg Additive.ofMul (z.quadruple (R.parent a) (R.parent b) (q b) (q c) x
    (R.subset a ha) (R.subset b hb) (hq b hb) (hq c hc))
  have third := congrArg Additive.ofMul (z.quadruple (R.parent a) (q a) (q b) (q c) x
    (R.subset a ha) (hq a ha) (hq b hb) (hq c hc))
  apply Additive.ofMul.injective
  simp only [restrictTwo_value, reparent, boundary, prism_value, ofMul_mul, ofMul_inv] at *
  linear_combination (norm := abel) first - second + third

/-- Changing the parent assignment on unchanged refined opens gives cohomologous restrictions, witnessed by the explicit smooth prism coefficient. -/
theorem related_reparent (R : Refinement U κ) (q : κ → ι)
    (hq : ∀ a, (R.domain a : Set B) ⊆ U (q a)) (z : TwoCocycle I U n) :
    Related (restrictTwo R z) (restrictTwo (reparent R q hq) z) :=
  ⟨prism R q hq z, prism_equation R q hq z⟩

/-- Every degree-two sign class restricts equally along either containing-chart assignment on the same refined domains. -/
theorem restrictClass_reparent (R : Refinement U κ) (q : κ → ι)
    (hq : ∀ a, (R.domain a : Set B) ⊆ U (q a)) (c : ObstructionClass I U n) :
    restrictClass R c = restrictClass (reparent R q hq) c := by
  induction c using Quotient.inductionOn with
  | h z => exact (classOf_eq_iff _ _).mpr (related_reparent R q hq z)

end FoliationQM.SignRefinementPrism
