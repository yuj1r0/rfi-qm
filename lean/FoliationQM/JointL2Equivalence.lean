module

public import FoliationQM.JointL2Product
public import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp

/-!
# The joint and iterated spatial Hilbert spaces are unitarily equivalent

Every square-integrable family of remote waves represents a joint scalar
wave. Outer indicators with Hilbert-valued coefficients lift to simple
tensors, and the isometric range of the complete joint space is closed.
The same approximation shows that products span a dense subspace of the
joint Hilbert space in v13 `thm:entanglement_nosignaling`.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.JointL2Equivalence

open MeasureTheory LorentzCoordinates JointL2Sections JointL2Curry JointL2Product
open scoped ENNReal

/-- The outer wave equal to a fixed remote vector on a finite-measure set and
zero elsewhere comes from a product with the scalar indicator of that set. -/
theorem curry_indicator_product {s : Set Spatial} (hs : MeasurableSet s) (hμ : volume s ≠ ∞)
    (v : Remote) :
    curry (product (indicatorConstLp 2 hs hμ (1 : ℂ)) v) = indicatorConstLp 2 hs hμ v := by
  apply Lp.ext
  filter_upwards [curry_product (indicatorConstLp 2 hs hμ (1 : ℂ)) v,
    (indicatorConstLp_coeFn (p := 2) (hs := hs) (hμs := hμ) (c := (1 : ℂ))),
    (indicatorConstLp_coeFn (p := 2) (hs := hs) (hμs := hμ) (c := v))] with x hp hscalar hv
  rw [hp, hscalar, hv]
  by_cases hx : x ∈ s <;> simp [hx]

/-- Finite complex linear combinations of curried product waves are dense in the outer space. -/
theorem dense_outer_products : Dense (Submodule.span ℂ (Set.range
    (fun p : Remote × Remote => curry (product p.1 p.2))) : Set Outer) := by
  let P := Submodule.span ℂ (Set.range (fun p : Remote × Remote => curry (product p.1 p.2)))
  change ∀ f : Outer, f ∈ P.topologicalClosure
  apply Lp.induction ENNReal.ofNat_ne_top (fun f : Outer => f ∈ P.topologicalClosure)
  · intro v s hs hμ
    rw [Lp.simpleFunc.coe_indicatorConst, ← curry_indicator_product hs hμ.ne]
    exact P.le_topologicalClosure (Submodule.subset_span ⟨(_,v), rfl⟩)
  · intro _ _ _ _ _ hf hg
    exact P.topologicalClosure.add_mem hf hg
  · exact P.isClosed_topologicalClosure

/-- Currying from joint scalar waves onto remote-Hilbert-valued waves is surjective. -/
theorem curry_surjective : Function.Surjective curry := by
  let r := curry.toLinearMap.range
  have hle : Submodule.span ℂ (Set.range (fun p : Remote × Remote => curry (product p.1 p.2))) ≤ r :=
    Submodule.span_le.mpr (by rintro _ ⟨p, rfl⟩; exact ⟨product p.1 p.2, rfl⟩)
  have hclosed : IsClosed (Set.range curry) := curry.isometry.isClosedEmbedding.isClosed_range
  intro f
  change f ∈ Set.range curry
  rw [← hclosed.closure_eq]
  exact (dense_outer_products.mono hle) f

/-- The complex linear isometric equivalence between the joint and iterated spatial `L²` spaces. -/
def equiv : Joint ≃ₗᵢ[ℂ] Outer := LinearIsometryEquiv.ofSurjective curry curry_surjective

/-- The forward equivalence is the map sending a joint wave to its remote sections. -/
theorem equiv_apply (ψ : Joint) : equiv ψ = curry ψ := rfl

/-- The joint wave associated to an outer class recovers its scalar sections
for almost every retained position and almost every remote position. -/
theorem coe_inverse (F : Outer) :
    ∀ᵐ x ∂volume, (fun y => equiv.symm F (x,y)) =ᵐ[volume] (F x : Spatial → ℂ) := by
  have he : curry (equiv.symm F) = F := equiv.apply_symm_apply F
  simpa only [he] using (coe_curry_joint (equiv.symm F)).mono (fun _ h => h.symm)

/-- Finite complex linear combinations of product waves are dense in the joint scalar space. -/
theorem dense_products : Dense (Submodule.span ℂ
    (Set.range (fun p : Remote × Remote => product p.1 p.2)) : Set Joint) := by
  let P := Submodule.span ℂ (Set.range (fun p : Remote × Remote => product p.1 p.2))
  have hm : Submodule.span ℂ (Set.range (fun p : Remote × Remote => curry (product p.1 p.2))) ≤
      P.comap equiv.symm.toLinearEquiv.toLinearMap := by
    apply Submodule.span_le.mpr
    rintro _ ⟨p, rfl⟩
    change equiv.symm (equiv (product p.1 p.2)) ∈ P
    rw [equiv.symm_apply_apply]
    exact Submodule.subset_span ⟨p, rfl⟩
  exact equiv.symm.surjective.denseRange.dense_of_mapsTo equiv.symm.continuous
    dense_outer_products (fun _ hx => hm hx)

/-- Continuous complex linear operators on joint waves that agree on all
product waves agree on every state, including entangled states. -/
theorem ext_on_products {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    {A B : Joint →L[ℂ] H} (he : ∀ u v, A (product u v) = B (product u v)) : A = B :=
  ContinuousLinearMap.ext_on dense_products (by rintro _ ⟨p, rfl⟩; exact he p.1 p.2)

end FoliationQM.JointL2Equivalence
