module

public import Mathlib.Topology.MetricSpace.Completion

/-!
# Completion of equivalent genuine metrics

Source: v13 `lem:uniqueness`, supporting general-cone completion topology.
A bijection satisfying upper and lower Lipschitz bounds induces a uniform
equivalence of the actual uniform completions. Both metric bounds persist,
and original points and newly added points correspond exactly. No completed
space is identified by definition with another space or assumed to have a
particular number of new points.

This module is generic. A cone application must supply its genuine metrics,
the bijection, and the quantitative bounds separately. Uniform equivalence
alone asserts neither isometry nor smoothness of a cone tip.
-/
@[expose] public section

noncomputable section

namespace FoliationQM.EquivalentMetricCompletion

open UniformSpace Set
open scoped NNReal

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
variable (e : X ≃ Y) {K L : ℝ≥0}
variable (hLip : LipschitzWith K e) (hAnti : AntilipschitzWith L e)

/-- A genuine bijection with the two metric bounds is a uniform equivalence. -/
def uniformEquiv : X ≃ᵤ Y :=
  { e with
    uniformContinuous_toFun := hLip.uniformContinuous
    uniformContinuous_invFun :=
      (hAnti.to_rightInverse e.apply_symm_apply).uniformContinuous }

/-- The uniform equivalence acts on the genuine completions by the actual
uniform-continuity extension of the supplied bijection. -/
def completionEquiv : Completion X ≃ᵤ Completion Y :=
  Completion.mapEquiv (uniformEquiv e hLip hAnti)

/-- In particular, the two actual completed metric spaces are homeomorphic. -/
def completionHomeomorph : Completion X ≃ₜ Completion Y :=
  (completionEquiv e hLip hAnti).toHomeomorph

/-- The completed equivalence agrees with the supplied original bijection. -/
theorem completionEquiv_coe (x : X) :
    completionEquiv e hLip hAnti (x : Completion X) = (e x : Completion Y) :=
  Completion.mapEquiv_coe (uniformEquiv e hLip hAnti) x

/-- The inverse completed equivalence agrees with the original inverse. -/
theorem completionEquiv_symm_coe (y : Y) :
    (completionEquiv e hLip hAnti).symm (y : Completion Y) =
      (e.symm y : Completion X) :=
  Completion.mapEquiv_coe (uniformEquiv e hLip hAnti).symm y

/-- The original upper Lipschitz constant is preserved by completion. -/
theorem completionEquiv_lipschitz :
    LipschitzWith K (completionEquiv e hLip hAnti) :=
  hLip.completion_map

/-- The original lower metric bound gives the same upper Lipschitz
constant for the inverse map between completions. -/
theorem completionEquiv_symm_lipschitz :
    LipschitzWith L (completionEquiv e hLip hAnti).symm :=
  (hAnti.to_rightInverse e.apply_symm_apply).completion_map

/-- The lower Lipschitz bound also persists on the actual completion. -/
theorem completionEquiv_antilipschitz :
    AntilipschitzWith L (completionEquiv e hLip hAnti) := by
  apply AntilipschitzWith.of_le_mul_dist
  intro x y
  simpa only [UniformEquiv.symm_apply_apply] using
    (completionEquiv_symm_lipschitz e hLip hAnti).dist_le_mul
      (completionEquiv e hLip hAnti x) (completionEquiv e hLip hAnti y)

/-- Agreement on the original dense space uniquely determines any
continuous extension to the completion. -/
theorem completionEquiv_unique {f : Completion X → Completion Y}
    (hf : Continuous f) (h : ∀ x : X, f (x : Completion X) = (e x : Completion Y)) :
    f = completionEquiv e hLip hAnti := by
  apply Completion.ext hf (completionEquiv e hLip hAnti).uniformContinuous.continuous
  intro x
  exact (h x).trans (completionEquiv_coe e hLip hAnti x).symm

/-- A completed point is original exactly when its image is original. -/
theorem mem_range_coe_iff (x : Completion X) :
    completionEquiv e hLip hAnti x ∈ Set.range (fun y : Y => (y : Completion Y)) ↔
      x ∈ Set.range (fun y : X => (y : Completion X)) := by
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨e.symm y, ?_⟩
    apply (completionEquiv e hLip hAnti).injective
    rw [completionEquiv_coe, e.apply_symm_apply]
    exact hy
  · rintro ⟨y, rfl⟩
    exact ⟨e y, (completionEquiv_coe e hLip hAnti y).symm⟩

/-- The newly added points correspond by a genuine uniform equivalence
between the two complements of the original completion embeddings. -/
def remainderEquiv :
    {x : Completion X // x ∉ Set.range (fun y : X => (y : Completion X))} ≃ᵤ
      {x : Completion Y // x ∉ Set.range (fun y : Y => (y : Completion Y))} :=
  (completionEquiv e hLip hAnti).subtype
    (fun x => (not_congr (mem_range_coe_iff e hLip hAnti x)).symm)

/-- If one genuine completion adds exactly one point, so does the other;
its tip is the inverse image under the constructed completed equivalence. -/
theorem compl_range_coe_eq_singleton (tip : Completion Y)
    (htip : (Set.range (fun y : Y => (y : Completion Y)))ᶜ = {tip}) :
    (Set.range (fun x : X => (x : Completion X)))ᶜ =
      {(completionEquiv e hLip hAnti).symm tip} := by
  ext x
  have hx : x ∉ Set.range (fun y : X => (y : Completion X)) ↔
      completionEquiv e hLip hAnti x = tip := by
    rw [← mem_range_coe_iff e hLip hAnti x]
    change completionEquiv e hLip hAnti x ∈
      (Set.range (fun y : Y => (y : Completion Y)))ᶜ ↔ _
    rw [htip, Set.mem_singleton_iff]
  change x ∉ Set.range (fun y : X => (y : Completion X)) ↔
    x = (completionEquiv e hLip hAnti).symm tip
  rw [hx]
  exact (completionEquiv e hLip hAnti).toEquiv.eq_symm_apply.symm

end FoliationQM.EquivalentMetricCompletion
