module
public import FoliationQM.ModTwoGlobalPullback

/-!
# Degree two on a point and pullback along a constant map

For the geometric frame component of v13 `prop:takabayasi`, a normalized
two-cocycle on a point-indexed cover of a subsingleton base is zero on
each true triple. Factoring a constant map through a point therefore
kills every all-cover class.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.ModTwoConstantPullback
open ModTwoAllCover ModTwoCohomology ModTwoGlobalPullback

variable {B X : Type*} [TopologicalSpace B] [TopologicalSpace X]

/-- Normalization kills every class in degree two on a subsingleton base, including the empty base. -/
theorem eq_zero_of_subsingleton [Subsingleton B] (c : GlobalH2 B) : c = 0 := by
  obtain ⟨P, d, rfl⟩ := exists_representative c
  obtain ⟨z, rfl⟩ := classOf_surjective d
  have hz : classOf z = 0 := by
    apply classOf_eq_of_eqOn (w := 0)
    intro i j k x hi _ hk
    cases Subsingleton.elim i j
    exact z.self_left i k x hi hk
  rw [hz, map_zero]

/-- Pullback along any constant continuous map sends every global degree-two class to zero. -/
theorem pull_const (b : B) (c : GlobalH2 B) : pull (ContinuousMap.const X b) c = 0 := by
  let p : C(X, Unit) := .const X ()
  let q : C(Unit, B) := .const Unit b
  have he : q.comp p = ContinuousMap.const X b := rfl
  rw [← he, ← pull_comp, eq_zero_of_subsingleton (pull q c), map_zero]

end FoliationQM.ModTwoConstantPullback
