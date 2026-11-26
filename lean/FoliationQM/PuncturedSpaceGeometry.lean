module
public import Mathlib.GroupTheory.CosetCover
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.Analysis.Convex.Contractible
public import Mathlib.Analysis.Normed.Module.Basic

/-!
# Finite polygon cones avoiding the origin

Source scope: the simple-connectivity foundation for the actual Spin
universal covering in v13 Section 7 and `prop:takabayasi`. In real dimension
at least three, finitely many two-generator subspaces do not cover the
ambient space. An actual point outside those subspaces cones a finite
polygon to a star-convex set which still avoids the origin. Vertices are
included separately, so the zero-edge polygon is covered as well.

These are geometric existence and containment results. No topological
simple-connectivity conclusion or loop contraction is assumed here.
-/

@[expose] public section
noncomputable section
open Set
namespace FoliationQM.PuncturedSpaceGeometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Any two-vector span is a proper subspace in real dimension at least three. -/
theorem pair_span_ne_top [FiniteDimensional ℝ E] (hdim : 3 ≤ Module.finrank ℝ E) (u v : E) :
    Submodule.span ℝ ({u, v} : Set E) ≠ ⊤ := by
  apply ne_of_lt (span_lt_top_of_ncard_lt_finrank ((finite_singleton v).insert u) ?_)
  have hcard : ({u, v} : Set E).ncard ≤ 2 := by
    by_cases h : u = v
    · simp [h]
    · exact (Set.ncard_pair h).le
  omega

/-- A finite family of two-vector spans admits an actual common avoiding point in real dimension at least three. -/
theorem exists_avoiding_pair_spans [FiniteDimensional ℝ E] {ι : Type*} [Finite ι]
    (hdim : 3 ≤ Module.finrank ℝ E) (u v : ι → E) :
    ∃ a : E, ∀ i, a ∉ Submodule.span ℝ ({u i, v i} : Set E) := by
  classical
  by_contra h
  push Not at h
  have hc : (⋃ i, (Submodule.span ℝ ({u i, v i} : Set E) : Set E)) = univ := by
    ext a
    simp only [mem_iUnion, mem_univ, iff_true]
    exact h a
  obtain ⟨i, hi⟩ := Subspace.exists_eq_top_of_iUnion_eq_univ hc
  exact pair_span_ne_top hdim (u i) (v i) hi

/-- Every point of a literal segment lies in the real span of its endpoints. -/
theorem segment_subset_pair_span (u v : E) :
    segment ℝ u v ⊆ Submodule.span ℝ ({u, v} : Set E) := by
  apply (Submodule.span ℝ ({u, v} : Set E)).convex.segment_subset
  · exact Submodule.subset_span (by simp)
  · exact Submodule.subset_span (by simp)

/-- Coning a nonzero vector in a subspace to a point outside that subspace cannot pass through the origin. -/
theorem zero_not_mem_segment_of_not_mem_submodule {P : Submodule ℝ E} {a y : E}
    (ha : a ∉ P) (hy : y ∈ P) (hy0 : y ≠ 0) : (0 : E) ∉ segment ℝ a y := by
  rintro ⟨s, t, hs, ht, hst, he⟩
  by_cases hs0 : s = 0
  · have ht1 : t = 1 := by simpa [hs0] using hst
    exact hy0 (by simpa [hs0, ht1] using he)
  · apply ha
    have hsy : s • a = -(t • y) := eq_neg_of_add_eq_zero_left he
    have hm : s • a ∈ P := hsy.symm ▸ P.neg_mem (P.smul_mem t hy)
    have hh := P.smul_mem s⁻¹ hm
    simpa [smul_smul, hs0] using hh

/-- The literal cone consists of all line segments from a fixed point to points of the given set. -/
def cone (a : E) (S : Set E) : Set E := ⋃ y ∈ S, segment ℝ a y

/-- A literal cone contains every point of the set being coned. -/
theorem subset_cone (a : E) (S : Set E) : S ⊆ cone a S := by
  intro y hy
  exact mem_iUnion.mpr ⟨y, mem_iUnion.mpr ⟨hy, right_mem_segment ℝ a y⟩⟩

/-- A nonempty literal cone contains its stated apex. -/
theorem apex_mem_cone (a : E) {S : Set E} (hS : S.Nonempty) : a ∈ cone a S := by
  obtain ⟨y, hy⟩ := hS
  exact mem_iUnion.mpr ⟨y, mem_iUnion.mpr ⟨hy, left_mem_segment ℝ a y⟩⟩

/-- The literal cone is star-convex at its actual apex, independently of the set being coned. -/
theorem starConvex_cone (a : E) (S : Set E) : StarConvex ℝ a (cone a S) := by
  apply starConvex_iUnion₂
  intro y _
  exact (convex_segment a y).starConvex (left_mem_segment ℝ a y)

/-- If every nonzero point of a set lies in a subspace avoided by an apex, its entire literal cone also avoids the origin. -/
theorem cone_subset_punctured {ι : Type*} (P : ι → Submodule ℝ E)
    {a : E} {S : Set E} (ha : ∀ i, a ∉ P i)
    (hS : ∀ y ∈ S, ∃ i, y ∈ P i) (hzero : (0 : E) ∉ S) :
    cone a S ⊆ {x : E | x ≠ 0} := by
  intro x hx hx0
  rcases mem_iUnion.mp hx with ⟨y, hy⟩
  rcases mem_iUnion.mp hy with ⟨hyS, hxy⟩
  obtain ⟨i, hyP⟩ := hS y hyS
  have hy0 : y ≠ 0 := fun h => hzero (h ▸ hyS)
  exact zero_not_mem_segment_of_not_mem_submodule (ha i) hyP hy0 (hx0 ▸ hxy)

/-- Every finite polygon whose vertices and edges avoid zero lies in an actual star-convex set avoiding zero, in real dimension at least three. -/
theorem exists_starConvex_polygon_container [FiniteDimensional ℝ E] {n : ℕ}
    (hdim : 3 ≤ Module.finrank ℝ E) (v : Fin (n + 1) → E)
    (hzero : ∀ i, v i ≠ 0)
    (hedge : ∀ i : Fin n, (0 : E) ∉ segment ℝ (v i.castSucc) (v i.succ)) :
    ∃ a : E, ∃ K : Set E, StarConvex ℝ a K ∧ a ∈ K ∧ K ⊆ {x : E | x ≠ 0} ∧
      (∀ i, v i ∈ K) ∧ (∀ i : Fin n, segment ℝ (v i.castSucc) (v i.succ) ⊆ K) := by
  classical
  let u : Fin (n + 1) ⊕ Fin n → E := Sum.elim v (fun i => v i.castSucc)
  let w : Fin (n + 1) ⊕ Fin n → E := Sum.elim v (fun i => v i.succ)
  let P (i : Fin (n + 1) ⊕ Fin n) : Submodule ℝ E := Submodule.span ℝ {u i, w i}
  obtain ⟨a, ha⟩ := exists_avoiding_pair_spans hdim u w
  let S : Set E := range v ∪ ⋃ i : Fin n, segment ℝ (v i.castSucc) (v i.succ)
  have hv (i : Fin (n + 1)) : v i ∈ S := Or.inl ⟨i, rfl⟩
  have he (i : Fin n) : segment ℝ (v i.castSucc) (v i.succ) ⊆ S := by
    intro y hy
    exact Or.inr (mem_iUnion.mpr ⟨i, hy⟩)
  have hSP : ∀ y ∈ S, ∃ i, y ∈ P i := by
    rintro y (⟨i, rfl⟩ | hy)
    · refine ⟨Sum.inl i, Submodule.subset_span ?_⟩
      simp [u]
    · obtain ⟨i, hi⟩ := mem_iUnion.mp hy
      exact ⟨Sum.inr i, segment_subset_pair_span _ _ hi⟩
  have hSzero : (0 : E) ∉ S := by
    rintro (⟨i, hi⟩ | hi)
    · exact hzero i hi
    · obtain ⟨i, hi⟩ := mem_iUnion.mp hi
      exact hedge i hi
  refine ⟨a, cone a S, starConvex_cone a S, apex_mem_cone a ⟨v 0, hv 0⟩,
    cone_subset_punctured P ha hSP hSzero, ?_, ?_⟩
  · intro i
    exact subset_cone a S (hv i)
  · intro i
    exact (he i).trans (subset_cone a S)

end FoliationQM.PuncturedSpaceGeometry
