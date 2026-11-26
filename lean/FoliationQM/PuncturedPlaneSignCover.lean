module
public import FoliationQM.SpinSignOneCocycle
public import Mathlib.Analysis.Convex.PathConnected

/-!
# A three-chart cover of the punctured real plane

Source scope: the degree-one Spin lifting component of v13 `prop:takabayasi`.
The strict inequalities x > 0, y > 0 and x + y < 0 cover the complement
of the origin. Each domain is a convex half-plane in the ambient plane.
The three pair overlaps contain explicit points, while the three distinct
charts have empty common intersection.
-/

@[expose] public section
noncomputable section
open Set Topology
open scoped Manifold
namespace FoliationQM.PuncturedPlaneSignCover

/-- The underlying real normed plane. -/
abbrev Ambient := ℝ × ℝ

/-- The open complement of the origin in the real normed plane. -/
def punctured : TopologicalSpace.Opens Ambient := ⟨{(0 : Ambient)}ᶜ, isOpen_compl_singleton⟩

/-- The punctured plane with its inherited open-subspace charts and topology. -/
abbrev Plane := ↥punctured

/-- The real plane model for the inherited charts of its open subset. -/
abbrev model := 𝓘(ℝ, Ambient)

/-- The three linear tests are x, y and minus their sum. -/
def test (i : Fin 3) : Ambient →L[ℝ] ℝ :=
  if i = 0 then ContinuousLinearMap.fst ℝ ℝ ℝ
  else if i = 1 then ContinuousLinearMap.snd ℝ ℝ ℝ
  else -(ContinuousLinearMap.fst ℝ ℝ ℝ + ContinuousLinearMap.snd ℝ ℝ ℝ)

/-- Each cover member consists of the points passing its strict linear test. -/
def domains (i : Fin 3) : TopologicalSpace.Opens Plane :=
  ⟨{p | 0 < test i p.val}, isOpen_lt continuous_const ((test i).continuous.comp continuous_subtype_val)⟩

/-- At least one of the three strict inequalities holds at every nonzero point. -/
theorem covers (p : Plane) : ∃ i : Fin 3, p ∈ domains i := by
  by_contra! h
  have hx : ¬ 0 < p.val.1 := by simpa [domains, test] using h 0
  have hy : ¬ 0 < p.val.2 := by simpa [domains, test] using h 1
  have hs : ¬ 0 < -(p.val.1 + p.val.2) := by simpa [domains, test] using h 2
  apply p.property
  change p.val = (0 : Ambient)
  exact Prod.ext (by change p.val.1 = 0; linarith) (by change p.val.2 = 0; linarith)

/-- Every actual chart domain is preconnected because its image is the entire convex open half-plane. -/
theorem domains_isPreconnected (i : Fin 3) : IsPreconnected (domains i : Set Plane) := by
  apply Topology.IsInducing.subtypeVal.isPreconnected_image.mp
  change IsPreconnected (Subtype.val '' ((Subtype.val : Plane → Ambient) ⁻¹' {p | 0 < test i p}))
  have sub : {p : Ambient | 0 < test i p} ⊆ range (Subtype.val : Plane → Ambient) := by
    intro p hp
    have ne : p ≠ 0 := by
      intro h0
      change 0 < test i p at hp
      simp [h0] at hp
    exact ⟨⟨p, ne⟩, rfl⟩
  rw [image_preimage_eq_of_subset sub]
  exact (convex_halfSpace_gt (test i).toLinearMap.isLinear 0).isPreconnected

/-- The point (1,1) belongs to the first and second opens. -/
theorem pair01 : ∃ p : Plane, p ∈ domains 0 ∧ p ∈ domains 1 := by
  let p : Plane := ⟨(1,1), by change (1,1) ≠ (0 : Ambient); norm_num⟩
  exact ⟨p, by norm_num [p, domains, test], by norm_num [p, domains, test]⟩

/-- The point (-2,1) belongs to the second and third opens. -/
theorem pair12 : ∃ p : Plane, p ∈ domains 1 ∧ p ∈ domains 2 := by
  let p : Plane := ⟨(-2,1), by change (-2,1) ≠ (0 : Ambient); norm_num⟩
  exact ⟨p, by norm_num [p, domains, test], by norm_num [p, domains, test]⟩

/-- The point (1,-2) belongs to the first and third opens. -/
theorem pair02 : ∃ p : Plane, p ∈ domains 0 ∧ p ∈ domains 2 := by
  let p : Plane := ⟨(1,-2), by change (1,-2) ≠ (0 : Ambient); norm_num⟩
  exact ⟨p, by norm_num [p, domains, test], by norm_num [p, domains, test]⟩

/-- No point of the punctured plane belongs to all three distinct charts. -/
theorem no_triple (p : Plane) (h0 : p ∈ domains 0) (h1 : p ∈ domains 1) (h2 : p ∈ domains 2) :
    False := by
  have hx : 0 < p.val.1 := by simpa [domains, test] using h0
  have hy : 0 < p.val.2 := by simpa [domains, test] using h1
  have hs : 0 < -(p.val.1+p.val.2) := by simpa [domains, test] using h2
  linarith

end FoliationQM.PuncturedPlaneSignCover
