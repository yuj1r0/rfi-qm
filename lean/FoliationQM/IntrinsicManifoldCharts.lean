module
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

/-!
# Smooth atlases from intrinsic coordinate slices

Source: a reusable differential-geometric bridge for the concrete source
manifolds in v13 `prop:takabayasi`. The topology and charted space are
supplied independently. Each chart must be an actual linear projection
of a specified ambient value map, and its actual inverse ambient values
must be smooth on the entire chart target. These hypotheses prove smooth
compatibility on every overlap, without replacing the topology or
assuming the desired transition regularity.
-/

@[expose] public section
open scoped Manifold
open Set
namespace FoliationQM.IntrinsicManifoldCharts
variable {V W M : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [TopologicalSpace M] [ChartedSpace W M]

/-- An atlas using linear ambient coordinate slices is smooth when its actual ambient inverse charts are smooth on their targets. -/
theorem isManifold_of_coordinate_slices (n : WithTop ℕ∞) (value : M → V)
    (hcoords : ∀ e ∈ atlas W M, ∃ P : V →L[ℝ] W, ∀ m, e m = P (value m))
    (hinverse : ∀ e ∈ atlas W M, ContDiffOn ℝ n (value ∘ e.symm) e.target) :
    IsManifold 𝓘(ℝ, W) n M := by
  apply isManifold_of_contDiffOn
  intro e e' he he'
  obtain ⟨P, hP⟩ := hcoords e' he'
  have h := P.contDiff.comp_contDiffOn (hinverse e he)
  have heq : (e.symm.trans e' : W → W) = P ∘ (value ∘ e.symm) := by
    funext w
    exact hP (e.symm w)
  simpa only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
    Function.id_comp, Function.comp_id, Set.preimage_id, Set.range_id, Set.inter_univ, heq] using
    h.mono (show (e.symm.trans e').source ⊆ e.target from fun _ hw => hw.1)

end FoliationQM.IntrinsicManifoldCharts
