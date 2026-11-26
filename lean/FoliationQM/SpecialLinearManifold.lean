module
public import FoliationQM.SpecialLinearCharts
public import FoliationQM.IntrinsicManifoldCharts
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# The intrinsic six-dimensional determinant-one matrix manifold

Sources: the concrete matrix factor of v13 `prop:takabayasi` and
`eq:takabayasi_polar`. The existing natural determinant-one matrix
subtype carries the two actual rational charts of `SpecialLinearCharts`.
A nonzero upper-left entry selects the first chart; otherwise the
nonzero upper-right entry selects the second. No topology is replaced.

The actual atlas transitions are smooth to every order because their
coordinate maps are ambient linear projections and their inverse
matrix formulas are smooth on their explicit nonzero-pivot targets.
The real local model has dimension six. The actual ambient matrix
inclusion is manifold-smooth, and intrinsic smoothness into this
manifold is equivalent to smoothness of the actual matrix-valued map.
This compatibility holds for arbitrary charted source manifolds and
arbitrary within-set domains, and specializes to ordinary real
Frechet calculus on normed source spaces. These are intrinsic manifold
and calculus results for the concrete determinant-one matrix subtype;
no abstract Spin-group classification is assumed or asserted.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Matrix.Norms.Operator Manifold
open Set Topology
namespace FoliationQM.SpecialLinearManifold
open SpinorMatrix SourcePolarDatum SpecialLinearCharts

/-- The existing natural determinant-one matrix subtype has the two actual rational charts, choosing the first whenever its pivot is nonzero. -/
instance instChartedSpaceSpecialLinearMatrix : ChartedSpace Model SpecialLinearMatrix := by
  classical
  exact {
    atlas := {chartA, chartB}
    chartAt := fun A => if A.val 0 0 ≠ 0 then chartA else chartB
    mem_chart_source := by
      intro A
      split_ifs with h
      · exact h
      · exact (pivot_cover A).resolve_left h
    chart_mem_atlas := by
      intro A
      split_ifs <;> simp }

/-- The intrinsic atlas consists exactly of the two rational matrix charts. -/
theorem mem_atlas_iff (e : OpenPartialHomeomorph SpecialLinearMatrix Model) :
    e ∈ atlas Model SpecialLinearMatrix ↔ e = chartA ∨ e = chartB := by
  rfl

/-- A determinant-one matrix with nonzero upper-left entry uses the first intrinsic chart. -/
theorem chartAt_eq_chartA (A : SpecialLinearMatrix) (ha : A.val 0 0 ≠ 0) :
    chartAt Model A = chartA := by
  change (if A.val 0 0 ≠ 0 then chartA else chartB) = chartA
  exact ite_eq_left ha

/-- A determinant-one matrix with zero upper-left entry uses the second intrinsic chart, whose upper-right pivot is necessarily nonzero. -/
theorem chartAt_eq_chartB (A : SpecialLinearMatrix) (ha : A.val 0 0 = 0) :
    chartAt Model A = chartB := by
  change (if A.val 0 0 ≠ 0 then chartA else chartB) = chartB
  exact ite_eq_right (not_ne_iff.mpr ha)

private theorem chart_linear (e : OpenPartialHomeomorph SpecialLinearMatrix Model)
    (he : e ∈ atlas Model SpecialLinearMatrix) :
    ∃ P : Mat2 →L[ℝ] Model, ∀ A, e A = P A.val := by
  rcases (mem_atlas_iff e).mp he with rfl | rfl
  · exact ⟨coordinatesACLM, fun _ => rfl⟩
  · exact ⟨coordinatesBCLM, fun _ => rfl⟩

/-- Every actual inverse chart, viewed as an ambient matrix-valued map, is smooth to every order on its target. -/
theorem contDiffOn_value_symm (n : WithTop ℕ∞)
    (e : OpenPartialHomeomorph SpecialLinearMatrix Model)
    (he : e ∈ atlas Model SpecialLinearMatrix) :
    ContDiffOn ℝ n (Subtype.val ∘ e.symm : Model → Mat2) e.target := by
  rcases (mem_atlas_iff e).mp he with rfl | rfl
  · exact contDiffOn_chartA_symm_val n
  · exact contDiffOn_chartB_symm_val n

/-- The actual rational atlas on the natural determinant-one matrix subtype is a real manifold to every differentiability order. -/
instance instIsManifoldSpecialLinearMatrix (n : WithTop ℕ∞) :
    IsManifold 𝓘(ℝ, Model) n SpecialLinearMatrix :=
  IntrinsicManifoldCharts.isManifold_of_coordinate_slices n Subtype.val
    chart_linear (contDiffOn_value_symm n)

/-- The intrinsic three-complex-coordinate model has real dimension six. -/
theorem model_finrank : Module.finrank ℝ Model = 6 := by
  simp [Model, Module.finrank_pi_fintype, Complex.finrank_real_complex]

/-- The actual inclusion of determinant-one matrices into the ambient complex matrix space is manifold-smooth to every order. -/
theorem contMDiff_value (n : WithTop ℕ∞) :
    ContMDiff 𝓘(ℝ, Model) 𝓘(ℝ, Mat2) n
      (Subtype.val : SpecialLinearMatrix → Mat2) := by
  apply contMDiff_iff.mpr
  refine ⟨continuous_subtype_val, ?_⟩
  intro A B
  simpa only [mfld_simps] using
    contDiffOn_value_symm n (chartAt Model A) (chart_mem_atlas Model A)

section GeneralSource
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M]
  {n : WithTop ℕ∞} {f : M → SpecialLinearMatrix} {s : Set M} {x : M}

/-- For an arbitrary charted source and any source set, intrinsic smoothness into determinant-one matrices is equivalent to manifold smoothness of their actual ambient matrix values. -/
theorem contMDiffWithinAt_iff_value :
    ContMDiffWithinAt I 𝓘(ℝ, Model) n f s x ↔
      ContMDiffWithinAt I 𝓘(ℝ, Mat2) n (fun y => (f y).val) s x := by
  constructor
  · intro hf
    exact (contMDiff_value n).contMDiffAt.comp_contMDiffWithinAt x hf
  · intro hf
    apply contMDiffWithinAt_iff_target.mpr
    refine ⟨IsInducing.subtypeVal.continuousWithinAt_iff.mpr hf.continuousWithinAt, ?_⟩
    obtain ⟨P, hP⟩ := chart_linear (chartAt Model (f x)) (chart_mem_atlas Model (f x))
    have he : (extChartAt 𝓘(ℝ, Model) (f x) ∘ f) = P ∘ (fun y => (f y).val) := by
      funext y
      simpa only [mfld_simps] using hP (f y)
    rw [he]
    exact P.contMDiffAt.comp_contMDiffWithinAt x hf

/-- For an arbitrary charted source, intrinsic smoothness at a point is equivalent to manifold smoothness of the actual ambient matrix-valued map. -/
theorem contMDiffAt_iff_value :
    ContMDiffAt I 𝓘(ℝ, Model) n f x ↔
      ContMDiffAt I 𝓘(ℝ, Mat2) n (fun y => (f y).val) x :=
  contMDiffWithinAt_iff_value

/-- For an arbitrary charted source, intrinsic smoothness on any set is equivalent to manifold smoothness of the actual ambient matrix-valued map on that set. -/
theorem contMDiffOn_iff_value :
    ContMDiffOn I 𝓘(ℝ, Model) n f s ↔
      ContMDiffOn I 𝓘(ℝ, Mat2) n (fun y => (f y).val) s := by
  simp only [ContMDiffOn, contMDiffWithinAt_iff_value]

/-- For an arbitrary charted source, global intrinsic smoothness is equivalent to manifold smoothness of the actual ambient matrix-valued map. -/
theorem contMDiff_iff_value :
    ContMDiff I 𝓘(ℝ, Model) n f ↔
      ContMDiff I 𝓘(ℝ, Mat2) n (fun y => (f y).val) := by
  simp only [ContMDiff, contMDiffAt_iff_value]

end GeneralSource

section NormedSource
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {n : WithTop ℕ∞} {f : E → SpecialLinearMatrix} {s : Set E} {x : E}

/-- For a real normed source, intrinsic smoothness within any set is exactly actual real Frechet smoothness of the underlying matrix-valued map. -/
theorem contMDiffWithinAt_iff_contDiffWithinAt_value :
    ContMDiffWithinAt 𝓘(ℝ, E) 𝓘(ℝ, Model) n f s x ↔
      ContDiffWithinAt ℝ n (fun y => (f y).val) s x :=
  contMDiffWithinAt_iff_value.trans _root_.contMDiffWithinAt_iff_contDiffWithinAt

/-- For a real normed source, intrinsic smoothness at a point is exactly actual real Frechet smoothness of the underlying matrix-valued map. -/
theorem contMDiffAt_iff_contDiffAt_value :
    ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, Model) n f x ↔
      ContDiffAt ℝ n (fun y => (f y).val) x :=
  contMDiffAt_iff_value.trans _root_.contMDiffAt_iff_contDiffAt

/-- For a real normed source, intrinsic smoothness on any set is exactly actual real Frechet smoothness of the underlying matrix-valued map on that set. -/
theorem contMDiffOn_iff_contDiffOn_value :
    ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, Model) n f s ↔
      ContDiffOn ℝ n (fun y => (f y).val) s :=
  contMDiffOn_iff_value.trans _root_.contMDiffOn_iff_contDiffOn

/-- For a real normed source, global intrinsic smoothness is exactly actual real Frechet smoothness of the underlying matrix-valued map. -/
theorem contMDiff_iff_contDiff_value :
    ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, Model) n f ↔
      ContDiff ℝ n (fun y => (f y).val) :=
  contMDiff_iff_value.trans _root_.contMDiff_iff_contDiff

end NormedSource
end FoliationQM.SpecialLinearManifold
