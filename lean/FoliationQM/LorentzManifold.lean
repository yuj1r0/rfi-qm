module
public import FoliationQM.LorentzCayleyCharts
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

/-!
# Independent six-dimensional proper future Lorentz manifold

Source scope: the independent Lorentz-frame target underlying v13
`prop:takabayasi` and `eq:tetrad_rotor_map`. The existing proper future
matrix-unit subgroup receives the actual translated real Cayley atlas.
The topology is unchanged. Every overlap is smooth because the ambient
rational forward coordinates are smooth at the overlap's genuine unit
denominator and the actual inverse-chart matrix values are smooth on
their specified future target. No Spin map defines this atlas.

The actual matrix inclusion is smooth, and intrinsic smoothness into the
Lorentz manifold is equivalent to smoothness of the actual ambient real
matrix values. The equivalence holds for arbitrary charted source spaces
and arbitrary within-set domains; no smoothness or denominator premise
is imposed on the source map beyond the stated ambient regularity.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Matrix.Norms.Operator Manifold
open Set Topology
namespace FoliationQM.LorentzManifold
open LorentzMatrixGroup LorentzCayleyCharts

/-- The intrinsic Lorentz manifold uses the six actual real Cayley coordinates. -/
abbrev Model := LorentzCayleyCharts.Model

/-- The chart model is the same six-coordinate real normed space. -/
abbrev ChartModel := Model

/-- The independent Lorentz manifold has the ordinary real model with no boundary. -/
abbrev model := 𝓘(ℝ, Model)

/-- The actual ambient matrix value of an independently defined proper future Lorentz element. -/
def value (L : ProperFutureLorentz) : Mat4 := matrix L.val

/-- Ambient values retain exactly the pre-existing underlying real matrices. -/
theorem value_apply (L : ProperFutureLorentz) : value L = matrix L.val := rfl

/-- The actual matrix map embeds the unchanged Lorentz subgroup topology. -/
theorem isEmbedding_value : IsEmbedding value :=
  LorentzMatrixTopology.isClosedEmbedding_properMatrix.isEmbedding

/-- The independently defined Lorentz group carries all its actual translated Cayley charts, centered at each point. -/
instance instChartedSpaceProperFutureLorentz : ChartedSpace Model ProperFutureLorentz where
  atlas := Set.range chart
  chartAt := chart
  mem_chart_source := mem_chart_source
  chart_mem_atlas L := ⟨L, rfl⟩

/-- The intrinsic atlas consists exactly of the actual translated Cayley charts. -/
theorem mem_atlas_iff (e : OpenPartialHomeomorph ProperFutureLorentz Model) :
    e ∈ atlas Model ProperFutureLorentz ↔ ∃ L, chart L = e := Iff.rfl

/-- The chart selected at a Lorentz element is its own actual translated Cayley chart. -/
theorem chartAt_eq_chart (L : ProperFutureLorentz) : chartAt Model L = chart L := rfl

/-- Every actual inverse chart has smooth ambient matrix values on its full target. -/
theorem contDiffOn_value_symm (n : WithTop ℕ∞)
    (e : OpenPartialHomeomorph ProperFutureLorentz Model)
    (he : e ∈ atlas Model ProperFutureLorentz) :
    ContDiffOn ℝ n (value ∘ e.symm) e.target := by
  obtain ⟨L, rfl⟩ := (mem_atlas_iff e).mp he
  exact contDiffOn_inverse_matrix n L

/-- Every genuine Cayley transition is smooth on its actual overlap, with the required matrix denominator derived from overlap membership. -/
theorem contDiffOn_transition (n : WithTop ℕ∞) (L K : ProperFutureLorentz) :
    ContDiffOn ℝ n ((chart L).symm.trans (chart K))
      ((chart L).symm.trans (chart K)).source := by
  have heq : ((chart L).symm.trans (chart K) : Model → Model) =
      ambientCoordinates K ∘ (value ∘ (chart L).symm) := by
    funext q
    exact chart_apply K ((chart L).symm q)
  rw [heq]
  intro q hq
  have hunit := (mem_chart_source_iff K ((chart L).symm q)).mp hq.2
  have hforward := contDiffAt_ambientCoordinates n K hunit
  have hinverse := (contDiffOn_inverse_matrix n L) q hq.1
  exact hforward.comp_contDiffWithinAt q
    (hinverse.mono (fun _ hp => hp.1))

/-- The independently constructed rational atlas makes the actual proper future Lorentz group a real manifold to every order. -/
instance instIsManifoldProperFutureLorentz (n : WithTop ℕ∞) :
    IsManifold model n ProperFutureLorentz := by
  apply isManifold_of_contDiffOn
  intro e e' he he'
  obtain ⟨L, rfl⟩ := (mem_atlas_iff e).mp he
  obtain ⟨K, rfl⟩ := (mem_atlas_iff e').mp he'
  simpa only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
    Function.id_comp, Function.comp_id, Set.preimage_id, Set.range_id, Set.inter_univ] using
    contDiffOn_transition n L K

/-- The independent real Lorentz chart model has dimension six. -/
theorem model_finrank : Module.finrank ℝ Model = 6 := by
  simp [Model, LorentzCayleyCharts.Model, LorentzCayleyCoordinates.Coordinates]

/-- The actual real-matrix inclusion is smooth to every order for the independently proved Cayley atlas. -/
theorem contMDiff_value (n : WithTop ℕ∞) :
    ContMDiff model 𝓘(ℝ, Mat4) n value := by
  apply contMDiff_iff.mpr
  refine ⟨continuous_matrix.comp continuous_subtype_val, ?_⟩
  intro L M
  simpa only [mfld_simps] using
    contDiffOn_value_symm n (chartAt Model L) (chart_mem_atlas Model L)

section GeneralSource
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M]
  {n : WithTop ℕ∞} {f : M → ProperFutureLorentz} {s : Set M} {x : M}

/-- On any source set in any charted source, intrinsic Lorentz smoothness is exactly smoothness of the actual ambient matrix map. -/
theorem contMDiffWithinAt_iff_value :
    ContMDiffWithinAt I model n f s x ↔
      ContMDiffWithinAt I 𝓘(ℝ, Mat4) n (fun y => value (f y)) s x := by
  constructor
  · intro hf
    exact (contMDiff_value n).contMDiffAt.comp_contMDiffWithinAt x hf
  · intro hf
    apply contMDiffWithinAt_iff_target.mpr
    refine ⟨isEmbedding_value.isInducing.continuousWithinAt_iff.mpr hf.continuousWithinAt, ?_⟩
    have he : extChartAt model (f x) ∘ f =
        ambientCoordinates (f x) ∘ (fun y => value (f y)) := by
      funext y
      simpa only [mfld_simps, chartAt_eq_chart, value] using chart_apply (f x) (f y)
    rw [he]
    have hunit := (mem_chart_source_iff (f x) (f x)).mp (mem_chart_source (f x))
    exact (contDiffAt_ambientCoordinates n (f x) hunit).comp_contMDiffWithinAt
      (f := fun y => value (f y)) hf

/-- At every point of an arbitrary charted source, Lorentz smoothness is equivalent to smoothness of the actual real matrix values. -/
theorem contMDiffAt_iff_value :
    ContMDiffAt I model n f x ↔
      ContMDiffAt I 𝓘(ℝ, Mat4) n (fun y => value (f y)) x :=
  contMDiffWithinAt_iff_value

/-- On any set in an arbitrary charted source, Lorentz smoothness is equivalent to smoothness of the actual real matrix values. -/
theorem contMDiffOn_iff_value :
    ContMDiffOn I model n f s ↔
      ContMDiffOn I 𝓘(ℝ, Mat4) n (fun y => value (f y)) s := by
  simp only [ContMDiffOn, contMDiffWithinAt_iff_value]

/-- Global smoothness into the independent Lorentz manifold is equivalent to smoothness of its actual ambient real matrix map. -/
theorem contMDiff_iff_value :
    ContMDiff I model n f ↔
      ContMDiff I 𝓘(ℝ, Mat4) n (fun y => value (f y)) := by
  simp only [ContMDiff, contMDiffAt_iff_value]

end GeneralSource

section NormedSource
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {n : WithTop ℕ∞} {f : E → ProperFutureLorentz} {s : Set E} {x : E}

/-- For a real normed source, intrinsic Lorentz smoothness within a set is exactly real Frechet smoothness of the actual matrix map. -/
theorem contMDiffWithinAt_iff_contDiffWithinAt_value :
    ContMDiffWithinAt 𝓘(ℝ, E) model n f s x ↔
      ContDiffWithinAt ℝ n (fun y => value (f y)) s x :=
  contMDiffWithinAt_iff_value.trans _root_.contMDiffWithinAt_iff_contDiffWithinAt

/-- For a real normed source, intrinsic Lorentz smoothness at a point is exactly real Frechet smoothness of the actual matrix map. -/
theorem contMDiffAt_iff_contDiffAt_value :
    ContMDiffAt 𝓘(ℝ, E) model n f x ↔
      ContDiffAt ℝ n (fun y => value (f y)) x :=
  contMDiffAt_iff_value.trans _root_.contMDiffAt_iff_contDiffAt

/-- For a real normed source, intrinsic Lorentz smoothness on any set is exactly real Frechet smoothness of the actual matrix map. -/
theorem contMDiffOn_iff_contDiffOn_value :
    ContMDiffOn 𝓘(ℝ, E) model n f s ↔
      ContDiffOn ℝ n (fun y => value (f y)) s :=
  contMDiffOn_iff_value.trans _root_.contMDiffOn_iff_contDiffOn

/-- For a real normed source, global intrinsic Lorentz smoothness is exactly real Frechet smoothness of the actual matrix map. -/
theorem contMDiff_iff_contDiff_value :
    ContMDiff 𝓘(ℝ, E) model n f ↔
      ContDiff ℝ n (fun y => value (f y)) :=
  contMDiff_iff_value.trans _root_.contMDiff_iff_contDiff

end NormedSource
end FoliationQM.LorentzManifold
