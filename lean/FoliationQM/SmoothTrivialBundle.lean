module
public import Mathlib.Topology.FiberBundle.Constructions
public import Mathlib.Geometry.Manifold.Diffeomorph
public import Mathlib.Geometry.Manifold.ContMDiffMap

/-!
# Actual smooth trivial bundles and their dependent sections

Source: the fixed-representation bundle and section bridge used in v13
`prop:takabayasi`. This construction uses the standard `Bundle.Trivial`
family, its actual total space, existing natural topology, and standard
fiber-bundle structure. The explicit total-space atlas is pulled back
from the independently supplied base and fiber product atlas through
the standard bundle homeomorphism. Smoothness of the actual trivialization
and its inverse is proved; smooth base and fiber manifolds give a smooth
total manifold. The atlas is an explicit definition used locally, so it
does not replace other globally registered bundle atlases.

A smooth section is a dependent fiber-valued function whose actual
bundle total-space graph is smooth. This is proved equivalent to
smoothness of its fiber values. A genuine fiber diffeomorphism induces
an actual base-preserving total-space diffeomorphism and a bijection of
these smooth dependent sections, with exact pointwise and graph laws.
These are trivial-bundle results; arbitrary twisted bundles, transition
cocycles, and global individual polar representatives are separate.
-/

@[expose] public section
noncomputable section
open scoped Manifold
open Set Function Topology
namespace FoliationQM.SmoothTrivialBundle

/-- The actual total space of the standard trivial bundle. -/
abbrev Total (B F : Type*) := Bundle.TotalSpace F (Bundle.Trivial B F)

section Topology
variable (H H' B F : Type*) [TopologicalSpace H] [TopologicalSpace H']
  [TopologicalSpace B] [TopologicalSpace F] [ChartedSpace H B] [ChartedSpace H' F]

/-- The actual trivial-bundle total space retains its natural topology and uses the explicit pullback of the base-and-fiber product atlas. -/
@[instance_reducible]
def totalChartedSpace : ChartedSpace (ModelProd H H') (Total B F) where
  atlas := {e | ∃ e' ∈ atlas (ModelProd H H') (B × F),
    e = (Bundle.Trivial.homeomorphProd B F).transOpenPartialHomeomorph e'}
  chartAt z := (Bundle.Trivial.homeomorphProd B F).transOpenPartialHomeomorph
    (chartAt (ModelProd H H') (Bundle.Trivial.homeomorphProd B F z))
  mem_chart_source z := mem_chart_source (ModelProd H H') (Bundle.Trivial.homeomorphProd B F z)
  chart_mem_atlas z := ⟨_, chart_mem_atlas (ModelProd H H') (Bundle.Trivial.homeomorphProd B F z), rfl⟩

end Topology
attribute [local instance] totalChartedSpace

section Smooth
variable {E E' H H' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H] [TopologicalSpace H']
  (I : ModelWithCorners ℝ E H) (J : ModelWithCorners ℝ E' H')
  (B F : Type*) [TopologicalSpace B] [TopologicalSpace F]
  [ChartedSpace H B] [ChartedSpace H' F]

/-- The preferred total-space chart is exactly the product chart after the actual standard trivial-bundle homeomorphism. -/
theorem total_chartAt (z : Total B F) :
    chartAt (ModelProd H H') z = (Bundle.Trivial.homeomorphProd B F).transOpenPartialHomeomorph
      (chartAt (ModelProd H H') (Bundle.Trivial.homeomorphProd B F z)) := rfl

/-- Smooth base and fiber atlases make the actual trivial-bundle total atlas smooth to the same order. -/
theorem isManifold_total (n : WithTop ℕ∞) [IsManifold I n B] [IsManifold J n F] :
    IsManifold (I.prod J) n (Total B F) where
  compatible := by
    rintro e e' ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    rw [Homeomorph.transOpenPartialHomeomorph_symm_trans]
    exact (contDiffGroupoid n (I.prod J)).compatible ha hb

variable (n : WithTop ℕ∞)

/-- The actual standard total-space-to-product homeomorphism is smooth for the explicit total atlas. -/
theorem contMDiff_toProd :
    ContMDiff (I.prod J) (I.prod J) n (Bundle.Trivial.homeomorphProd B F) := by
  intro z
  have hh := (contMDiff_id (I := I.prod J) (n := n) :
    ContMDiff (I.prod J) (I.prod J) n (fun p : B × F => p))
      (Bundle.Trivial.homeomorphProd B F z)
  rw [contMDiffAt_iff] at hh ⊢
  refine ⟨(Bundle.Trivial.homeomorphProd B F).continuous.continuousAt, ?_⟩
  convert hh.2 using 1
  all_goals simp [total_chartAt, Function.comp_def]
  all_goals first | rfl | constructor <;> rfl

/-- The actual inverse standard product-to-total-space homeomorphism is smooth for the explicit total atlas. -/
theorem contMDiff_fromProd :
    ContMDiff (I.prod J) (I.prod J) n (Bundle.Trivial.homeomorphProd B F).symm := by
  intro p
  have hh := (contMDiff_id (I := I.prod J) (n := n) :
    ContMDiff (I.prod J) (I.prod J) n (fun p : B × F => p)) p
  rw [contMDiffAt_iff] at hh ⊢
  refine ⟨(Bundle.Trivial.homeomorphProd B F).symm.continuous.continuousAt, ?_⟩
  convert hh.2 using 1
  all_goals simp [total_chartAt, Function.comp_def]
  all_goals rfl

/-- The standard natural trivialization is a genuine global diffeomorphism for the actual total-space and product atlases. -/
def totalDiffeomorph : Diffeomorph (I.prod J) (I.prod J) (Total B F) (B × F) n where
  toEquiv := (Bundle.Trivial.homeomorphProd B F).toEquiv
  contMDiff_toFun := contMDiff_toProd I J B F n
  contMDiff_invFun := contMDiff_fromProd I J B F n

/-- The total-space diffeomorphism retains exactly the standard natural bundle homeomorphism. -/
theorem totalDiffeomorph_toHomeomorph :
    (totalDiffeomorph I J B F n).toHomeomorph = Bundle.Trivial.homeomorphProd B F := rfl

/-- The standard bundle trivialization is smooth for the explicit total-space atlas. -/
theorem contMDiff_trivialization :
    ContMDiff (I.prod J) (I.prod J) n (Bundle.Trivial.trivialization B F) :=
  contMDiff_toProd I J B F n

/-- The inverse of the standard bundle trivialization is smooth for the explicit total-space atlas. -/
theorem contMDiff_trivialization_symm :
    ContMDiff (I.prod J) (I.prod J) n
      (Bundle.Trivial.trivialization B F).toOpenPartialHomeomorph.symm :=
  contMDiff_fromProd I J B F n

/-- The actual bundle projection is smooth for the supplied smooth base and fiber manifolds. -/
theorem contMDiff_proj :
    ContMDiff (I.prod J) I n (Bundle.TotalSpace.proj : Total B F → B) :=
  (contMDiff_toProd I J B F n).fst

/-- A dependent section of the actual trivial bundle is smooth exactly when its fiber-valued function is smooth. -/
theorem contMDiff_graph_iff (f : ∀ b : B, Bundle.Trivial B F b) :
    ContMDiff I (I.prod J) n (fun b => (⟨b, f b⟩ : Total B F)) ↔
      ContMDiff I J n f := by
  constructor
  · intro h
    exact ((contMDiff_toProd I J B F n).comp h).snd
  · intro h
    exact (contMDiff_fromProd I J B F n).comp (contMDiff_id.prodMk h)

/-- Smooth dependent sections of the actual trivial bundle, defined by smoothness of their total-space graph. -/
def SmoothSection := {f : ∀ b : B, Bundle.Trivial B F b //
  ContMDiff I (I.prod J) n (fun b => (⟨b, f b⟩ : Total B F))}

/-- Smooth actual trivial-bundle sections correspond exactly to bundled smooth fiber-valued maps. -/
def sectionEquiv : SmoothSection I J B F n ≃ ContMDiffMap I J B F n where
  toFun s := ⟨s.val, (contMDiff_graph_iff I J B F n s.val).mp s.property⟩
  invFun f := ⟨f, (contMDiff_graph_iff I J B F n f).mpr f.contMDiff⟩
  left_inv _ := rfl
  right_inv _ := rfl

end Smooth
section FiberMap
variable {E E' E'' H H' H'' : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E']
  [NormedAddCommGroup E''] [NormedSpace ℝ E'']
  [TopologicalSpace H] [TopologicalSpace H'] [TopologicalSpace H'']
  (I : ModelWithCorners ℝ E H)
  {J : ModelWithCorners ℝ E' H'} {K : ModelWithCorners ℝ E'' H''}
  (B : Type*) {F G : Type*} [TopologicalSpace B] [TopologicalSpace F] [TopologicalSpace G]
  [ChartedSpace H B] [ChartedSpace H' F] [ChartedSpace H'' G]
  {n : WithTop ℕ∞} (h : Diffeomorph J K F G n)

/-- A genuine fiber diffeomorphism induces a genuine total-space diffeomorphism of the actual trivial bundles over the same base. -/
def totalMapDiffeomorph :
    Diffeomorph (I.prod J) (I.prod K) (Total B F) (Total B G) n := by
  let p : Diffeomorph (I.prod J) (I.prod K) (B × F) (B × G) n := {
    toEquiv := (Equiv.refl B).prodCongr h.toEquiv
    contMDiff_toFun := contMDiff_fst.prodMk (h.contMDiff.comp contMDiff_snd)
    contMDiff_invFun := contMDiff_fst.prodMk (h.symm.contMDiff.comp contMDiff_snd) }
  exact (totalDiffeomorph I J B F n).trans (p.trans (totalDiffeomorph I K B G n).symm)

/-- The induced total-space diffeomorphism applies the actual fiber map and keeps the base point. -/
theorem totalMapDiffeomorph_apply (z : Total B F) :
    totalMapDiffeomorph I B h z = ⟨z.proj, h z.snd⟩ := rfl

/-- The actual bundle projection is preserved by the induced total-space diffeomorphism. -/
theorem totalMapDiffeomorph_proj (z : Total B F) :
    (totalMapDiffeomorph I B h z).proj = z.proj := rfl

/-- The fiber value of the induced total-space diffeomorphism is exactly the given fiber diffeomorphism. -/
theorem totalMapDiffeomorph_snd (z : Total B F) :
    (totalMapDiffeomorph I B h z).snd = h z.snd := rfl

/-- A genuine fiber diffeomorphism induces a bijection of smooth dependent sections of the actual trivial bundles. -/
def sectionCongr : SmoothSection I J B F n ≃ SmoothSection I K B G n where
  toFun s := ⟨fun b => h (s.val b), (contMDiff_graph_iff I K B G n _).mpr
    (h.contMDiff.comp ((contMDiff_graph_iff I J B F n _).mp s.property))⟩
  invFun s := ⟨fun b => h.symm (s.val b), (contMDiff_graph_iff I J B F n _).mpr
    (h.symm.contMDiff.comp ((contMDiff_graph_iff I K B G n _).mp s.property))⟩
  left_inv s := Subtype.ext (funext fun b => h.symm_apply_apply (s.val b))
  right_inv s := Subtype.ext (funext fun b => h.apply_symm_apply (s.val b))

/-- The smooth-section correspondence evaluates pointwise by the actual fiber diffeomorphism. -/
theorem sectionCongr_apply (s : SmoothSection I J B F n) (b : B) :
    (sectionCongr I B h s).val b = h (s.val b) := rfl

/-- The inverse smooth-section correspondence evaluates pointwise by the actual inverse fiber diffeomorphism. -/
theorem sectionCongr_symm_apply (s : SmoothSection I K B G n) (b : B) :
    ((sectionCongr I B h).symm s).val b = h.symm (s.val b) := rfl

/-- Mapping a smooth actual section commutes exactly with taking its actual total-space graph. -/
theorem sectionCongr_graph (s : SmoothSection I J B F n) (b : B) :
    totalMapDiffeomorph I B h (⟨b, s.val b⟩ : Total B F) =
      (⟨b, (sectionCongr I B h s).val b⟩ : Total B G) := rfl

end FiberMap
end FoliationQM.SmoothTrivialBundle
