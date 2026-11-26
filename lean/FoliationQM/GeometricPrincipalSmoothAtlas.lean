module
public import FoliationQM.GeometricPrincipalAtlas
public import Mathlib.Geometry.Manifold.Algebra.LieGroup
public import Mathlib.Geometry.Manifold.LocalDiffeomorph

/-!
# Smoothness from independent geometric principal charts

Source scope: the smooth geometric principal-bundle bridge underlying
v13 `prop:takabayasi`. The base, group and original total space retain
independently supplied charted-space structures and models. The only
additional geometric regularity premises are smoothness of the actual
principal trivializations and their actual inverses on their genuine
source and target domains.

Canonical unit sections, geometric transition functions and the original
projection are then proved smooth. The original right operation is
jointly smooth when the supplied group multiplication is smooth. Actual
trivializations also give genuine partial diffeomorphisms between the
independent total model and the base/group product model. No total atlas
is defined by transport through a desired reconstruction, and no smooth
principal action or geometric Spin lift is assumed as a conclusion.
-/

@[expose] public section
noncomputable section
open Set Function Bundle Topology
open scoped Topology Manifold
namespace FoliationQM.GeometricPrincipalSmoothAtlas

variable {EB EG EP HB HG HP B G P : Type*}
  [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [NormedAddCommGroup EP] [NormedSpace ℝ EP]
  [TopologicalSpace HB] [TopologicalSpace HG] [TopologicalSpace HP]
  [TopologicalSpace B] [ChartedSpace HB B]
  [TopologicalSpace G] [ChartedSpace HG G] [Group G]
  [TopologicalSpace P] [ChartedSpace HP P]
  {proj : P → B} {ι : Type*}

/-- Smooth geometric principal-atlas data over an independently charted total space, requiring only true-domain regularity of its original trivializations and inverses. -/
structure Data (I : ModelWithCorners ℝ EB HB) (J : ModelWithCorners ℝ EG HG)
    (K : ModelWithCorners ℝ EP HP) (A : GeometricPrincipalAtlas.Data (G := G) proj ι)
    (n : WithTop ℕ∞) where
  /-- Each actual principal trivialization is smooth on its original source. -/
  smooth_triv : ∀ i, ContMDiffOn K (I.prod J) n (A.triv i) (A.triv i).source
  /-- Each actual inverse trivialization is smooth on its original target. -/
  smooth_symm : ∀ i, ContMDiffOn (I.prod J) K n
    (A.triv i).toOpenPartialHomeomorph.symm (A.triv i).target

namespace Data
variable {I : ModelWithCorners ℝ EB HB} {J : ModelWithCorners ℝ EG HG}
  {K : ModelWithCorners ℝ EP HP} {A : GeometricPrincipalAtlas.Data (G := G) proj ι}
  {n : WithTop ℕ∞} (S : Data I J K A n)

include S

/-- An actual principal trivialization is smooth at every point of its original open source. -/
theorem contMDiffAt_triv (i : ι) (p : P) (hp : proj p ∈ (A.triv i).baseSet) :
    ContMDiffAt K (I.prod J) n (A.triv i) p :=
  (S.smooth_triv i).contMDiffAt
    ((A.triv i).open_source.mem_nhds ((A.triv i).mem_source.mpr hp))

/-- An actual inverse principal trivialization is smooth at every point of its original open target. -/
theorem contMDiffAt_symm (i : ι) (x : B × G) (hx : x.1 ∈ (A.triv i).baseSet) :
    ContMDiffAt (I.prod J) K n (A.triv i).toOpenPartialHomeomorph.symm x :=
  (S.smooth_symm i).contMDiffAt
    ((A.triv i).open_target.mem_nhds ((A.triv i).mem_target.mpr hx))

/-- Canonical geometric unit sections are smooth on their actual base chart domains, through the independently supplied inverse trivializations. -/
theorem contMDiffOn_localSection (i : ι) :
    ContMDiffOn I K n (A.localSection i) (A.triv i).baseSet :=
  (S.smooth_symm i).comp (contMDiff_id.prodMk contMDiff_const).contMDiffOn
    (fun _ hx => (A.triv i).mem_target.mpr hx)

/-- The actual geometric group transitions are smooth on their genuine pair overlaps, derived from unit sections and the original geometric charts. -/
theorem contMDiffOn_transition (i j : ι) :
    ContMDiffOn I J n (A.transition i j) ((A.triv i).baseSet ∩ (A.triv j).baseSet) := by
  have hs : ContMDiffOn I K n (A.localSection i)
      ((A.triv i).baseSet ∩ (A.triv j).baseSet) :=
    (S.contMDiffOn_localSection i).mono inter_subset_left
  have ht := (S.smooth_triv j).comp hs (by
    intro x hx
    apply (A.triv j).mem_source.mpr
    rw [A.proj_localSection i x hx.1]
    exact hx.2)
  intro x hx
  exact (ht x hx).snd

/-- The original geometric bundle projection is smooth for its independent total-space and base charted structures. -/
theorem contMDiff_proj : ContMDiff K I n proj := by
  intro p
  obtain ⟨i, hi⟩ := A.covers (proj p)
  have ht := (S.contMDiffAt_triv i p hi).fst
  apply ht.congr_of_eventuallyEq
  filter_upwards [(A.triv i).open_source.mem_nhds ((A.triv i).mem_source.mpr hi)] with q hq
  exact ((A.triv i).coe_fst hq).symm

/-- Actual geometric bundle trivializations, with their original maps and domains, form genuine partial diffeomorphisms for the independent total and product models. -/
def localTrivDiffeomorph (i : ι) : PartialDiffeomorph K (I.prod J) P (B × G) n where
  toPartialEquiv := (A.triv i).toPartialEquiv
  open_source := (A.triv i).open_source
  open_target := (A.triv i).open_target
  contMDiffOn_toFun := S.smooth_triv i
  contMDiffOn_invFun := S.smooth_symm i

/-- The original geometric right operation is jointly smooth, derived from true chart formulas and smooth group multiplication rather than assumed as principal-bundle data. -/
theorem contMDiff_right [ContMDiffMul J n G] :
    ContMDiff (K.prod J) K n (fun z : P × G => A.right z.1 z.2) := by
  intro z
  obtain ⟨i, hi⟩ := A.covers (proj z.1)
  have ht := (S.contMDiffAt_triv i z.1 hi).comp z
    (contMDiff_fst : ContMDiff (K.prod J) K n (Prod.fst : P × G → P)).contMDiffAt
  have hb : ContMDiffAt (K.prod J) I n (fun y : P × G => proj y.1) z :=
    S.contMDiff_proj.contMDiffAt.comp z contMDiff_fst.contMDiffAt
  have hg : ContMDiffAt (K.prod J) J n (Prod.snd : P × G → G) z :=
    contMDiff_snd.contMDiffAt
  have hm := (contMDiff_mul J n).contMDiffAt.comp z (ht.snd.prodMk hg)
  have hs := (S.contMDiffAt_symm i (proj z.1, (A.triv i z.1).2 * z.2) hi).comp z
    (hb.prodMk hm)
  apply hs.congr_of_eventuallyEq
  filter_upwards [hb.continuousAt.preimage_mem_nhds ((A.triv i).open_baseSet.mem_nhds hi)] with y hy
  exact A.right_eq_symm i y.1 y.2 hy

end Data
end FoliationQM.GeometricPrincipalSmoothAtlas
