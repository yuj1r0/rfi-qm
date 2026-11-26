module
public import FoliationQM.PrincipalCocycleBundle

/-!
# Genuine smooth principal bundle maps from cocycle homomorphisms

Source scope: the geometric Spin-frame bridge underlying v13 `prop:takabayasi`.
Two independently supplied smooth group cocycles have the same actual cover.
A smooth group homomorphism relates their transitions only on genuine overlaps.
It induces a map of their actual core-generated total spaces. The construction
uses the source-selected chart and the target's true inverse trivialization;
there is no assumption that the two pointwise chart choices agree or are smooth.
The local coordinate formula proves projection preservation, equivariance,
continuity and smoothness. Surjectivity is derived when the group homomorphism
is surjective. No Spin lift of an arbitrary Lorentz cocycle is assumed here.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Function Bundle Topology
open scoped Manifold
namespace FoliationQM.PrincipalCocycleMorphism
open PrincipalCocycleBundle

variable {E E' E'' H H' H'' : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E']
  [NormedAddCommGroup E''] [NormedSpace ℝ E'']
  [TopologicalSpace H] [TopologicalSpace H'] [TopologicalSpace H'']
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ E' H'}
  {K : ModelWithCorners ℝ E'' H''}
  {B G G' : Type*} [TopologicalSpace B] [ChartedSpace H B]
  [Group G] [TopologicalSpace G] [ChartedSpace H' G]
  [Group G'] [TopologicalSpace G'] [ChartedSpace H'' G']
  {ι : Type*} {n : WithTop ℕ∞}

/-- A smooth group homomorphism with actual same-cover cocycle compatibility only on the true pair overlaps. -/
structure Data (S : PrincipalCocycleBundle.Data I J B G ι n)
    (T : PrincipalCocycleBundle.Data I K B G' ι n) (φ : G →* G') where
  /-- The two cocycles have exactly the same actual chart domains. -/
  domain_eq : S.domain = T.domain
  /-- The homomorphism is smooth in the independently supplied group atlases. -/
  smooth_hom : ContMDiff J K n φ
  /-- Projection of the source transition equals the target transition on every genuine overlap. -/
  transition : ∀ i j x, x ∈ S.domain i → x ∈ S.domain j →
    φ (S.transition i j x) = T.transition i j x

namespace Data

variable {S : PrincipalCocycleBundle.Data I J B G ι n}
  {T : PrincipalCocycleBundle.Data I K B G' ι n} {φ : G →* G'}
  (D : Data S T φ)

include D in
/-- A genuine source chart contains a base point exactly when the corresponding target chart does. -/
theorem mem_domain_iff (i : ι) (x : B) : x ∈ S.domain i ↔ x ∈ T.domain i := by
  rw [D.domain_eq]

variable [ContMDiffMul J n G] [ContMDiffMul K n G']

/-- The actual total-space map uses the source-selected chart and the target's independently constructed inverse trivialization. -/
def totalMap (_D : Data S T φ) (p : Total S) : Total T :=
  ((core T).localTriv (indexAt S p.proj)).toOpenPartialHomeomorph.symm
    (p.proj, φ (fiberValue S p))

/-- The constructed genuine total-space map preserves the actual base point. -/
theorem totalMap_proj (p : Total S) : (D.totalMap p).proj = p.proj := rfl

/-- In every containing actual chart, the bundle map has exactly the supplied group-homomorphism coordinate expression. -/
theorem localTriv_totalMap (i : ι) (p : Total S) (hp : p.proj ∈ S.domain i) :
    (core T).localTriv i (D.totalMap p) =
      (p.proj, φ (((core S).localTriv i p).2)) := by
  apply Prod.ext
  · rfl
  · change T.transition (indexAt T p.proj) i p.proj *
        (T.transition (indexAt S p.proj) (indexAt T p.proj) p.proj * φ (fiberValue S p)) =
      φ (S.transition (indexAt S p.proj) i p.proj * fiberValue S p)
    rw [φ.map_mul, D.transition _ _ _ (mem_domain_indexAt S p.proj) hp, ← mul_assoc,
      T.comp _ _ _ p.proj
        ((D.mem_domain_iff _ _).mp (mem_domain_indexAt S p.proj))
        (mem_domain_indexAt T p.proj) ((D.mem_domain_iff _ _).mp hp)]

/-- On any genuine chart the total-space map is reconstructed by the target's actual inverse chart and the homomorphic source coordinate. -/
theorem totalMap_eq_symm (i : ι) (p : Total S) (hp : p.proj ∈ S.domain i) :
    D.totalMap p = ((core T).localTriv i).toOpenPartialHomeomorph.symm
      (p.proj, φ (((core S).localTriv i p).2)) := by
  rw [← D.localTriv_totalMap i p hp]
  exact (((core T).localTriv i).left_inv ((D.mem_domain_iff i p.proj).mp hp)).symm

/-- The map on an actual source inverse chart is the target inverse chart applied to the original base and the homomorphic fiber coordinate. -/
theorem totalMap_symm (i : ι) (x : B) (g : G) (hx : x ∈ S.domain i) :
    D.totalMap (((core S).localTriv i).toOpenPartialHomeomorph.symm (x, g)) =
      ((core T).localTriv i).toOpenPartialHomeomorph.symm (x, φ g) := by
  rw [D.totalMap_eq_symm i _ (show x ∈ S.domain i from hx),
    ((core S).localTriv i).apply_symm_apply' hx]
  rfl

/-- The actual total-space map is equivariant for the supplied group homomorphism and the derived principal right actions. -/
theorem totalMap_rightAct (p : Total S) (g : G) :
    D.totalMap (rightAct S p g) = rightAct T (D.totalMap p) (φ g) := by
  let i := indexAt S p.proj
  have hi := mem_domain_indexAt S p.proj
  apply (geometricData T).coordinate_injective i
    (p := D.totalMap (rightAct S p g)) (q := rightAct T (D.totalMap p) (φ g))
    ((D.mem_domain_iff i p.proj).mp hi) ((D.mem_domain_iff i p.proj).mp hi) rfl
  change ((core T).localTriv i (D.totalMap (rightAct S p g))).2 =
    ((core T).localTriv i (rightAct T (D.totalMap p) (φ g))).2
  simp only [D.localTriv_totalMap i (rightAct S p g) hi,
    localTriv_rightAct S i p g, localTriv_rightAct T i (D.totalMap p) (φ g),
    D.localTriv_totalMap i p hi, φ.map_mul]

/-- A surjective group homomorphism induces a surjective actual principal bundle map on the same cover. -/
theorem totalMap_surjective (hφ : Surjective φ) : Surjective D.totalMap := by
  intro p
  let i := indexAt T p.proj
  have hi : p.proj ∈ S.domain i :=
    (D.mem_domain_iff i p.proj).mpr (mem_domain_indexAt T p.proj)
  obtain ⟨g, hg⟩ := hφ (((core T).localTriv i p).2)
  refine ⟨((core S).localTriv i).toOpenPartialHomeomorph.symm (p.proj, g), ?_⟩
  rw [D.totalMap_symm i p.proj g hi, hg]
  exact ((core T).localTriv i).symm_apply_mk_proj (mem_domain_indexAt T p.proj)

/-- The actual core bundle map is continuous in the original glued topologies, derived from its local homomorphism expression. -/
theorem continuous_totalMap : Continuous D.totalMap := by
  apply continuous_iff_continuousAt.mpr
  intro p
  let i := indexAt S p.proj
  have hi := mem_domain_indexAt S p.proj
  apply ((core T).localTriv i).continuousAt_of_comp_left
  · exact (core S).continuous_proj.continuousAt
  · exact (D.mem_domain_iff i p.proj).mp hi
  · have ht := ((core S).localTriv i).toOpenPartialHomeomorph.continuousAt hi
    have hh := ht.fst.prodMk (D.smooth_hom.continuous.continuousAt.comp ht.snd)
    apply hh.congr_of_eventuallyEq
    filter_upwards [(core S).continuous_proj.continuousAt.preimage_mem_nhds
      ((S.domain i).isOpen.mem_nhds hi)] with q hq
    exact D.localTriv_totalMap i q hq

variable [IsManifold I n B]

/-- The genuine principal bundle map is smooth for the independently constructed source and target cocycle atlases. -/
theorem contMDiff_totalMap : ContMDiff (I.prod J) (I.prod K) n D.totalMap := by
  intro p
  let i := indexAt S p.proj
  have hi := mem_domain_indexAt S p.proj
  apply (SmoothCocycleBundle.contMDiffAt_iff_localTriv I K (core T)
    (contMDiffOn_change T) i ((D.mem_domain_iff i p.proj).mp hi)).mpr
  have ht := SmoothCocycleBundle.contMDiffAt_localTriv I J (core S)
    (contMDiffOn_change S) i p hi
  have hh := ht.fst.prodMk (D.smooth_hom.contMDiffAt.comp p ht.snd)
  apply hh.congr_of_eventuallyEq
  filter_upwards [(core S).continuous_proj.continuousAt.preimage_mem_nhds
    ((S.domain i).isOpen.mem_nhds hi)] with q hq
  exact D.localTriv_totalMap i q hq

end Data
end FoliationQM.PrincipalCocycleMorphism
