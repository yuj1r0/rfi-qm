module
public import FoliationQM.PrincipalCocycleBundle
public import FoliationQM.GeometricPrincipalSmoothAtlas

/-!
# Reconstructing an independent geometric principal atlas

Source scope: the geometric principal-bundle bridge underlying the Spin-frame
interpretation of v13 `prop:takabayasi`. The original total space, topology,
projection and actual compatible principal trivializations are independently
supplied. Their derived transition functions build a genuine new group-fiber
core with its natural topology. Explicit mutually inverse maps identify this
core with the original geometric total space, preserving base and right action.
Continuity is proved using genuine local coordinate identities, without any
regularity of the pointwise chart-index choice. With independently specified
original total-space charts and smooth genuine trivializations in both directions,
the extracted cocycle is smooth and the same reconstruction is a diffeomorphism
to the independently constructed core atlas.

This reconstructs supplied principal-atlas geometry; it does not assert the
existence of a Spin lift of an arbitrary Lorentz frame bundle.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Function Bundle Topology
open scoped Topology Manifold
namespace FoliationQM.PrincipalAtlasReconstruction

section Topology
variable {B P G : Type*} [TopologicalSpace B] [TopologicalSpace P]
  [TopologicalSpace G] [Group G]
  {proj : P → B} {ι : Type*} (A : GeometricPrincipalAtlas.Data (G := G) proj ι)

/-- A pointwise choice from the independently supplied geometric cover; no regularity is asserted for the chosen index. -/
def indexAt (x : B) : ι := Classical.choose (A.covers x)

/-- The selected genuine principal chart contains the actual base point. -/
theorem mem_baseSet_indexAt (x : B) : x ∈ (A.triv (indexAt A x)).baseSet :=
  Classical.choose_spec (A.covers x)

variable [ContinuousMul G]

/-- The geometric transition functions generate a genuine group-fiber core, independently of the desired reconstruction equivalence. -/
def core : FiberBundleCore ι B G where
  baseSet i := (A.triv i).baseSet
  isOpen_baseSet i := (A.triv i).open_baseSet
  indexAt := indexAt A
  mem_baseSet_at := mem_baseSet_indexAt A
  coordChange i j x g := A.transition i j x * g
  coordChange_self i x hx g := by rw [A.transition_self i x hx, one_mul]
  continuousOn_coordChange i j :=
    ((A.continuousOn_transition i j).comp continuous_fst.continuousOn
      (fun _ hx => hx.1)).mul continuous_snd.continuousOn
  coordChange_comp i j k x hx g := by
    rw [← mul_assoc, A.transition_comp i j k x hx.1.1 hx.1.2 hx.2]

/-- An actual geometric point is recorded in its pointwise selected original principal chart. -/
def toCore (p : P) : (core A).TotalSpace :=
  ⟨proj p, (A.triv (indexAt A (proj p)) p).2⟩

/-- A point of the new core is realized using the original inverse principal chart at its selected base index. -/
def fromCore (q : (core A).TotalSpace) : P :=
  (A.triv (indexAt A q.proj)).toOpenPartialHomeomorph.symm (q.proj, q.2)

/-- Reconstruction into the core preserves the original base point exactly. -/
theorem toCore_proj (p : P) : (toCore A p).proj = proj p := rfl

/-- Realization of the new core preserves its actual base point. -/
theorem fromCore_proj (q : (core A).TotalSpace) : proj (fromCore A q) = q.proj :=
  (A.triv (indexAt A q.proj)).proj_symm_apply' (mem_baseSet_indexAt A q.proj)

/-- Realizing the recorded coordinates of an original geometric point returns that point. -/
theorem fromCore_toCore (p : P) : fromCore A (toCore A p) = p :=
  (A.triv (indexAt A (proj p))).symm_apply_mk_proj
    ((A.triv (indexAt A (proj p))).mem_source.mpr (mem_baseSet_indexAt A (proj p)))

/-- Recording the actual realization of a core point recovers its original selected coordinates. -/
theorem toCore_fromCore (q : (core A).TotalSpace) : toCore A (fromCore A q) = q := by
  apply Bundle.TotalSpace.ext (fromCore_proj A q)
  apply heq_of_eq
  change (A.triv (indexAt A (proj (fromCore A q))) (fromCore A q)).2 = q.2
  rw [fromCore_proj A q]
  exact congrArg Prod.snd
    ((A.triv (indexAt A q.proj)).apply_symm_apply' (mem_baseSet_indexAt A q.proj))

/-- Every genuine chart of the reconstructed core agrees with the original geometric chart on its true source. -/
theorem localTriv_toCore (i : ι) (p : P) (hp : proj p ∈ (A.triv i).baseSet) :
    (core A).localTriv i (toCore A p) = A.triv i p := by
  apply Prod.ext
  · exact ((A.triv i).coe_fst' hp).symm
  · exact (A.change_coordinate (indexAt A (proj p)) i p
      (mem_baseSet_indexAt A (proj p)) hp).symm

/-- Realization of a reconstructed core point has precisely its original core coordinates in any containing geometric chart. -/
theorem localTriv_fromCore (i : ι) (q : (core A).TotalSpace)
    (hq : q.proj ∈ (A.triv i).baseSet) :
    A.triv i (fromCore A q) = (core A).localTriv i q := by
  have h := localTriv_toCore A i (fromCore A q) (by rw [fromCore_proj A q]; exact hq)
  rw [toCore_fromCore] at h
  exact h.symm

/-- On every containing original chart, realization is its actual inverse trivialization applied to the genuine reconstructed coordinates. -/
theorem fromCore_eq_symm (i : ι) (q : (core A).TotalSpace)
    (hq : q.proj ∈ (A.triv i).baseSet) :
    fromCore A q = (A.triv i).toOpenPartialHomeomorph.symm ((core A).localTriv i q) := by
  rw [← localTriv_fromCore A i q hq]
  exact ((A.triv i).left_inv ((A.triv i).mem_source.mpr
    (by rw [fromCore_proj A q]; exact hq))).symm

/-- The reconstruction map is continuous in the independent original and genuine core-generated topologies, by its exact local coordinate identity. -/
theorem continuous_toCore : Continuous (toCore A) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  let i := indexAt A (proj p)
  have hp := mem_baseSet_indexAt A (proj p)
  apply ((core A).localTriv i).continuousAt_of_comp_left (f := toCore A)
    A.continuous_proj.continuousAt hp
  have ht := (A.triv i).toOpenPartialHomeomorph.continuousAt
    ((A.triv i).mem_source.mpr hp)
  apply ht.congr_of_eventuallyEq
  filter_upwards [A.continuous_proj.continuousAt.preimage_mem_nhds
    ((A.triv i).open_baseSet.mem_nhds hp)] with p' hp'
  exact localTriv_toCore A i p' hp'

/-- Realization from the genuine reconstructed core is continuous in the independent original total-space topology, without a continuous index selection. -/
theorem continuous_fromCore : Continuous (fromCore A) := by
  apply continuous_iff_continuousAt.mpr
  intro q
  let i := indexAt A q.proj
  have hq := mem_baseSet_indexAt A q.proj
  have hb : ContinuousAt (proj ∘ fromCore A) q := by
    convert (core A).continuous_proj.continuousAt using 1
    exact funext (fromCore_proj A)
  apply (A.triv i).continuousAt_of_comp_left hb (by rw [fromCore_proj A q]; exact hq)
  have ht := ((core A).localTriv i).toOpenPartialHomeomorph.continuousAt hq
  apply ht.congr_of_eventuallyEq
  filter_upwards [(core A).continuous_proj.continuousAt.preimage_mem_nhds
    ((A.triv i).open_baseSet.mem_nhds hq)] with q' hq'
  exact localTriv_fromCore A i q' hq'

/-- An independently topologized geometric principal atlas is genuinely homeomorphic to the natural core generated by its actual extracted transitions. -/
def reconstructionHomeomorph : P ≃ₜ (core A).TotalSpace where
  toFun := toCore A
  invFun := fromCore A
  left_inv := fromCore_toCore A
  right_inv := toCore_fromCore A
  continuous_toFun := continuous_toCore A
  continuous_invFun := continuous_fromCore A

/-- The reconstruction homeomorphism has the literal independently defined selected-coordinate forward map. -/
theorem reconstructionHomeomorph_apply (p : P) :
    reconstructionHomeomorph A p = toCore A p := rfl

/-- The inverse reconstruction homeomorphism is the literal original inverse principal trivialization. -/
theorem reconstructionHomeomorph_symm_apply (q : (core A).TotalSpace) :
    (reconstructionHomeomorph A).symm q = fromCore A q := rfl

/-- Reconstruction intertwines the original geometric right action with literal right multiplication in the reconstructed selected group coordinate. -/
theorem toCore_right (p : P) (g : G) :
    toCore A (A.right p g) =
      (⟨proj p, (A.triv (indexAt A (proj p)) p).2 * g⟩ : (core A).TotalSpace) := by
  unfold toCore
  rw [A.proj_right]
  exact congrArg (fun v : G => (⟨proj p, v⟩ : (core A).TotalSpace))
    (A.right_local (indexAt A (proj p)) p g (mem_baseSet_indexAt A (proj p)))

/-- The selected group coordinate in the reconstructed core, without a continuity claim. -/
def fiberValue (q : (core A).TotalSpace) : G := q.2

/-- Realization intertwines literal right multiplication of a reconstructed group coordinate with the original actual geometric right action. -/
theorem fromCore_right (q : (core A).TotalSpace) (g : G) :
    fromCore A (⟨q.proj, fiberValue A q * g⟩ : (core A).TotalSpace) =
      A.right (fromCore A q) g := by
  apply (reconstructionHomeomorph A).injective
  change toCore A (fromCore A _) = toCore A (A.right (fromCore A q) g)
  rw [toCore_fromCore, toCore_right, fromCore_proj A q]
  have h := congrArg (fun q : (core A).TotalSpace => (q.2 : G)) (toCore_fromCore A q)
  change (A.triv (indexAt A (proj (fromCore A q))) (fromCore A q)).2 = q.2 at h
  rw [fromCore_proj A q] at h
  change _ = (⟨q.proj, (A.triv (indexAt A q.proj) (fromCore A q)).2 * g⟩ : (core A).TotalSpace)
  rw [h]
  rfl

end Topology

section Smooth
variable {EB EG EP HB HG HP B G P : Type*}
  [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [NormedAddCommGroup EP] [NormedSpace ℝ EP]
  [TopologicalSpace HB] [TopologicalSpace HG] [TopologicalSpace HP]
  [TopologicalSpace B] [ChartedSpace HB B]
  [TopologicalSpace G] [ChartedSpace HG G] [Group G]
  [TopologicalSpace P] [ChartedSpace HP P]
  {I : ModelWithCorners ℝ EB HB} {J : ModelWithCorners ℝ EG HG}
  {K : ModelWithCorners ℝ EP HP} {proj : P → B} {ι : Type*}
  {A : GeometricPrincipalAtlas.Data (G := G) proj ι} {n : WithTop ℕ∞}
  (S : GeometricPrincipalSmoothAtlas.Data I J K A n)

/-- Smooth transitions are extracted from the original independent geometric charts and their actual unit sections, with no desired reconstruction theorem as a premise. -/
def cocycleData : PrincipalCocycleBundle.Data I J B G ι n where
  domain i := ⟨(A.triv i).baseSet, (A.triv i).open_baseSet⟩
  covers := A.covers
  transition := A.transition
  smooth_transition := S.contMDiffOn_transition
  identity := A.transition_self
  comp := A.transition_comp

/-- The extracted smooth cocycle retains exactly the original actual geometric chart domains. -/
theorem cocycleData_domain (i : ι) :
    ((cocycleData S).domain i : Set B) = (A.triv i).baseSet := rfl

/-- The extracted smooth cocycle has the literal geometric transition value, defined by original unit sections and trivializations. -/
theorem cocycleData_transition (i j : ι) (x : B) :
    (cocycleData S).transition i j x = A.transition i j x := rfl

variable [ContMDiffMul J n G] [ContinuousMul G]

/-- The independently constructed topological reconstruction core is exactly the genuine principal core of the extracted smooth cocycle. -/
theorem core_eq_cocycleCore : core A = PrincipalCocycleBundle.core (cocycleData S) := rfl

/-- The topological reconstruction core locally uses the same explicit base/group product atlas as its definitionally equal smooth principal core. -/
local instance instChartedSpaceReconstruction : ChartedSpace (ModelProd HB HG) (core A).TotalSpace :=
  SmoothCocycleBundle.totalChartedSpace HB HG (core A)

variable [IsManifold I n B]
include S

/-- Reconstruction is smooth from the independently supplied original total atlas into the genuine product-charted principal core, by the actual local-coordinate identity. -/
theorem contMDiff_toCore :
    ContMDiff K (I.prod J) n
      (toCore A : P → PrincipalCocycleBundle.Total (cocycleData S)) := by
  intro p
  let i := indexAt A (proj p)
  have hp := mem_baseSet_indexAt A (proj p)
  apply (SmoothCocycleBundle.contMDiffAt_iff_localTriv I J
    (PrincipalCocycleBundle.core (cocycleData S))
    (PrincipalCocycleBundle.contMDiffOn_change (cocycleData S))
    (f := toCore A) (x := p) i hp).mpr
  apply (S.contMDiffAt_triv i p hp).congr_of_eventuallyEq
  filter_upwards [A.continuous_proj.continuousAt.preimage_mem_nhds
    ((A.triv i).open_baseSet.mem_nhds hp)] with p' hp'
  exact localTriv_toCore A i p' hp'

/-- The same literal inverse realization is smooth into the independently supplied original total atlas, using actual local inverse principal charts. -/
theorem contMDiff_fromCore :
    ContMDiff (I.prod J) K n
      (fromCore A : PrincipalCocycleBundle.Total (cocycleData S) → P) := by
  intro q
  let i := indexAt A q.proj
  have hq := mem_baseSet_indexAt A q.proj
  have ht := SmoothCocycleBundle.contMDiffAt_localTriv I J
    (PrincipalCocycleBundle.core (cocycleData S))
    (PrincipalCocycleBundle.contMDiffOn_change (cocycleData S)) i q hq
  have hs := (S.contMDiffAt_symm i ((core A).localTriv i q) hq).comp q ht
  apply hs.congr_of_eventuallyEq
  filter_upwards [(core A).continuous_proj.continuousAt.preimage_mem_nhds
    ((A.triv i).open_baseSet.mem_nhds hq)] with q' hq'
  exact fromCore_eq_symm A i q' hq'

omit [ContinuousMul G] in
/-- An independent smooth geometric principal atlas is genuinely diffeomorphic to the principal core constructed from its actual extracted smooth transition cocycle; continuity of group multiplication is derived internally from its smoothness. -/
def reconstructionDiffeomorph :
    P ≃ₘ^n⟮K, I.prod J⟯ PrincipalCocycleBundle.Total (cocycleData S) := by
  letI : ContinuousMul G := continuousMul_of_contMDiffMul J n
  exact
    { toEquiv := (reconstructionHomeomorph A).toEquiv
      contMDiff_toFun := contMDiff_toCore S
      contMDiff_invFun := contMDiff_fromCore S }

/-- Smooth reconstruction retains exactly the previously proved natural-topology reconstruction homeomorphism. -/
theorem reconstructionDiffeomorph_toHomeomorph :
    (reconstructionDiffeomorph S).toHomeomorph = reconstructionHomeomorph A := rfl

/-- The smooth reconstruction has the same actual selected-coordinate forward map as the original topological construction. -/
theorem reconstructionDiffeomorph_apply (p : P) :
    reconstructionDiffeomorph S p = toCore A p := rfl

/-- The inverse smooth reconstruction uses the actual original inverse trivialization, without transporting the original atlas. -/
theorem reconstructionDiffeomorph_symm_apply (q : PrincipalCocycleBundle.Total (cocycleData S)) :
    (reconstructionDiffeomorph S).symm q = fromCore A q := rfl

omit [ContinuousMul G] in
/-- The actual reconstruction diffeomorphism preserves the independently given original bundle projection. -/
theorem reconstructionDiffeomorph_proj (p : P) :
    (reconstructionDiffeomorph S p).proj = proj p := rfl

omit [ContinuousMul G] in
/-- Smooth reconstruction intertwines the original geometric principal action and the previously constructed literal principal-core right action. -/
theorem reconstructionDiffeomorph_right (p : P) (g : G) :
    reconstructionDiffeomorph S (A.right p g) =
      PrincipalCocycleBundle.rightAct (cocycleData S) (reconstructionDiffeomorph S p) g := by
  let : ContinuousMul G := continuousMul_of_contMDiffMul J n
  exact toCore_right A p g

omit [ContinuousMul G] in
/-- In every containing chart, smooth reconstruction preserves the exact original geometric principal coordinates. -/
theorem reconstructionDiffeomorph_localTriv (i : ι) (p : P)
    (hp : proj p ∈ (A.triv i).baseSet) :
    (PrincipalCocycleBundle.core (cocycleData S)).localTriv i (reconstructionDiffeomorph S p) =
      A.triv i p := by
  let : ContinuousMul G := continuousMul_of_contMDiffMul J n
  exact localTriv_toCore A i p hp

end Smooth
end FoliationQM.PrincipalAtlasReconstruction
