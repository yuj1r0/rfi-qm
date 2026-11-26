module
public import FoliationQM.SmoothCocycleBundle
public import FoliationQM.GeometricPrincipalAtlas
public import Mathlib.Geometry.Manifold.Algebra.LieGroup

/-!
# Genuine principal group bundles from smooth transition cocycles

Source scope: principal-bundle infrastructure for the geometric Spin
interpretation underlying v13 `prop:takabayasi`. Supplied smooth group
transitions act by literal left multiplication in group fibers. Their
actual FiberBundleCore generates the total topology; genuine local
trivializations followed by independently specified base/group charts
generate its smooth atlas.

Right multiplication in the selected fiber coordinates commutes with
every left transition. Its actual local-coordinate formula proves joint
continuity and smoothness without any regularity of chart-index choice.
Identity, composition, freeness and unique transitivity on each fiber
are derived from the group law, not supplied as bundle conclusions.
No tangent-frame identification, geometric Spin lift of arbitrary
Lorentz data, or spacetime Spin-structure existence is asserted here.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Function Bundle Topology
open scoped Manifold
namespace FoliationQM.PrincipalCocycleBundle

variable {E E' H H' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H] [TopologicalSpace H']
  (I : ModelWithCorners ℝ E H) (J : ModelWithCorners ℝ E' H')
  (B G : Type*) [TopologicalSpace B] [ChartedSpace H B]
  [Group G] [TopologicalSpace G] [ChartedSpace H' G]

/-- Independently supplied smooth group-valued transition cocycles on an actual open cover, in chart i to chart j order. -/
structure Data (ι : Type*) (n : WithTop ℕ∞) where
  /-- The original open chart domains. -/
  domain : ι → TopologicalSpace.Opens B
  /-- These domains cover the base. -/
  covers : ∀ x : B, ∃ i, x ∈ domain i
  /-- The actual group transition from chart i coordinates to chart j coordinates. -/
  transition : ι → ι → B → G
  /-- Only the genuine pair overlap is required to carry smooth transitions. -/
  smooth_transition : ∀ i j, ContMDiffOn I J n (transition i j)
    ((domain i : Set B) ∩ (domain j : Set B))
  /-- Self-transitions equal the group unit on their chart. -/
  identity : ∀ i x, x ∈ domain i → transition i i x = 1
  /-- The ordered cocycle equation holds on actual triple overlaps. -/
  comp : ∀ i j k x, x ∈ domain i → x ∈ domain j → x ∈ domain k →
    transition j k x * transition i j x = transition i k x

variable {I J B G} {ι : Type*} {n : WithTop ℕ∞} (D : Data I J B G ι n)

/-- A pointwise chart choice from the supplied cover, with no continuity premise or conclusion. -/
def indexAt (x : B) : ι := Classical.choose (D.covers x)

/-- The chosen chart contains the actual base point. -/
theorem mem_domain_indexAt (x : B) : x ∈ D.domain (indexAt D x) :=
  Classical.choose_spec (D.covers x)

/-- The actual group-fiber coordinate change is literal left multiplication by the supplied transition. -/
def change (i j : ι) (x : B) (g : G) : G := D.transition i j x * g

/-- A self-coordinate change fixes the actual group fiber on its chart. -/
theorem change_self (i : ι) (x : B) (hx : x ∈ D.domain i) (g : G) :
    change D i i x g = g := by
  rw [change, D.identity i x hx, one_mul]

/-- Actual left-multiplication coordinate changes compose in the given chart order on triple overlaps. -/
theorem change_comp (i j k : ι) (x : B)
    (hi : x ∈ D.domain i) (hj : x ∈ D.domain j) (hk : x ∈ D.domain k) (g : G) :
    change D j k x (change D i j x g) = change D i k x g := by
  simp only [change, ← mul_assoc, D.comp i j k x hi hj hk]

variable [ContMDiffMul J n G]

/-- The actual group-fiber changes are jointly smooth on precisely the original overlap times the entire group fiber. -/
theorem contMDiffOn_change (i j : ι) :
    ContMDiffOn (I.prod J) J n (fun p : B × G => change D i j p.1 p.2)
      (((D.domain i : Set B) ∩ (D.domain j : Set B)) ×ˢ univ) := by
  have ht : ContMDiffOn (I.prod J) J n (fun p : B × G => D.transition i j p.1)
      (((D.domain i : Set B) ∩ (D.domain j : Set B)) ×ˢ univ) :=
    (D.smooth_transition i j).comp contMDiff_fst.contMDiffOn (fun _ hx => hx.1)
  exact (contMDiff_mul J n).comp_contMDiffOn (ht.prodMk contMDiff_snd.contMDiffOn)

/-- The actual group-fiber core is constructed directly from the independently supplied transitions and their proved left-multiplication changes. -/
def core : FiberBundleCore ι B G where
  baseSet i := D.domain i
  isOpen_baseSet i := (D.domain i).isOpen
  indexAt := indexAt D
  mem_baseSet_at := mem_domain_indexAt D
  coordChange := change D
  coordChange_self := change_self D
  continuousOn_coordChange i j := (contMDiffOn_change D i j).continuousOn
  coordChange_comp i j k x hx g := change_comp D i j k x hx.1.1 hx.1.2 hx.2 g

/-- The principal cocycle total space carries its original core-generated topology. -/
abbrev Total := (core D).TotalSpace

/-- The group-fiber atlas uses genuine core trivializations followed by the independently specified product charts. -/
instance instChartedSpaceTotal : ChartedSpace (ModelProd H H') (Total D) :=
  SmoothCocycleBundle.totalChartedSpace H H' (core D)

/-- The actual group coordinate in the core's pointwise selected chart; no global continuity is asserted for this coordinate. -/
def fiberValue (p : Total D) : G := p.2

/-- The actual principal right action is right multiplication in the core's selected group coordinate. -/
def rightAct (p : Total D) (g : G) : Total D := ⟨p.proj, fiberValue D p * g⟩

/-- The genuine principal right action preserves the actual base point. -/
theorem rightAct_proj (p : Total D) (g : G) : (rightAct D p g).proj = p.proj := rfl

/-- In every genuine local trivialization the principal right action is ordinary right multiplication of the group coordinate. -/
theorem localTriv_rightAct (i : ι) (p : Total D) (g : G) :
    (core D).localTriv i (rightAct D p g) =
      (p.proj, ((core D).localTriv i p).2 * g) := by
  apply Prod.ext
  · rfl
  · exact (mul_assoc (D.transition (indexAt D p.proj) i p.proj) (fiberValue D p) g).symm

/-- The group unit fixes every actual total-space point. -/
@[simp] theorem rightAct_one (p : Total D) : rightAct D p 1 = p := by
  cases p
  simp only [rightAct, mul_one, fiberValue]

/-- The actual principal right action satisfies its correctly ordered composition law. -/
theorem rightAct_mul (p : Total D) (g h : G) :
    rightAct D (rightAct D p g) h = rightAct D p (g * h) := by
  cases p with
  | mk x v =>
    change G at v
    exact congrArg (fun w : G => (⟨x, w⟩ : Total D)) (mul_assoc (v : G) g h)

/-- The actual right action is free at every total-space point, as a consequence of genuine group cancellation. -/
theorem rightAct_injective (p : Total D) : Injective (rightAct D p) := by
  intro g h he
  have he' : fiberValue D p * g = fiberValue D p * h :=
    congrArg (fiberValue D) he
  exact mul_left_cancel he'

/-- Any two actual points of the same bundle fiber differ by exactly one right group element. -/
theorem existsUnique_rightAct (p q : Total D) (hpq : p.proj = q.proj) :
    ∃! g : G, rightAct D p g = q := by
  cases p with
  | mk x v =>
    cases q with
    | mk y w =>
      cases hpq
      change G at v w
      refine ⟨(v : G)⁻¹ * (w : G), ?_, ?_⟩
      · simp only [rightAct, fiberValue, mul_inv_cancel_left]
      · intro g hg
        have he := congrArg (fiberValue D) hg
        exact mul_left_cancel (he.trans (mul_inv_cancel_left (v : G) (w : G)).symm)

/-- The original core projection is continuous in the actual glued topology. -/
theorem continuous_proj : Continuous (core D).proj := (core D).continuous_proj

/-- The actual principal right action is jointly continuous, derived in genuine local trivializations without a continuous chart-index choice. -/
theorem continuous_rightAct : Continuous (fun p : Total D × G => rightAct D p.1 p.2) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  let i := indexAt D p.1.proj
  have hp : p.1 ∈ ((core D).localTriv i).source := mem_domain_indexAt D p.1.proj
  apply ((core D).localTriv i).continuousAt_of_comp_left
  · exact ((core D).continuous_proj.comp continuous_fst).continuousAt
  · exact hp
  · have ht := ((core D).localTriv i).toOpenPartialHomeomorph.continuousAt hp
    have ht' := ht.comp continuousAt_fst
    have hm := (contMDiff_mul J n).continuous.continuousAt.comp
      (ht'.snd.prodMk continuousAt_snd)
    convert ht'.fst.prodMk hm using 1
    exact funext (fun q => localTriv_rightAct D i q.1 q.2)

/-- The genuine cocycle bundle supplies independently defined geometric principal-atlas data through its actual trivializations and derived local right-action formula. -/
def geometricData : GeometricPrincipalAtlas.Data (G := G) (core D).proj ι where
  triv := (core D).localTriv
  covers := D.covers
  right := rightAct D
  proj_right := rightAct_proj D
  right_local i p g _ := congrArg Prod.snd (localTriv_rightAct D i p g)

/-- The constructed geometric principal atlas uses exactly the original genuine core trivialization. -/
theorem geometricData_triv (i : ι) : (geometricData D).triv i = (core D).localTriv i := rfl

/-- The constructed geometric right operation is exactly the independently proved actual core right multiplication. -/
theorem geometricData_right (p : Total D) (g : G) :
    (geometricData D).right p g = rightAct D p g := rfl

/-- Extracting transition values geometrically from the constructed independent principal atlas recovers precisely the original supplied group cocycle on every true overlap. -/
theorem geometricData_transition (i j : ι) (x : B)
    (hi : x ∈ D.domain i) (hj : x ∈ D.domain j) :
    (geometricData D).transition i j x = D.transition i j x := by
  change D.transition (indexAt D x) j x * (D.transition i (indexAt D x) x * 1) = _
  simpa only [mul_one] using D.comp i (indexAt D x) j x hi (mem_domain_indexAt D x) hj

variable [IsManifold I n B]

/-- The explicit core-generated atlas is a manifold of the stated order, by the proved actual transition regularity. -/
instance instIsManifoldTotal : IsManifold (I.prod J) n (Total D) :=
  SmoothCocycleBundle.isManifold_total I J (core D) (contMDiffOn_change D)

/-- The original core trivialization is smooth on its actual source in the independently constructed total-space atlas. -/
theorem contMDiffOn_localTriv (i : ι) :
    ContMDiffOn (I.prod J) (I.prod J) n ((core D).localTriv i)
      ((core D).localTriv i).source :=
  SmoothCocycleBundle.contMDiffOn_localTriv I J (core D) (contMDiffOn_change D) i

/-- The original inverse core trivialization is smooth on its actual base/group target. -/
theorem contMDiffOn_localTriv_symm (i : ι) :
    ContMDiffOn (I.prod J) (I.prod J) n ((core D).localTriv i).toOpenPartialHomeomorph.symm
      ((core D).localTriv i).target :=
  SmoothCocycleBundle.contMDiffOn_localTriv_symm I J (core D) (contMDiffOn_change D) i

/-- The genuine core projection is smooth for the independently constructed product atlas. -/
theorem contMDiff_proj : ContMDiff (I.prod J) I n (core D).proj :=
  SmoothCocycleBundle.contMDiff_proj I J (core D) (contMDiffOn_change D)

/-- The actual principal right action is jointly smooth, proved using its real group-multiplication expression in each genuine bundle chart. -/
theorem contMDiff_rightAct :
    ContMDiff ((I.prod J).prod J) (I.prod J) n
      (fun p : Total D × G => rightAct D p.1 p.2) := by
  intro p
  let i := indexAt D p.1.proj
  have hp : p.1 ∈ ((core D).localTriv i).source := mem_domain_indexAt D p.1.proj
  apply (SmoothCocycleBundle.contMDiffAt_iff_localTriv I J (core D)
    (contMDiffOn_change D) (f := fun q : Total D × G => rightAct D q.1 q.2) (x := p)
    i (show rightAct D p.1 p.2 ∈ ((core D).localTriv i).source from hp)).mpr
  have ht := (SmoothCocycleBundle.contMDiffAt_localTriv I J (core D)
    (contMDiffOn_change D) i p.1 hp).comp p
      (contMDiff_fst : ContMDiff ((I.prod J).prod J) (I.prod J) n
        (Prod.fst : Total D × G → Total D)).contMDiffAt
  have hs : ContMDiffAt ((I.prod J).prod J) J n (Prod.snd : Total D × G → G) p :=
    contMDiff_snd.contMDiffAt
  have hm := (contMDiff_mul J n).contMDiffAt.comp p (ht.snd.prodMk hs)
  apply (ht.fst.prodMk hm).congr_of_eventuallyEq
  exact Filter.Eventually.of_forall (fun q => localTriv_rightAct D i q.1 q.2)

end FoliationQM.PrincipalCocycleBundle
