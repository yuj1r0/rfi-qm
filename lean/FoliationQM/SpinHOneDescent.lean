module
public import FoliationQM.SpinHOneRestriction
public import FoliationQM.PuncturedPlaneSpinSign

/-!
# Descent of smooth chart signs along an open refinement

Source scope: the global Spin-frame component of v13 `prop:takabayasi`.
A chart gauge trivializing a restricted one-cocycle determines chart
signs on the original cover. On each intersection with a refined open
the sign has a smooth formula using a single parent transition and the
refined chart gauge. The original cocycle law makes these formulas agree.
-/

@[expose] public section
noncomputable section
open Set Topology
open scoped Manifold
namespace FoliationQM.SpinHOneDescent
open CliffordSpinSignKernel CliffordSpinCoverRefinement SpinSignOneCocycle SpinSignHOne

variable {E H B ι κ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace B] [ChartedSpace H B] {U : ι → TopologicalSpace.Opens B} {n : WithTop ℕ∞}
  (R : Refinement U κ) (z : Cocycle I U n) (b : ZeroCochain I R.domain n)

/-- On a refined pair, the original sign between the parents is the ratio of the two refined chart signs. -/
def Matches : Prop :=
  ∀ a d x, x ∈ R.domain a → x ∈ R.domain d →
    z.val.value (R.parent a) (R.parent d) x = b.value d x * (b.value a x)⁻¹

/-- Transport the refined chart sign through its parent transition into an original chart. -/
def descendedValue (i : ι) (x : B) : Kernel :=
  let a := Classical.choose (R.covers x)
  z.val.value (R.parent a) i x * b.value a x

/-- Any refined chart containing the point gives the same transported sign on the original chart. -/
theorem descendedValue_local (h : Matches R z b) (i : ι) (a : κ) (x : B)
    (hi : x ∈ U i) (ha : x ∈ R.domain a) :
    descendedValue R z b i x = z.val.value (R.parent a) i x * b.value a x := by
  let c := Classical.choose (R.covers x)
  have hc : x ∈ R.domain c := Classical.choose_spec (R.covers x)
  change z.val.value (R.parent c) i x * b.value c x = _
  rw [← z.property (R.parent c) (R.parent a) i x (R.subset c hc) (R.subset a ha) hi,
    h c a x hc ha]
  simp only [mul_assoc, inv_mul_cancel, mul_one]

/-- The transported signs are smooth on each original chart by their fixed-chart formula on its open intersections. -/
def descended (h : Matches R z b) : ZeroCochain I U n where
  value := descendedValue R z b
  smooth_value i := by
    intro x hx
    obtain ⟨a, ha⟩ := R.covers x
    have hpair := (z.val.smooth_value (R.parent a) i).contMDiffAt
      (((U (R.parent a)).isOpen.inter (U i).isOpen).mem_nhds ⟨R.subset a ha, hx⟩)
    have hchart := (b.smooth_value a).contMDiffAt ((R.domain a).isOpen.mem_nhds ha)
    apply ContMDiffAt.contMDiffWithinAt
    apply ((CliffordSpinManifold.contMDiff_mul n).contMDiffAt.comp x
      (hpair.prodMk hchart)).congr_of_eventuallyEq
    filter_upwards [(U i).isOpen.mem_nhds hx, (R.domain a).isOpen.mem_nhds ha] with y hy hya
    exact congrArg Subtype.val (descendedValue_local R z b h i a y hy hya)

/-- On each original pair overlap the descended chart coboundary recovers the given cocycle. -/
theorem overlapEq_coboundary_descended (h : Matches R z b) :
    OverlapEq z (coboundary (descended R z b h)) := by
  intro i j x hi hj
  obtain ⟨a, ha⟩ := R.covers x
  change z.val.value i j x = descendedValue R z b j x * (descendedValue R z b i x)⁻¹
  apply eq_mul_inv_iff_mul_eq.mpr
  rw [descendedValue_local R z b h i a x hi ha, descendedValue_local R z b h j a x hj ha,
    ← mul_assoc, z.property (R.parent a) i j x (R.subset a ha) hi hj]

open SpinHOneRestriction

/-- Restriction to any open refinement reflects as well as preserves neutrality of degree-one sign classes. -/
theorem restrictHom_eq_one_iff (c : H1 I U n) : restrictHom R c = 1 ↔ c = 1 := by
  constructor
  · intro h
    obtain ⟨w, rfl⟩ := classOf_surjective c
    rw [restrictHom_classOf] at h
    obtain ⟨t, ht⟩ := (classOf_eq_one_iff _).mp h
    exact (classOf_eq_one_iff w).mpr
      ⟨descended R w t ht, overlapEq_coboundary_descended R w t ht⟩
  · rintro rfl
    exact map_one _

/-- The restriction homomorphism embeds the original fixed-cover first sign cohomology in that of every open refinement. -/
theorem restrictHom_injective : Function.Injective (restrictHom (I := I) (n := n) R) :=
  (injective_iff_map_eq_one _).mpr (fun c => (restrictHom_eq_one_iff R c).mp)

/-- Two original degree-one classes become equal under a specified refinement exactly when they were already equal. -/
theorem restrictHom_eq_iff (c d : H1 I U n) :
    restrictHom R c = restrictHom R d ↔ c = d :=
  (restrictHom_injective R).eq_iff

/-- The concrete nonneutral sign around the three punctured-plane charts survives every open refinement. -/
theorem puncturedPlane_nontrivial (n : WithTop ℕ∞) (R : Refinement PuncturedPlaneSignCover.domains κ) :
    restrictHom R (classOf (PuncturedPlaneSpinSign.cocycle n)) ≠ 1 :=
  fun h => PuncturedPlaneSpinSign.class_ne_one n ((restrictHom_eq_one_iff R _).mp h)

end FoliationQM.SpinHOneDescent
