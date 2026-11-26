module
public import FoliationQM.PrincipalAtlasCrossGauge
public import FoliationQM.ModTwoPullback

/-!
# Pulling back a geometric principal atlas

For the frame bundle in v13 `prop:takabayasi`, pulling back along a continuous
base map gives the fiber product with its subspace topology. The local
coordinates keep the new base point and read the original group coordinate.
The inverse chart uses the original inverse chart over each preimage open.
-/

@[expose] public section
noncomputable section
open Set Bundle
namespace FoliationQM.GeometricPrincipalPullback

variable {X B T G ι : Type*} [TopologicalSpace X] [TopologicalSpace B]
  (f : C(X, B))

/-- The fiber product of the base map and the original bundle projection. -/
abbrev Total (proj : T → B) := {z : X × T // f z.1 = proj z.2}

/-- The fiber-product projection to the new base. -/
def projection (proj : T → B) (p : Total f proj) : X := p.val.1

/-- The map from the fiber product to the original total space. -/
def toOriginal (proj : T → B) (p : Total f proj) : T := p.val.2

variable {proj : T → B}

/-- The two projections give the same point of the original base. -/
theorem commutes (p : Total f proj) : f (projection f proj p) = proj (toOriginal f proj p) :=
  p.property

/-- The fiber product maps continuously to its new base. -/
theorem continuous_projection [TopologicalSpace T] : Continuous (projection f proj) :=
  continuous_fst.comp continuous_subtype_val

/-- The map to the original total space is continuous for the fiber-product topology. -/
theorem continuous_toOriginal [TopologicalSpace T] : Continuous (toOriginal f proj) :=
  continuous_snd.comp continuous_subtype_val

/-- Lift a base-preserving right operation to the fiber product, keeping its new base point. -/
def right (act : T → G → T) (hact : ∀ p g, proj (act p g) = proj p)
    (p : Total f proj) (g : G) : Total f proj :=
  ⟨(p.val.1, act p.val.2 g), p.property.trans (hact p.val.2 g).symm⟩

/-- The induced operation is equivariant over the original total space. -/
theorem toOriginal_right (act : T → G → T) (hact : ∀ p g, proj (act p g) = proj p)
    (p : Total f proj) (g : G) :
    toOriginal f proj (right f act hact p g) = act (toOriginal f proj p) g := rfl

variable [TopologicalSpace T] [TopologicalSpace G] [Group G]
  (A : GeometricPrincipalAtlas.Data (G := G) proj ι)

/-- Over its chart open the inverse reconstructs the original point in the prescribed fiber. -/
def inverseChart (i : ι) (z : X × G) : Total f proj := by
  classical
  by_cases h : f z.1 ∈ (A.triv i).baseSet
  · exact ⟨(z.1, (A.triv i).toOpenPartialHomeomorph.symm (f z.1, z.2)),
      ((A.triv i).proj_symm_apply' h).symm⟩
  · exact ⟨(z.1, (A.proj_surjective (f z.1)).choose), (A.proj_surjective (f z.1)).choose_spec.symm⟩

/-- On the true target, the inverse is the original inverse chart at the image base point. -/
theorem inverseChart_val (i : ι) (z : X × G) (hz : f z.1 ∈ (A.triv i).baseSet) :
    (inverseChart f A i z).val = (z.1, (A.triv i).toOpenPartialHomeomorph.symm (f z.1, z.2)) := by
  classical
  simp [inverseChart, hz]

/-- The original principal chart induces a genuine trivialization on its preimage open. -/
def trivialization (i : ι) : Trivialization G (projection f proj) := by
  let e := A.triv i
  let U : Set X := f ⁻¹' e.baseSet
  have hU : IsOpen U := e.open_baseSet.preimage f.continuous
  exact
    { toFun := fun p => (projection f proj p, (e (toOriginal f proj p)).2)
      invFun := inverseChart f A i
      source := projection f proj ⁻¹' U
      target := U ×ˢ univ
      map_source' := fun p hp => ⟨hp, mem_univ _⟩
      map_target' := by
        intro z hz
        change (inverseChart f A i z).val.1 ∈ U
        rw [inverseChart_val f A i z hz.1]
        exact hz.1
      left_inv' := by
        intro p hp
        apply Subtype.ext
        rw [inverseChart_val f A i (projection f proj p, (e (toOriginal f proj p)).2) hp]
        refine Prod.ext ?_ ?_
        · rfl
        · change e.toOpenPartialHomeomorph.symm (f p.val.1, (e p.val.2).2) = p.val.2
          rw [p.property]
          exact e.symm_apply_mk_proj (e.mem_source.mpr (p.property ▸ hp))
      right_inv' := by
        intro z hz
        change ((inverseChart f A i z).val.1, (e (inverseChart f A i z).val.2).2) = z
        rw [inverseChart_val f A i z hz.1]
        exact Prod.ext rfl (congrArg (Prod.snd : B × G → G) (e.apply_symm_apply' (x := z.2) hz.1))
      open_source := hU.preimage (continuous_projection f)
      open_target := hU.prod isOpen_univ
      continuousOn_toFun := by
        apply (continuous_projection f).continuousOn.prodMk
        apply ContinuousOn.snd
        apply e.toOpenPartialHomeomorph.continuousOn.comp (continuous_toOriginal f).continuousOn
        intro p hp
        exact e.mem_source.mpr (p.property ▸ hp)
      continuousOn_invFun := by
        apply Topology.IsEmbedding.subtypeVal.isInducing.continuousOn_iff.mpr
        have hc : Continuous (fun z : X × G => (f z.1, z.2)) :=
          (f.continuous.comp continuous_fst).prodMk continuous_snd
        have ht : ContinuousOn (fun z : X × G => e.toOpenPartialHomeomorph.symm (f z.1, z.2))
            (U ×ˢ univ) := e.toOpenPartialHomeomorph.continuousOn_symm.comp hc.continuousOn
              (fun _ hz => e.mem_target.mpr hz.1)
        exact (continuous_fst.continuousOn.prodMk ht).congr
          (fun z hz => inverseChart_val f A i z hz.1)
      baseSet := U
      open_baseSet := hU
      source_eq := rfl
      target_eq := rfl
      proj_toFun := fun _ _ => rfl }

/-- The actual principal atlas on the fiber-product projection. -/
def atlas : GeometricPrincipalAtlas.Data (G := G) (projection f proj) ι where
  triv := trivialization f A
  covers x := A.covers (f x)
  right := right f A.right A.proj_right
  proj_right _ _ := rfl
  right_local i p g hp := A.right_local i p.val.2 g (p.property ▸ hp)

/-- The pullback atlas uses the lifted original right action. -/
theorem atlas_right : (atlas f A).right = right f A.right A.proj_right := rfl

/-- The extracted pullback opens are exactly the inverse images of the original chart opens. -/
theorem domain_eq :
    (PrincipalAtlasCrossGauge.data (atlas f A)).domain =
      ModTwoPullback.domain f (PrincipalAtlasCrossGauge.data A).domain := rfl

/-- Reading the pulled-back chart keeps the base point and reads the original coordinate. -/
theorem chart_apply (i : ι) (p : Total f proj) :
    (atlas f A).triv i p = (projection f proj p, (A.triv i (toOriginal f proj p)).2) := rfl

/-- Above a chart open, the canonical unit section projects to the original unit section. -/
theorem toOriginal_localSection (i : ι) (x : X) (hx : x ∈ ((atlas f A).triv i).baseSet) :
    toOriginal f proj ((atlas f A).localSection i x) = A.localSection i (f x) :=
  congrArg Prod.snd (inverseChart_val f A i (x, 1) hx)

/-- Actual transitions in the pulled-back charts are the original transitions on each true pair. -/
theorem transition_eq (i j : ι) (x : X)
    (hi : x ∈ ((atlas f A).triv i).baseSet) (_hj : x ∈ ((atlas f A).triv j).baseSet) :
    (atlas f A).transition i j x = A.transition i j (f x) := by
  change (A.triv j (toOriginal f proj ((atlas f A).localSection i x))).2 = _
  rw [toOriginal_localSection f A i x hi]
  rfl

end FoliationQM.GeometricPrincipalPullback
