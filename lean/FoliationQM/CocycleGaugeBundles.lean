module
public import FoliationQM.CocycleGaugeTransform
public import FoliationQM.PolarCocycleManifold

/-!
# Actual smooth cocycle-bundle changes of local frames

Source: the supplied-transition interpretation of v13 `prop:takabayasi`.
A supplied determinant-one matrix change is smooth only on its own open
cover domain. The transformed cocycle has the same cover and actual
transition matrices `h_j G_ij h_i⁻¹`. The old and transformed total spaces
retain their actual core-generated topologies and independently
constructed cocycle-bundle atlases.

The total-space maps are defined directly by actual matrix action in
the selected fiber coordinates, with the actual inverse matrix defining
the reverse maps. Actual transition intertwining proves their precise
local-trivialization formulas in every chart. Those formulas use the
smooth local matrix field belonging to that chart. The genuine local
bundle smoothness criterion proves smoothness of the polar maps. Actual
equivariance identifies the directly defined represented-spinor maps
with compositions of those smooth polar maps and the independently
proved total realization diffeomorphisms, proving their smoothness as
well. No regularity of the pointwise selected index is assumed.

The resulting polar and represented-spinor maps are actual
base-preserving diffeomorphisms, with exact forward and inverse formulas.
Their square with the independently constructed actual polar total-space
realization commutes by the previously proved matrix-action equivariance.
These are supplied concrete changes of bundle coordinates; no abstract
Spin classification, global individual polar representative, or covariance
of a differentiated field equation is asserted.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Matrix.Norms.Operator Manifold
open Set Topology
namespace FoliationQM.CocycleGaugeBundles
open DiracMatrices PolarSignQuotient PolarTransitionCocycle PolarCocycleBundles
open PolarCocycleManifold CocycleGaugeTransform

section Generic
variable {B F ι : Type*} [TopologicalSpace B] [TopologicalSpace F]
private theorem localTriv_frameMap (Z W : FiberBundleCore ι B F)
    (a : ι → B → F → F) (hind : W.indexAt = Z.indexAt)
    (ha : ∀ i j x v, W.coordChange i j x (a i x v) = a j x (Z.coordChange i j x v))
    (i : ι) (p : Z.TotalSpace) :
    W.localTriv i (⟨p.proj, a (Z.indexAt p.proj) p.proj p.2⟩ : W.TotalSpace) =
      (p.proj, a i p.proj (Z.localTriv i p).2) := by
  simp only [FiberBundleCore.localTriv_apply, hind]
  exact congrArg (Prod.mk p.proj) (ha (Z.indexAt p.proj) i p.proj p.2)
end Generic

variable {E H B ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace B] [ChartedSpace H B] {n : WithTop ℕ∞}
  (D : Data I B ι n) (h : FrameChange D)

/-- The actual polar total-space frame change acts in the selected fiber coordinates by the supplied local matrix at the same base point. -/
def polarMap (p : PolarTotal D) : PolarTotal (transformed D h) :=
  ⟨p.proj, DensityFrameAction.productAction (h.value (indexAt D p.proj) p.proj) p.2⟩

/-- The actual inverse polar total-space change uses the inverse of the same supplied matrix in the same selected coordinates. -/
def polarInvMap (p : PolarTotal (transformed D h)) : PolarTotal D :=
  ⟨p.proj, DensityFrameAction.productAction (h.value (indexAt D p.proj) p.proj)⁻¹ p.2⟩

/-- The actual spinor total-space frame change is the direct represented local matrix action in the selected fiber coordinates. -/
def spinorMap (p : SpinorTotal D) : SpinorTotal (transformed D h) :=
  ⟨p.proj, RegularSpinorAction.act (h.value (indexAt D p.proj) p.proj) p.2⟩

/-- The actual inverse spinor total-space change uses the direct represented inverse matrix in the same selected coordinates. -/
def spinorInvMap (p : SpinorTotal (transformed D h)) : SpinorTotal D :=
  ⟨p.proj, RegularSpinorAction.act (h.value (indexAt D p.proj) p.proj)⁻¹ p.2⟩

/-- Actual inverse matrix action cancels the forward polar total-space frame change. -/
theorem polarInvMap_polarMap (p : PolarTotal D) :
    polarInvMap D h (polarMap D h p) = p := by
  cases p
  simp only [polarMap, polarInvMap, DensityFrameAction.productAction_inv_left]

/-- Actual forward matrix action cancels the inverse polar total-space frame change. -/
theorem polarMap_polarInvMap (p : PolarTotal (transformed D h)) :
    polarMap D h (polarInvMap D h p) = p := by
  cases p
  simp only [polarMap, polarInvMap, DensityFrameAction.productAction_inv_right]

/-- Actual represented inverse matrix action cancels the forward spinor total-space frame change. -/
theorem spinorInvMap_spinorMap (p : SpinorTotal D) :
    spinorInvMap D h (spinorMap D h p) = p := by
  cases p
  simp only [spinorMap, spinorInvMap, RegularSpinorAction.act_inv_act]

/-- Actual represented forward action cancels the inverse spinor total-space frame change. -/
theorem spinorMap_spinorInvMap (p : SpinorTotal (transformed D h)) :
    spinorMap D h (spinorInvMap D h p) = p := by
  cases p
  simp only [spinorMap, spinorInvMap, RegularSpinorAction.act_act_inv]

/-- In every actual bundle trivialization the polar total-space map is the local matrix action indexed by that chart, with the base unchanged. -/
theorem localTriv_polarMap (i : ι) (p : PolarTotal D) :
    (polarCore (transformed D h)).localTriv i (polarMap D h p) =
      (p.proj, DensityFrameAction.productAction (h.value i p.proj)
        ((polarCore D).localTriv i p).2) := by
  change (p.proj, polarChange (transformed D h) (indexAt (transformed D h) p.proj) i p.proj
    (DensityFrameAction.productAction (h.value (indexAt D p.proj) p.proj) p.2)) = _
  exact congrArg (Prod.mk p.proj) (polar_intertwining D h (indexAt D p.proj) i p.proj p.2)

/-- In every actual trivialization the inverse polar total-space map is the actual inverse local matrix action, with the base unchanged. -/
theorem localTriv_polarInvMap (i : ι) (p : PolarTotal (transformed D h)) :
    (polarCore D).localTriv i (polarInvMap D h p) =
      (p.proj, DensityFrameAction.productAction (h.value i p.proj)⁻¹
        ((polarCore (transformed D h)).localTriv i p).2) := by
  change (p.proj, polarChange D (indexAt D p.proj) i p.proj
    (DensityFrameAction.productAction (h.value (indexAt D p.proj) p.proj)⁻¹ p.2)) =
    (p.proj, DensityFrameAction.productAction (h.value i p.proj)⁻¹
      (polarChange (transformed D h) (indexAt (transformed D h) p.proj) i p.proj p.2))
  exact congrArg (Prod.mk p.proj) (polar_intertwining_inv D h (indexAt D p.proj) i p.proj p.2)

/-- The actual spinor total-space frame change has the direct represented local matrix action in every actual bundle chart. -/
theorem localTriv_spinorMap (i : ι) (p : SpinorTotal D) :
    (spinorCore (transformed D h)).localTriv i (spinorMap D h p) =
      (p.proj, RegularSpinorAction.act (h.value i p.proj)
        ((spinorCore D).localTriv i p).2) := by
  exact localTriv_frameMap (spinorCore D) (spinorCore (transformed D h))
    (fun i x q => RegularSpinorAction.act (h.value i x) q) rfl
    (spinor_intertwining D h) i p

/-- The actual inverse spinor total-space frame change has the represented inverse local matrix action in every bundle chart. -/
theorem localTriv_spinorInvMap (i : ι) (p : SpinorTotal (transformed D h)) :
    (spinorCore D).localTriv i (spinorInvMap D h p) =
      (p.proj, RegularSpinorAction.act (h.value i p.proj)⁻¹
        ((spinorCore (transformed D h)).localTriv i p).2) := by
  exact localTriv_frameMap (spinorCore (transformed D h)) (spinorCore D)
    (fun i x q => RegularSpinorAction.act ((h.value i x)⁻¹) q) rfl
    (spinor_intertwining_inv D h) i p

variable [IsManifold I n B]

/-- The actual polar total-space frame change is smooth because every genuine local expression is the supplied smooth matrix action. -/
theorem contMDiff_polarMap :
    ContMDiff (polarModel I) (polarModel I) n (polarMap D h) := by
  intro p
  let i := indexAt D p.proj
  have hp : p ∈ ((polarCore D).localTriv i).source := mem_domain_indexAt D p.proj
  have hq : polarMap D h p ∈ ((polarCore (transformed D h)).localTriv i).source := hp
  apply (SmoothCocycleBundle.contMDiffAt_iff_localTriv I DensityFrameManifold.model
    (polarCore (transformed D h)) (contMDiffOn_polarChange (transformed D h)) i hq).mpr
  have htriv := SmoothCocycleBundle.contMDiffAt_localTriv I DensityFrameManifold.model
    (polarCore D) (contMDiffOn_polarChange D) i p hp
  have ha := (contMDiffOn_fst.prodMk (contMDiffOn_polarAction D h i)).contMDiffAt
    (((D.domain i).isOpen.prod isOpen_univ).mem_nhds
      (show (polarCore D).localTriv i p ∈ (D.domain i : Set B) ×ˢ univ from
        ⟨hp, mem_univ _⟩))
  apply (ha.comp p htriv).congr_of_eventuallyEq
  exact Filter.Eventually.of_forall (fun q => localTriv_polarMap D h i q)

/-- The actual polar inverse total-space frame change is smooth because every genuine local expression is the supplied smooth inverse matrix action. -/
theorem contMDiff_polarInvMap :
    ContMDiff (polarModel I) (polarModel I) n (polarInvMap D h) := by
  intro p
  let i := indexAt D p.proj
  have hp : p ∈ ((polarCore (transformed D h)).localTriv i).source := mem_domain_indexAt D p.proj
  have hq : polarInvMap D h p ∈ ((polarCore D).localTriv i).source := hp
  apply (SmoothCocycleBundle.contMDiffAt_iff_localTriv I DensityFrameManifold.model
    (polarCore D) (contMDiffOn_polarChange D) i hq).mpr
  have htriv := SmoothCocycleBundle.contMDiffAt_localTriv I DensityFrameManifold.model
    (polarCore (transformed D h)) (contMDiffOn_polarChange (transformed D h)) i p hp
  have ha := (contMDiffOn_fst.prodMk (contMDiffOn_polarAction_inv D h i)).contMDiffAt
    (((D.domain i).isOpen.prod isOpen_univ).mem_nhds
      (show (polarCore (transformed D h)).localTriv i p ∈ (D.domain i : Set B) ×ˢ univ from
        ⟨hp, mem_univ _⟩))
  apply (ha.comp p htriv).congr_of_eventuallyEq
  exact Filter.Eventually.of_forall (fun q => localTriv_polarInvMap D h i q)

/-- The directly defined represented-spinor frame change is smooth by its proved equivariance with the locally smooth polar bundle map and the independent total realization diffeomorphisms. -/
theorem contMDiff_spinorMap :
    ContMDiff (spinorModel I) (spinorModel I) n (spinorMap D h) := by
  have he : spinorMap D h = (totalRealizationDiffeomorph (transformed D h)) ∘
      (polarMap D h) ∘ (totalRealizationDiffeomorph D).symm := by
    funext p
    cases p with
    | mk x v =>
      change (⟨x, RegularSpinorAction.act (h.value (indexAt D x) x) v⟩ :
        SpinorTotal (transformed D h)) =
        ⟨x, SourcePolarProductQuotient.productRegularHomeomorph
          (DensityFrameAction.productAction (h.value (indexAt D x) x)
            (SourcePolarProductQuotient.productRegularHomeomorph.symm v))⟩
      have hv := RegularSpinorAction.realization_equivariant
        (h.value (indexAt D x) x) (SourcePolarProductQuotient.productRegularHomeomorph.symm v)
      rw [Homeomorph.apply_symm_apply] at hv
      exact congrArg (fun q => (⟨x, q⟩ : SpinorTotal (transformed D h))) hv.symm
  rw [he]
  exact (totalRealizationDiffeomorph (transformed D h)).contMDiff.comp
    ((contMDiff_polarMap D h).comp (totalRealizationDiffeomorph D).symm.contMDiff)

/-- The directly defined inverse represented-spinor frame change is smooth through the proved inverse action equivariance and the independently smooth polar inverse and total realization maps. -/
theorem contMDiff_spinorInvMap :
    ContMDiff (spinorModel I) (spinorModel I) n (spinorInvMap D h) := by
  have he : spinorInvMap D h = (totalRealizationDiffeomorph D) ∘
      (polarInvMap D h) ∘ (totalRealizationDiffeomorph (transformed D h)).symm := by
    funext p
    cases p with
    | mk x v =>
      change (⟨x, RegularSpinorAction.act (h.value (indexAt D x) x)⁻¹ v⟩ :
        SpinorTotal D) =
        ⟨x, SourcePolarProductQuotient.productRegularHomeomorph
          (DensityFrameAction.productAction (h.value (indexAt D x) x)⁻¹
            (SourcePolarProductQuotient.productRegularHomeomorph.symm v))⟩
      have hv := RegularSpinorAction.realization_equivariant
        (h.value (indexAt D x) x)⁻¹ (SourcePolarProductQuotient.productRegularHomeomorph.symm v)
      rw [Homeomorph.apply_symm_apply] at hv
      exact congrArg (fun q => (⟨x, q⟩ : SpinorTotal D)) hv.symm
  rw [he]
  exact (totalRealizationDiffeomorph D).contMDiff.comp
    ((contMDiff_polarInvMap D h).comp
      (totalRealizationDiffeomorph (transformed D h)).symm.contMDiff)

/-- The supplied local frame change induces a genuine base-preserving diffeomorphism between the actual old and transformed polar bundle total spaces. -/
def polarDiffeomorph :
    Diffeomorph (polarModel I) (polarModel I) (PolarTotal D)
      (PolarTotal (transformed D h)) n where
  toFun := polarMap D h
  invFun := polarInvMap D h
  left_inv := polarInvMap_polarMap D h
  right_inv := polarMap_polarInvMap D h
  contMDiff_toFun := contMDiff_polarMap D h
  contMDiff_invFun := contMDiff_polarInvMap D h

/-- The supplied local frame change induces a genuine base-preserving diffeomorphism between the actual old and transformed represented-spinor bundle total spaces. -/
def spinorDiffeomorph :
    Diffeomorph (spinorModel I) (spinorModel I) (SpinorTotal D)
      (SpinorTotal (transformed D h)) n where
  toFun := spinorMap D h
  invFun := spinorInvMap D h
  left_inv := spinorInvMap_spinorMap D h
  right_inv := spinorMap_spinorInvMap D h
  contMDiff_toFun := contMDiff_spinorMap D h
  contMDiff_invFun := contMDiff_spinorInvMap D h

/-- The actual polar bundle diffeomorphism applies the supplied matrix in selected fiber coordinates and leaves the base point fixed. -/
theorem polarDiffeomorph_apply (p : PolarTotal D) :
    polarDiffeomorph D h p =
      ⟨p.proj, DensityFrameAction.productAction (h.value (indexAt D p.proj) p.proj) p.2⟩ := rfl

/-- The actual inverse polar diffeomorphism applies the inverse supplied matrix in the same selected fiber coordinates. -/
theorem polarDiffeomorph_symm_apply (p : PolarTotal (transformed D h)) :
    (polarDiffeomorph D h).symm p =
      ⟨p.proj, DensityFrameAction.productAction (h.value (indexAt D p.proj) p.proj)⁻¹ p.2⟩ := rfl

/-- The actual spinor bundle diffeomorphism is direct represented matrix action in selected fiber coordinates over the same base point. -/
theorem spinorDiffeomorph_apply (p : SpinorTotal D) :
    spinorDiffeomorph D h p =
      ⟨p.proj, RegularSpinorAction.act (h.value (indexAt D p.proj) p.proj) p.2⟩ := rfl

/-- The actual inverse spinor bundle diffeomorphism uses the direct represented inverse matrix at the same base point. -/
theorem spinorDiffeomorph_symm_apply (p : SpinorTotal (transformed D h)) :
    (spinorDiffeomorph D h).symm p =
      ⟨p.proj, RegularSpinorAction.act (h.value (indexAt D p.proj) p.proj)⁻¹ p.2⟩ := rfl

/-- The actual polar bundle diffeomorphism preserves the bundle projection exactly. -/
theorem polarDiffeomorph_proj (p : PolarTotal D) :
    (polarDiffeomorph D h p).proj = p.proj := rfl

/-- The actual represented-spinor bundle diffeomorphism preserves the bundle projection exactly. -/
theorem spinorDiffeomorph_proj (p : SpinorTotal D) :
    (spinorDiffeomorph D h p).proj = p.proj := by
  have he := congrArg (fun q : SpinorTotal (transformed D h) => q.proj)
    (spinorDiffeomorph_apply D h p)
  exact he

/-- The independently constructed gauge bundle maps commute with actual total-space polar realization. -/
theorem realization_commutes (p : PolarTotal D) :
    totalRealizationDiffeomorph (transformed D h) (polarDiffeomorph D h p) =
      spinorDiffeomorph D h (totalRealizationDiffeomorph D p) := by
  cases p with
  | mk x v =>
    change (⟨x, SourcePolarProductQuotient.productRegularHomeomorph
        (DensityFrameAction.productAction (h.value (indexAt D x) x) v)⟩ :
      SpinorTotal (transformed D h)) =
      ⟨x, RegularSpinorAction.act (h.value (indexAt D x) x)
        (SourcePolarProductQuotient.productRegularHomeomorph v)⟩
    exact congrArg (fun q => (⟨x, q⟩ : SpinorTotal (transformed D h)))
      (RegularSpinorAction.realization_equivariant _ _)

end FoliationQM.CocycleGaugeBundles
