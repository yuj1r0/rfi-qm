module
public import FoliationQM.PolarCocycleBundles
public import FoliationQM.SmoothCocycleBundle

/-!
# Actual smooth polar and spinor cocycle total spaces

Source: the supplied-transition interpretation of v13 `prop:takabayasi`.
The actual polar and regular-spinor `FiberBundleCore` total spaces retain
exactly their existing core-generated topologies. Each independently
receives the atlas obtained from its own genuine local trivializations
followed by the supplied base charts and its independently established
fiber charts. Smooth transition maps and a base manifold of the same
order give genuine total-space manifold structures.

The actual core projections and trivializations are smooth on their
specified domains. Actual total-space realization is then proved smooth
in these two independent atlases: in every trivialization it is the base
identity paired with the existing intrinsic polar fiber diffeomorphism.
The inverse is proved smooth by the corresponding actual local formula.
The resulting bundled diffeomorphism has exactly the previously proved
base-preserving homeomorphism as its underlying map.

All statements retain the supplied cocycle and base-regularity premises.
No total-space topology is replaced by a product topology, no spinor
atlas is defined by transporting the polar atlas through realization,
and no abstract spacetime Spin classification or global individual
angle/frame representative is asserted.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Matrix.Norms.Operator Manifold
open Set Topology
namespace FoliationQM.PolarCocycleManifold
open DiracMatrices PolarSignQuotient PolarTransitionCocycle PolarCocycleBundles
open SourcePolarProductQuotient

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H]

/-- The actual polar total space has the supplied base model times the independent intrinsic density-frame model. -/
abbrev polarModel (I : ModelWithCorners ℝ E H) := I.prod DensityFrameManifold.model

/-- The actual regular-spinor total space has the supplied base model times the independent ambient spinor model. -/
abbrev spinorModel (I : ModelWithCorners ℝ E H) := I.prod 𝓘(ℝ, Spinor)

variable {I : ModelWithCorners ℝ E H} {B ι : Type*}
  [TopologicalSpace B] [ChartedSpace H B] {n : WithTop ℕ∞}
  (D : Data I B ι n)

/-- The polar bundle uses its actual core trivializations followed by the independently specified base and polar-fiber charts, on its unchanged core topology. -/
instance instChartedSpacePolarTotal :
    ChartedSpace (ModelProd H DensityFrameManifold.ChartModel) (PolarTotal D) :=
  SmoothCocycleBundle.totalChartedSpace H DensityFrameManifold.ChartModel (polarCore D)

/-- The spinor bundle independently uses its own actual core trivializations followed by the base and regular-spinor charts, on its unchanged core topology. -/
instance instChartedSpaceSpinorTotal :
    ChartedSpace (ModelProd H Spinor) (SpinorTotal D) :=
  SmoothCocycleBundle.totalChartedSpace H Spinor (spinorCore D)

variable [IsManifold I n B]

/-- Smooth supplied matrix transitions make the actual polar bundle total space a manifold at the same order as the base. -/
instance instIsManifoldPolarTotal : IsManifold (polarModel I) n (PolarTotal D) :=
  SmoothCocycleBundle.isManifold_total I DensityFrameManifold.model (polarCore D)
    (contMDiffOn_polarChange D)

/-- Smooth supplied represented transitions make the independently charted spinor bundle total space a manifold at the same order as the base. -/
instance instIsManifoldSpinorTotal : IsManifold (spinorModel I) n (SpinorTotal D) :=
  SmoothCocycleBundle.isManifold_total I 𝓘(ℝ, Spinor) (spinorCore D)
    (contMDiffOn_spinorChange D)

/-- Every actual polar core trivialization is smooth on its actual source domain for the intrinsic total atlas. -/
theorem contMDiffOn_polar_localTriv (i : ι) :
    ContMDiffOn (polarModel I) (polarModel I) n ((polarCore D).localTriv i)
      ((polarCore D).localTriv i).source :=
  SmoothCocycleBundle.contMDiffOn_localTriv I DensityFrameManifold.model (polarCore D)
    (contMDiffOn_polarChange D) i

/-- Every actual inverse polar core trivialization is smooth on its actual product target domain. -/
theorem contMDiffOn_polar_localTriv_symm (i : ι) :
    ContMDiffOn (polarModel I) (polarModel I) n
      ((polarCore D).localTriv i).toOpenPartialHomeomorph.symm
      ((polarCore D).localTriv i).target :=
  SmoothCocycleBundle.contMDiffOn_localTriv_symm I DensityFrameManifold.model (polarCore D)
    (contMDiffOn_polarChange D) i

/-- Every actual spinor core trivialization is smooth on its actual source domain for its independently constructed total atlas. -/
theorem contMDiffOn_spinor_localTriv (i : ι) :
    ContMDiffOn (spinorModel I) (spinorModel I) n ((spinorCore D).localTriv i)
      ((spinorCore D).localTriv i).source :=
  SmoothCocycleBundle.contMDiffOn_localTriv I 𝓘(ℝ, Spinor) (spinorCore D)
    (contMDiffOn_spinorChange D) i

/-- Every actual inverse spinor core trivialization is smooth on its actual product target domain. -/
theorem contMDiffOn_spinor_localTriv_symm (i : ι) :
    ContMDiffOn (spinorModel I) (spinorModel I) n
      ((spinorCore D).localTriv i).toOpenPartialHomeomorph.symm
      ((spinorCore D).localTriv i).target :=
  SmoothCocycleBundle.contMDiffOn_localTriv_symm I 𝓘(ℝ, Spinor) (spinorCore D)
    (contMDiffOn_spinorChange D) i

/-- The actual polar bundle projection is globally smooth for the genuine total atlas. -/
theorem contMDiff_polar_proj : ContMDiff (polarModel I) I n (polarCore D).proj := by
  intro p
  let i := indexAt D p.proj
  have hp : p ∈ ((polarCore D).localTriv i).source := mem_domain_indexAt D p.proj
  have h := (contMDiffOn_polar_localTriv D i).contMDiffAt
    (((polarCore D).localTriv i).open_source.mem_nhds hp)
  exact h.fst

/-- The actual regular-spinor bundle projection is globally smooth for its independently constructed total atlas. -/
theorem contMDiff_spinor_proj : ContMDiff (spinorModel I) I n (spinorCore D).proj := by
  intro p
  let i := indexAt D p.proj
  have hp : p ∈ ((spinorCore D).localTriv i).source := mem_domain_indexAt D p.proj
  have h := (contMDiffOn_spinor_localTriv D i).contMDiffAt
    (((spinorCore D).localTriv i).open_source.mem_nhds hp)
  exact h.fst

/-- Actual fiberwise realization is smooth in the genuine independently specified total-space atlases. -/
theorem contMDiff_totalRealization :
    ContMDiff (polarModel I) (spinorModel I) n (totalRealization D) := by
  intro p
  let i := indexAt D p.proj
  have hp : p ∈ ((polarCore D).localTriv i).source := mem_domain_indexAt D p.proj
  have hq : totalRealization D p ∈ ((spinorCore D).localTriv i).source := hp
  have hpt := (contMDiffOn_polar_localTriv D i).contMDiffAt
    (((polarCore D).localTriv i).open_source.mem_nhds hp)
  have ht : ContMDiff (polarModel I) (spinorModel I) n
      (fun q : B × DensityFrameManifold.Product =>
        (q.1, productRegularHomeomorph q.2)) :=
    contMDiff_fst.prodMk
      ((DensityFrameManifold.productRegularDiffeomorph n).contMDiff.comp contMDiff_snd)
  have hqt := (contMDiffOn_spinor_localTriv_symm D i).contMDiffAt
    (((spinorCore D).localTriv i).open_target.mem_nhds
      (((spinorCore D).localTriv i).map_source hq))
  change ContMDiffAt (spinorModel I) (spinorModel I) n
    ((spinorCore D).localTriv i).toOpenPartialHomeomorph.symm
    ((spinorCore D).localTriv i (totalRealization D p)) at hqt
  rw [localTriv_totalRealization D i p] at hqt
  have hc := hqt.comp p (ht.contMDiffAt.comp p hpt)
  apply hc.congr_of_eventuallyEq
  filter_upwards [((polarCore D).localTriv i).open_source.mem_nhds hp] with q hqs
  change totalRealization D q =
    ((spinorCore D).localTriv i).toOpenPartialHomeomorph.symm
      (((polarCore D).localTriv i q).1,
        productRegularHomeomorph ((polarCore D).localTriv i q).2)
  rw [← localTriv_totalRealization D i q]
  exact (((spinorCore D).localTriv i).toOpenPartialHomeomorph.left_inv hqs).symm

/-- Actual inverse fiberwise polar reconstruction is smooth in the two genuine total-space atlases. -/
theorem contMDiff_totalRealization_symm :
    ContMDiff (spinorModel I) (polarModel I) n (totalRealization D).symm := by
  intro p
  let i := indexAt D p.proj
  have hp : p ∈ ((spinorCore D).localTriv i).source := mem_domain_indexAt D p.proj
  have hq : (totalRealization D).symm p ∈ ((polarCore D).localTriv i).source := hp
  have hpt := (contMDiffOn_spinor_localTriv D i).contMDiffAt
    (((spinorCore D).localTriv i).open_source.mem_nhds hp)
  have ht : ContMDiff (spinorModel I) (polarModel I) n
      (fun q : B × RegularSpinor =>
        (q.1, productRegularHomeomorph.symm q.2)) :=
    contMDiff_fst.prodMk
      ((DensityFrameManifold.productRegularDiffeomorph n).symm.contMDiff.comp contMDiff_snd)
  have hqt := (contMDiffOn_polar_localTriv_symm D i).contMDiffAt
    (((polarCore D).localTriv i).open_target.mem_nhds
      (((polarCore D).localTriv i).map_source hq))
  change ContMDiffAt (polarModel I) (polarModel I) n
    ((polarCore D).localTriv i).toOpenPartialHomeomorph.symm
    ((polarCore D).localTriv i ((totalRealization D).symm p)) at hqt
  rw [localTriv_totalRealization_symm D i p] at hqt
  have hc := hqt.comp p (ht.contMDiffAt.comp p hpt)
  apply hc.congr_of_eventuallyEq
  filter_upwards [((spinorCore D).localTriv i).open_source.mem_nhds hp] with q hqs
  change (totalRealization D).symm q =
    ((polarCore D).localTriv i).toOpenPartialHomeomorph.symm
      (((spinorCore D).localTriv i q).1,
        productRegularHomeomorph.symm ((spinorCore D).localTriv i q).2)
  rw [← localTriv_totalRealization_symm D i q]
  exact (((polarCore D).localTriv i).toOpenPartialHomeomorph.left_inv hqs).symm

/-- The existing base-preserving total-space realization homeomorphism is a genuine diffeomorphism for the independently constructed cocycle-bundle atlases. -/
def totalRealizationDiffeomorph :
    Diffeomorph (polarModel I) (spinorModel I) (PolarTotal D) (SpinorTotal D) n where
  toEquiv := (totalRealization D).toEquiv
  contMDiff_toFun := contMDiff_totalRealization D
  contMDiff_invFun := contMDiff_totalRealization_symm D

/-- The genuine total-space diffeomorphism retains exactly the previously constructed homeomorphism and hence the original core topologies. -/
theorem totalRealizationDiffeomorph_toHomeomorph :
    (totalRealizationDiffeomorph D).toHomeomorph = totalRealization D := rfl

/-- The total-space diffeomorphism is the actual fiber realization at the same base point. -/
theorem totalRealizationDiffeomorph_apply (p : PolarTotal D) :
    totalRealizationDiffeomorph D p = ⟨p.proj, productRegularHomeomorph p.2⟩ := rfl

/-- The actual inverse total-space diffeomorphism is quotient-valued polar reconstruction at the same base point. -/
theorem totalRealizationDiffeomorph_symm_apply (p : SpinorTotal D) :
    (totalRealizationDiffeomorph D).symm p =
      ⟨p.proj, productRegularHomeomorph.symm p.2⟩ := rfl

end FoliationQM.PolarCocycleManifold
