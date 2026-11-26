module
public import FoliationQM.CliffordSpinCocycleFields
public import FoliationQM.PolarCocycleSections
public import FoliationQM.SmoothCocycleSections

/-!
# Actual Clifford polar cocycle bundles and graph-smooth sections

Source scope: the supplied-cocycle section bridge in v13 `prop:takabayasi`.
An independently supplied smooth Clifford Spin-valued transition cocycle
constructs a genuine fiber-bundle core with the actual density/Clifford
frame-quotient fiber. Its topology is the core topology, and its atlas
uses actual local trivializations followed by the independent base and
fiber charts. Smoothness of total-space transitions is proved from the
actual overlap action, without a smooth chart-index selection.

Dependent sections are defined independently by smoothness of their
actual total-space graphs. The generic local-coordinate theorem gives
their precise correspondence with independently compatible local fields;
actual polar realization then identifies them with the existing graph-
smooth represented-spinor sections for the same supplied cocycle. No
existence of a Spin structure from arbitrary Lorentz transitions, no
arbitrary geometric spacetime identification, and no variational Dirac
dynamics is asserted.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Matrix.Norms.Operator Manifold Topology
open Set Bundle
namespace FoliationQM.CliffordSpinCocycleSections
open CliffordSpinPolarCocycle CliffordSpinPolarReconstruction

variable {E H B : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace B] [ChartedSpace H B] {ι : Type*} {n : WithTop ℕ∞}
  (D : Data I B ι n)

/-- The actual polar bundle core has genuine Clifford frame-quotient fibers and the independently supplied actual Spin transition action. -/
def polarCore : FiberBundleCore ι B Product where
  baseSet i := D.domain i
  isOpen_baseSet i := (D.domain i).isOpen
  indexAt := PolarTransitionCocycle.indexAt (toMatrixData D)
  mem_baseSet_at := PolarTransitionCocycle.mem_domain_indexAt (toMatrixData D)
  coordChange := polarChange D
  coordChange_self := polarChange_self D
  continuousOn_coordChange i j := (contMDiffOn_polarChange D i j).continuousOn
  coordChange_comp i j k x hx v := polarChange_comp D i j k x hx.1.1 hx.1.2 hx.2 v

/-- The actual Clifford polar cocycle total space, with its genuine core-generated topology. -/
abbrev PolarTotal := (polarCore D).TotalSpace

/-- The actual Clifford cocycle atlas uses its genuine core trivializations and the independently specified base and actual polar-fiber charts. -/
instance instChartedSpacePolarTotal :
    ChartedSpace (ModelProd H ChartModel) (PolarTotal D) :=
  SmoothCocycleBundle.totalChartedSpace H ChartModel (polarCore D)

variable [IsManifold I n B]

/-- Actual smooth Clifford transitions give a manifold atlas on the genuine polar core total space at the stated base regularity. -/
instance instIsManifoldPolarTotal : IsManifold (I.prod model) n (PolarTotal D) :=
  SmoothCocycleBundle.isManifold_total I model (polarCore D) (contMDiffOn_polarChange D)

/-- Each actual Clifford polar bundle trivialization is smooth on its genuine total-space source. -/
theorem contMDiffOn_localTriv (i : ι) :
    ContMDiffOn (I.prod model) (I.prod model) n ((polarCore D).localTriv i)
      ((polarCore D).localTriv i).source :=
  SmoothCocycleBundle.contMDiffOn_localTriv I model (polarCore D)
    (contMDiffOn_polarChange D) i

/-- Each actual inverse Clifford polar trivialization is smooth on its genuine base/fiber domain. -/
theorem contMDiffOn_localTriv_symm (i : ι) :
    ContMDiffOn (I.prod model) (I.prod model) n ((polarCore D).localTriv i).toOpenPartialHomeomorph.symm
      ((polarCore D).localTriv i).target :=
  SmoothCocycleBundle.contMDiffOn_localTriv_symm I model (polarCore D)
    (contMDiffOn_polarChange D) i

/-- The actual Clifford polar bundle projection is smooth for its genuine independently constructed core atlas. -/
theorem contMDiff_proj : ContMDiff (I.prod model) I n (polarCore D).proj :=
  SmoothCocycleBundle.contMDiff_proj I model (polarCore D) (contMDiffOn_polarChange D)

/-- Actual dependent Clifford polar sections are defined by smoothness of their total-space graphs in the core atlas. -/
abbrev PolarSection := SmoothCocycleSections.SmoothSection I model (polarCore D) n

/-- Actual represented-spinor sections use the independently defined section graphs for the same genuine Spin cocycle's matrix representation. -/
abbrev SpinorSection := PolarCocycleSections.SpinorSection (toMatrixData D)

/-- Graph smoothness of an actual Clifford polar dependent section is exactly smoothness of every true local trivialization coordinate. -/
theorem graph_smooth_iff (s : ∀ x : B, (polarCore D).Fiber x) :
    ContMDiff I (I.prod model) n (SmoothCocycleSections.sectionGraph (polarCore D) s) ↔
      ∀ i, ContMDiff I model n (SmoothCocycleSections.sectionCoordinate (polarCore D) s i) :=
  SmoothCocycleSections.contMDiff_graph_iff I model (polarCore D) n
    (contMDiffOn_polarChange D) s

/-- Independently graph-smooth actual Clifford polar sections correspond exactly to independently compatible smooth actual polar families. -/
def polarFamilyEquiv : PolarSection D ≃ CliffordSpinCocycleFields.SmoothPolarFamily D :=
  SmoothCocycleSections.sectionEquiv I model (polarCore D) n
    (contMDiffOn_polarChange D)

/-- The actual section/family correspondence reads the genuine local-trivialization coordinate of the section graph. -/
theorem polarFamilyEquiv_apply (s : PolarSection D) (i : ι) (x : D.domain i) :
    (polarFamilyEquiv D s).val i x =
      ((polarCore D).localTriv i (⟨x.val, s.val x.val⟩ : PolarTotal D)).2 := rfl

/-- Reconstructing an actual Clifford polar section from a compatible local family recovers the prescribed coordinate in every available chart. -/
theorem polarFamilyEquiv_symm_localTriv (f : CliffordSpinCocycleFields.SmoothPolarFamily D)
    (i : ι) (x : D.domain i) :
    (polarCore D).localTriv i
      (⟨x.val, ((polarFamilyEquiv D).symm f).val x.val⟩ : PolarTotal D) =
      (x.val, f.val i x) :=
  SmoothCocycleSections.sectionEquiv_symm_localTriv I model (polarCore D) n
    (contMDiffOn_polarChange D) f i x.val x.property

/-- The genuine Clifford polar section correspondence is assembled through exact compatible-family realization and the independently graph-defined represented-spinor sections. -/
def sectionEquiv : PolarSection D ≃ SpinorSection D :=
  (polarFamilyEquiv D).trans
    ((CliffordSpinCocycleFields.realizationEquiv D).trans
      ((CliffordSpinCocycleFields.matrixSpinorFamilyEquiv D).trans
        (PolarCocycleSections.spinorFamilyEquiv (toMatrixData D)).symm))

/-- Section realization has exactly the already proved actual local-family realization in every chart. -/
theorem sectionEquiv_family (s : PolarSection D) :
    PolarCocycleSections.spinorFamilyEquiv (toMatrixData D) (sectionEquiv D s) =
      CliffordSpinCocycleFields.matrixSpinorFamilyEquiv D
        (CliffordSpinCocycleFields.realizationEquiv D (polarFamilyEquiv D s)) := by
  exact (PolarCocycleSections.spinorFamilyEquiv (toMatrixData D)).apply_symm_apply _


/-- The actual graph-section correspondence realizes the genuine Clifford density/frame value in the fiber over the same base point. -/
theorem sectionEquiv_apply (s : PolarSection D) (x : B) :
    (sectionEquiv D s).val x =
      CliffordSpinPolarQuotient.productRegularHomeomorph (s.val x) := by
  let i := PolarTransitionCocycle.indexAt (toMatrixData D) x
  have hx : x ∈ D.domain i := PolarTransitionCocycle.mem_domain_indexAt (toMatrixData D) x
  have h := congrArg (fun f : CocyclePolarFields.SmoothSpinorFamily (toMatrixData D) =>
    f.val i ⟨x, hx⟩) (sectionEquiv_family D s)
  rw [CliffordSpinCocycleFields.matrixSpinorFamilyEquiv_apply,
    CliffordSpinCocycleFields.realizationEquiv_apply] at h
  have hs : (polarFamilyEquiv D s).val i ⟨x, hx⟩ = s.val x :=
    SmoothCocycleSections.sectionCoordinate_indexAt (polarCore D) s.val x
  have ht : (PolarCocycleSections.spinorFamilyEquiv (toMatrixData D)
      (sectionEquiv D s)).val i ⟨x, hx⟩ = (sectionEquiv D s).val x :=
    SmoothCocycleSections.sectionCoordinate_indexAt
      (PolarCocycleBundles.spinorCore (toMatrixData D)) (sectionEquiv D s).val x
  rw [hs, ht] at h
  exact h

/-- Inverse graph-section reconstruction is precisely the actual Clifford quotient-valued polar inverse in each original fiber. -/
theorem sectionEquiv_symm_apply (s : SpinorSection D) (x : B) :
    ((sectionEquiv D).symm s).val x =
      CliffordSpinPolarQuotient.productRegularHomeomorph.symm (s.val x) := by
  apply CliffordSpinPolarQuotient.productRegularHomeomorph.injective
  rw [← sectionEquiv_apply, Equiv.apply_symm_apply,
    CliffordSpinPolarQuotient.productRegularHomeomorph.apply_symm_apply]

/-- Actual graph-section realization preserves the original positive density as the represented section's scalar-pseudoscalar bilinear invariant. -/
theorem sectionEquiv_density (s : PolarSection D) (x : B) :
    SpinorRegularity.invariantDensity ((sectionEquiv D s).val x).val =
      ((s.val x).1 : ℝ) := by
  rw [sectionEquiv_apply]
  exact CliffordSpinPolarQuotient.density_productRegularHomeomorph (s.val x)

/-- Inverse actual graph-section reconstruction recovers the represented section's original bilinear invariant density. -/
theorem sectionEquiv_symm_density (s : SpinorSection D) (x : B) :
    ((((sectionEquiv D).symm s).val x).1 : ℝ) =
      SpinorRegularity.invariantDensity (s.val x).val := by
  rw [sectionEquiv_symm_apply]
  exact CliffordSpinPolarQuotient.productRegularHomeomorph_symm_density (s.val x)

/-- Every graph-smooth represented-spinor section has exactly one graph-smooth actual Clifford polar section with its pointwise physical realization. -/
theorem existsUnique_polarSection (s : SpinorSection D) :
    ∃! t : PolarSection D, ∀ x,
      CliffordSpinPolarQuotient.productRegularHomeomorph (t.val x) = s.val x := by
  refine ⟨(sectionEquiv D).symm s, ?_, ?_⟩
  · intro x
    rw [sectionEquiv_symm_apply,
      CliffordSpinPolarQuotient.productRegularHomeomorph.apply_symm_apply]
  · intro t ht
    apply Subtype.ext
    funext x
    apply CliffordSpinPolarQuotient.productRegularHomeomorph.injective
    rw [ht x, sectionEquiv_symm_apply,
      CliffordSpinPolarQuotient.productRegularHomeomorph.apply_symm_apply]

/-- Every independently compatible actual Clifford polar family determines a unique graph-smooth actual dependent section with precisely those local coordinates. -/
theorem existsUnique_section (f : CliffordSpinCocycleFields.SmoothPolarFamily D) :
    ∃! s : PolarSection D, ∀ (i : ι) (x : D.domain i),
      SmoothCocycleSections.sectionCoordinate (polarCore D) s.val i x = f.val i x :=
  SmoothCocycleSections.existsUnique_section I model (polarCore D) n
    (contMDiffOn_polarChange D) f

end FoliationQM.CliffordSpinCocycleSections
