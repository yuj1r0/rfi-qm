module
public import FoliationQM.CliffordSpinPolarCocycle
public import FoliationQM.CliffordSpinPolarFields
public import FoliationQM.CocyclePolarFields

/-!
# Compatible local fields for actual Clifford Spin cocycles

Source scope: supplied-cocycle polar fields in v13 `prop:takabayasi`
and `eq:takabayasi_polar`. Local polar and regular-spinor fields are
independently required to be smooth on the actual open chart subtypes
and compatible under the independently defined Clifford group actions.
The genuine quotient-coordinate diffeomorphism identifies actual polar
families with the existing matrix polar families on the identical cover;
the direct universal Clifford Dirac action identifies spinor families.

Actual polar realization and quotient-valued reconstruction give a
bijection of these independently compatible families. The matrix-family
identifications commute with realization. The original bilinear
invariant density is recovered and glues uniquely to a smooth positive
density. The chart index used for pointwise gluing is never assumed
continuous. No global individual representative, arbitrary Lorentz-cocycle
lift, spacetime Spin structure, or variational dynamics is asserted.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Matrix.Norms.Operator Manifold
open Function Set Topology
namespace FoliationQM.CliffordSpinCocycleFields
open CliffordSpinPolarCocycle CliffordSpinPolarReconstruction CliffordSpinPolarQuotient
open PolarSignQuotient DiracMatrices PolarAmplitudeTopology

variable {E H B : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace B] [ChartedSpace H B]
  {ι : Type*} {n : WithTop ℕ∞} (D : Data I B ι n)

/-- Genuine bundled smooth actual Clifford polar fields, each restricted to its supplied open chart domain. -/
abbrev RawPolarFamily := ∀ i : ι, C^n⟮I, ↥(D.domain i); model, Product⟯

/-- Genuine bundled smooth regular-spinor fields on the supplied actual open chart domains. -/
abbrev RawSpinorFamily := ∀ i : ι, C^n⟮I, ↥(D.domain i); 𝓘(ℝ, Spinor), RegularSpinor⟯

/-- Independent polar compatibility uses the actual Clifford frame-class action in the chart i to chart j orientation. -/
def PolarCompatible (f : RawPolarFamily D) : Prop :=
  ∀ (i j : ι) (x : B) (hi : x ∈ D.domain i) (hj : x ∈ D.domain j),
    f j ⟨x, hj⟩ = polarChange D i j x (f i ⟨x, hi⟩)

/-- Independent spinor compatibility uses the direct universal Clifford Dirac transition in the same chart-change orientation. -/
def SpinorCompatible (psi : RawSpinorFamily D) : Prop :=
  ∀ (i j : ι) (x : B) (hi : x ∈ D.domain i) (hj : x ∈ D.domain j),
    psi j ⟨x, hj⟩ = spinorChange D i j x (psi i ⟨x, hi⟩)

/-- Smooth local actual Clifford polar families satisfying their independently stated transition law. -/
def SmoothPolarFamily := {f : RawPolarFamily D // PolarCompatible D f}

/-- Smooth local regular-spinor families satisfying their independently stated universal Dirac transition law. -/
def SmoothSpinorFamily := {psi : RawSpinorFamily D // SpinorCompatible D psi}

/-- The actual Clifford-to-matrix quotient diffeomorphism identifies compatible bundled polar families on exactly the same supplied open cover. -/
def matrixPolarFamilyEquiv :
    SmoothPolarFamily D ≃ CocyclePolarFields.SmoothPolarFamily (toMatrixData D) where
  toFun f := ⟨fun i => (productMatrixDiffeomorph n).toContMDiffMap.comp (f.val i), by
    intro i j x hi hj
    change productMatrixDiffeomorph n (f.val j ⟨x, hj⟩) =
      PolarTransitionCocycle.polarChange (toMatrixData D) i j x
        (productMatrixDiffeomorph n (f.val i ⟨x, hi⟩))
    rw [f.property i j x hi hj]
    exact polarChange_matrix D i j x (f.val i ⟨x, hi⟩)⟩
  invFun f := ⟨fun i => (productMatrixDiffeomorph n).symm.toContMDiffMap.comp (f.val i), by
    intro i j x hi hj
    apply (productMatrixDiffeomorph n).injective
    change productMatrixDiffeomorph n ((productMatrixDiffeomorph n).symm (f.val j ⟨x, hj⟩)) =
      productMatrixDiffeomorph n (polarChange D i j x
        ((productMatrixDiffeomorph n).symm (f.val i ⟨x, hi⟩)))
    rw [(productMatrixDiffeomorph n).apply_symm_apply, polarChange_matrix,
      (productMatrixDiffeomorph n).apply_symm_apply]
    exact f.property i j x hi hj⟩
  left_inv f := by
    apply Subtype.ext
    funext i
    apply ContMDiffMap.ext
    intro x
    exact (productMatrixDiffeomorph n).symm_apply_apply (f.val i x)
  right_inv f := by
    apply Subtype.ext
    funext i
    apply ContMDiffMap.ext
    intro x
    exact (productMatrixDiffeomorph n).apply_symm_apply (f.val i x)

/-- Matrix-family conversion applies exactly the genuine product quotient-coordinate diffeomorphism at every local point. -/
theorem matrixPolarFamilyEquiv_apply (f : SmoothPolarFamily D) (i : ι) (x : D.domain i) :
    (matrixPolarFamilyEquiv D f).val i x = productMatrixDiffeomorph n (f.val i x) := rfl

/-- Inverse matrix-family conversion uses precisely the genuine inverse product coordinate diffeomorphism at each local point. -/
theorem matrixPolarFamilyEquiv_symm_apply
    (f : CocyclePolarFields.SmoothPolarFamily (toMatrixData D)) (i : ι) (x : D.domain i) :
    ((matrixPolarFamilyEquiv D).symm f).val i x =
      (productMatrixDiffeomorph n).symm (f.val i x) := rfl

/-- Genuine Clifford-compatible spinor families and their represented matrix counterparts agree as local fields, because the actual universal representations agree. -/
def matrixSpinorFamilyEquiv :
    SmoothSpinorFamily D ≃ CocyclePolarFields.SmoothSpinorFamily (toMatrixData D) where
  toFun psi := ⟨psi.val, by
    intro i j x hi hj
    change psi.val j ⟨x, hj⟩ = PolarTransitionCocycle.spinorChange (toMatrixData D) i j x
      (psi.val i ⟨x, hi⟩)
    rw [← spinorChange_eq_matrix]
    exact psi.property i j x hi hj⟩
  invFun psi := ⟨psi.val, by
    intro i j x hi hj
    change psi.val j ⟨x, hj⟩ = spinorChange D i j x (psi.val i ⟨x, hi⟩)
    rw [spinorChange_eq_matrix]
    exact psi.property i j x hi hj⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The Clifford-to-matrix spinor-family identification leaves each original local spinor value unchanged. -/
theorem matrixSpinorFamilyEquiv_apply (psi : SmoothSpinorFamily D) (i : ι) (x : D.domain i) :
    (matrixSpinorFamilyEquiv D psi).val i x = psi.val i x := rfl

/-- The inverse matrix-to-Clifford spinor-family identification also leaves each original local spinor unchanged. -/
theorem matrixSpinorFamilyEquiv_symm_apply
    (psi : CocyclePolarFields.SmoothSpinorFamily (toMatrixData D)) (i : ι) (x : D.domain i) :
    ((matrixSpinorFamilyEquiv D).symm psi).val i x = psi.val i x := rfl

/-- Actual polar realization preserves the independently imposed Clifford transition compatibility of local smooth fields. -/
theorem realization_compatible {f : RawPolarFamily D} (hf : PolarCompatible D f) :
    SpinorCompatible D (fun i => CliffordSpinPolarFields.fieldEquiv n (f i)) := by
  intro i j x hi hj
  change CliffordSpinPolarFields.fieldEquiv n (f j) ⟨x, hj⟩ =
    spinorChange D i j x (CliffordSpinPolarFields.fieldEquiv n (f i) ⟨x, hi⟩)
  rw [CliffordSpinPolarFields.fieldEquiv_apply, CliffordSpinPolarFields.fieldEquiv_apply,
    hf i j x hi hj]
  exact change_equivariant D i j x (f i ⟨x, hi⟩)

/-- Genuine quotient-valued inverse reconstruction preserves independently imposed universal Clifford Dirac compatibility on every overlap. -/
theorem reconstruction_compatible {psi : RawSpinorFamily D} (hpsi : SpinorCompatible D psi) :
    PolarCompatible D (fun i => (CliffordSpinPolarFields.fieldEquiv n).symm (psi i)) := by
  intro i j x hi hj
  change (CliffordSpinPolarFields.fieldEquiv n).symm (psi j) ⟨x, hj⟩ =
    polarChange D i j x ((CliffordSpinPolarFields.fieldEquiv n).symm (psi i) ⟨x, hi⟩)
  rw [CliffordSpinPolarFields.fieldEquiv_symm_apply, CliffordSpinPolarFields.fieldEquiv_symm_apply]
  change productRegularHomeomorph.symm (psi j ⟨x, hj⟩) =
    polarChange D i j x (productRegularHomeomorph.symm (psi i ⟨x, hi⟩))
  rw [hpsi i j x hi hj]
  exact CliffordSpinPolarAction.reconstruction_equivariant (D.transition i j x) (psi i ⟨x, hi⟩)

/-- Genuine actual Clifford polar realization and inverse reconstruction give a bijection of independently compatible smooth local families on the supplied cover. -/
def realizationEquiv : SmoothPolarFamily D ≃ SmoothSpinorFamily D where
  toFun f := ⟨fun i => CliffordSpinPolarFields.fieldEquiv n (f.val i),
    realization_compatible D f.property⟩
  invFun psi := ⟨fun i => (CliffordSpinPolarFields.fieldEquiv n).symm (psi.val i),
    reconstruction_compatible D psi.property⟩
  left_inv f := by
    apply Subtype.ext
    funext i
    exact (CliffordSpinPolarFields.fieldEquiv n).symm_apply_apply (f.val i)
  right_inv psi := by
    apply Subtype.ext
    funext i
    exact (CliffordSpinPolarFields.fieldEquiv n).apply_symm_apply (psi.val i)

/-- Each compatible local family is realized by its exact actual Clifford density/frame homeomorphism. -/
theorem realizationEquiv_apply (f : SmoothPolarFamily D) (i : ι) (x : D.domain i) :
    (realizationEquiv D f).val i x = productRegularHomeomorph (f.val i x) :=
  CliffordSpinPolarFields.fieldEquiv_apply n (f.val i) x

/-- The inverse compatible-family correspondence is exactly the actual quotient-valued local polar reconstruction. -/
theorem realizationEquiv_symm_apply (psi : SmoothSpinorFamily D) (i : ι) (x : D.domain i) :
    ((realizationEquiv D).symm psi).val i x = productRegularHomeomorph.symm (psi.val i x) :=
  CliffordSpinPolarFields.fieldEquiv_symm_apply n (psi.val i) x

/-- The Clifford and matrix compatible-family identifications commute exactly with their independently proved actual polar realizations. -/
theorem matrix_realization_commutes (f : SmoothPolarFamily D) :
    matrixSpinorFamilyEquiv D (realizationEquiv D f) =
      CocyclePolarFields.realizationEquiv (toMatrixData D) (matrixPolarFamilyEquiv D f) := by
  apply Subtype.ext
  funext i
  apply ContMDiffMap.ext
  intro x
  rw [matrixSpinorFamilyEquiv_apply, realizationEquiv_apply,
    CocyclePolarFields.realizationEquiv_apply, matrixPolarFamilyEquiv_apply]
  exact (congrArg (fun h => h (f.val i x)) (productRegularDiffeomorph_toHomeomorph n)).symm

/-- Actual local family realization recovers precisely the positive density as the spinor's invariant scalar-pseudoscalar density. -/
theorem realizationEquiv_density (f : SmoothPolarFamily D) (i : ι) (x : D.domain i) :
    SpinorRegularity.invariantDensity ((realizationEquiv D f).val i x).val =
      ((f.val i x).1 : ℝ) := by
  rw [realizationEquiv_apply]
  exact density_productRegularHomeomorph (f.val i x)

/-- Actual local inverse family reconstruction recovers exactly the original regular spinor's bilinear invariant density. -/
theorem realizationEquiv_symm_density (psi : SmoothSpinorFamily D) (i : ι) (x : D.domain i) :
    ((((realizationEquiv D).symm psi).val i x).1 : ℝ) =
      SpinorRegularity.invariantDensity (psi.val i x).val := by
  rw [realizationEquiv_symm_apply]
  exact productRegularHomeomorph_symm_density (psi.val i x)

/-- Every compatible actual Clifford spinor family has exactly one compatible quotient-valued polar family with those local realizations. -/
theorem existsUnique_polarFamily (psi : SmoothSpinorFamily D) :
    ∃! f : SmoothPolarFamily D, ∀ (i : ι) (x : D.domain i),
      productRegularHomeomorph (f.val i x) = psi.val i x := by
  refine ⟨(realizationEquiv D).symm psi, ?_, ?_⟩
  · intro i x
    rw [realizationEquiv_symm_apply]
    exact productRegularHomeomorph.apply_symm_apply (psi.val i x)
  · intro f hf
    apply (realizationEquiv D).injective
    rw [(realizationEquiv D).apply_symm_apply]
    apply Subtype.ext
    funext i
    apply ContMDiffMap.ext
    intro x
    rw [realizationEquiv_apply]
    exact hf i x

/-- Compatible actual Clifford polar fields have equal positive-density coordinates on each true overlap. -/
theorem polar_density_overlap (f : SmoothPolarFamily D) (i j : ι) (x : B)
    (hi : x ∈ D.domain i) (hj : x ∈ D.domain j) :
    (f.val j ⟨x, hj⟩).1 = (f.val i ⟨x, hi⟩).1 := by
  rw [f.property i j x hi hj]
  rfl

/-- The actual positive density of a compatible Clifford polar family selected in any covering chart, with no continuity assumption on the selected index. -/
def polarDensity (f : SmoothPolarFamily D) (x : B) : PositiveDensity :=
  (f.val (PolarTransitionCocycle.indexAt (toMatrixData D) x)
    ⟨x, PolarTransitionCocycle.mem_domain_indexAt (toMatrixData D) x⟩).1

/-- The globally defined positive density equals the original local density in every supplied chart containing the point. -/
theorem polarDensity_eq_local (f : SmoothPolarFamily D) (i : ι) (x : B)
    (hi : x ∈ D.domain i) : polarDensity D f x = (f.val i ⟨x, hi⟩).1 :=
  (polar_density_overlap D f (PolarTransitionCocycle.indexAt (toMatrixData D) x) i x
    (PolarTransitionCocycle.mem_domain_indexAt (toMatrixData D) x) hi).symm

/-- Agreement with each actual local smooth density projection proves the glued positive density is globally smooth. -/
theorem contMDiff_polarDensity (f : SmoothPolarFamily D) :
    ContMDiff I 𝓘(ℝ, ℝ) n (polarDensity D f) := by
  intro x
  obtain ⟨i, hi⟩ := D.covers x
  have he : (fun y : D.domain i => polarDensity D f y) =
      (fun y : D.domain i => (f.val i y).1) := by
    funext y
    exact polarDensity_eq_local D f i y y.property
  have hs : ContMDiff I 𝓘(ℝ, ℝ) n (fun y : D.domain i => polarDensity D f y) := by
    rw [he]
    exact (f.val i).contMDiff.fst
  exact contMDiffAt_subtype_iff.mp (hs ⟨x, hi⟩)

/-- The actual glued invariant density of a compatible Clifford polar family as a bundled smooth positive-density field. -/
def polarDensityField (f : SmoothPolarFamily D) : C^n⟮I, B; 𝓘(ℝ, ℝ), PositiveDensity⟯ :=
  ⟨polarDensity D f, contMDiff_polarDensity D f⟩

/-- Each actual compatible Clifford polar family has exactly one global smooth positive-density field agreeing with every local density coordinate. -/
theorem existsUnique_polarDensityField (f : SmoothPolarFamily D) :
    ∃! r : C^n⟮I, B; 𝓘(ℝ, ℝ), PositiveDensity⟯,
      ∀ i (x : D.domain i), r x = (f.val i x).1 := by
  refine ⟨polarDensityField D f, ?_, ?_⟩
  · intro i x
    exact polarDensity_eq_local D f i x x.property
  · intro r hr
    apply ContMDiffMap.ext
    intro x
    obtain ⟨i, hi⟩ := D.covers x
    exact (hr i ⟨x, hi⟩).trans (polarDensity_eq_local D f i x hi).symm

/-- The globally smooth density of a compatible actual Clifford spinor family is constructed by genuine local quotient reconstruction and proved density gluing. -/
def spinorDensityField (psi : SmoothSpinorFamily D) : C^n⟮I, B; 𝓘(ℝ, ℝ), PositiveDensity⟯ :=
  polarDensityField D ((realizationEquiv D).symm psi)

/-- The real value of the glued Clifford spinor density equals its original actual bilinear invariant on every local chart. -/
theorem spinorDensityField_value_eq_local (psi : SmoothSpinorFamily D) (i : ι) (x : D.domain i) :
    (spinorDensityField D psi x : ℝ) = SpinorRegularity.invariantDensity (psi.val i x).val := by
  change (polarDensity D ((realizationEquiv D).symm psi) x : ℝ) = _
  rw [polarDensity_eq_local D _ i x x.property]
  exact realizationEquiv_symm_density D psi i x

/-- Compatible actual Clifford spinor invariants determine exactly one globally smooth positive-density field on the supplied base. -/
theorem existsUnique_spinorDensityField (psi : SmoothSpinorFamily D) :
    ∃! r : C^n⟮I, B; 𝓘(ℝ, ℝ), PositiveDensity⟯,
      ∀ i (x : D.domain i), (r x : ℝ) = SpinorRegularity.invariantDensity (psi.val i x).val := by
  refine ⟨spinorDensityField D psi, spinorDensityField_value_eq_local D psi, ?_⟩
  · intro r hr
    apply ContMDiffMap.ext
    intro x
    obtain ⟨i, hi⟩ := D.covers x
    apply Subtype.ext
    exact (hr i ⟨x, hi⟩).trans (spinorDensityField_value_eq_local D psi i ⟨x, hi⟩).symm

/-- Realizing a compatible actual Clifford polar family leaves its globally glued positive density exactly unchanged. -/
theorem spinorDensityField_realization (f : SmoothPolarFamily D) :
    spinorDensityField D (realizationEquiv D f) = polarDensityField D f := by
  simp only [spinorDensityField, Equiv.symm_apply_apply]

end FoliationQM.CliffordSpinCocycleFields
