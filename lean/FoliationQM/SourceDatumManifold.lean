module
public import FoliationQM.SourcePolarDatum
public import FoliationQM.PolarScalarManifolds
public import FoliationQM.PolarAmplitudeManifold
public import FoliationQM.PolarDatumManifold
public import FoliationQM.SourcePolarRealization
public import FoliationQM.SmoothPolarCovering
public import FoliationQM.SourcePolarCovering
public import FoliationQM.SourceQuotientManifold
public import FoliationQM.ChiralAngleManifold
public import FoliationQM.SpecialLinearManifold
public import Mathlib.Geometry.Manifold.Diffeomorph
public import Mathlib.Geometry.Manifold.LocalDiffeomorph
public import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# The intrinsic literal source datum and its actual smooth realization

Sources: v13 `prop:takabayasi` and `eq:takabayasi_polar`. Literal source
data retain the natural product of positive density, the four-pi angle
circle, and actual determinant-one matrices. The independently proved
factor atlases supply the ordinary product atlas, whose real model has
dimension eight. Mathlib's chart-model product tags record that same
product construction without replacing any topology or chart.

The actual phase diffeomorphism, positive-square-root amplitude
reconstruction, and actual matrix-coordinate diffeomorphism assemble a
bundled diffeomorphism to the intrinsic datum manifold. Its maps are
proved to be exactly the existing source conversion and inverse; its
amplitude is literally sqrt(rho) times the half-angle phase. The earlier
independent coordinate-regularity predicate agrees with this intrinsic
source smoothness after the actual conversion.

The genuine two-pi/matrix-sign involution is smooth directly from its
intrinsic factor maps and retains its existing homeomorphism. The actual
regular-spinor realization is smooth and a local diffeomorphism, by
composition with the already proved intrinsic datum realization. Its
independently established natural covering property and exact two-point
fibers are retained. Composition with the existing natural source-quotient
diffeomorphism proves the same three properties for the literal source
sign projection, directly connecting that quotient atlas to this intrinsic
product atlas. No global real angle, global representative of the
sign quotient, or abstract Spin-group classification is assumed.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Matrix.Norms.Operator Manifold ContDiff
open Function Set Topology
namespace FoliationQM.SourceDatumManifold
open SourcePolarDatum PolarAmplitudeTopology ChiralAngleCircle ChiralAngleManifold
open SpinorMatrix PolarSignQuotient

/-- The real normed source model is the product of the density, full-angle, and intrinsic determinant-one matrix models. -/
abbrev Model := ℝ × (AngleModel × SpecialLinearCharts.Model)
/-- The actual chart codomain uses Mathlib's tagged product of the same three intrinsic factor chart spaces. -/
abbrev ChartModel := ModelProd ℝ (ModelProd AngleModel SpecialLinearCharts.Model)
/-- The source model with corners is exactly the product of the independently established intrinsic factor models. -/
abbrev model : ModelWithCorners ℝ Model ChartModel :=
  (𝓘(ℝ, ℝ)).prod ((𝓡 1).prod 𝓘(ℝ, SpecialLinearCharts.Model))

/-- The literal natural source product, with its existing product atlas, is a real manifold to every differentiability order. -/
theorem isManifold_source (n : WithTop ℕ∞) : IsManifold model n SourceDatum := inferInstance

/-- Every preferred source chart is exactly the product of the preferred density, full-angle, and determinant-one matrix charts. -/
theorem chartAt_eq (d : SourceDatum) :
    chartAt ChartModel d = (chartAt ℝ d.1).prod
      ((chartAt AngleModel d.2.1).prod (chartAt SpecialLinearCharts.Model d.2.2)) := rfl

/-- The intrinsic source model has eight real dimensions: one density, one angle, and six determinant-one matrix coordinates. -/
theorem model_finrank : Module.finrank ℝ Model = 8 := by
  simp [Model, Module.finrank_prod,
    SpecialLinearManifold.model_finrank]

/-- Actual half-angle phase conversion and product reassociation give a diffeomorphism from literal source data to density-phase pairs with the same determinant-one matrix. -/
def phaseCoordinatesDiffeomorph (n : WithTop ℕ∞) :
    Diffeomorph model ((𝓘(ℝ, ℝ)).prod (𝓡 1) |>.prod 𝓘(ℝ, SpecialLinearCharts.Model))
      SourceDatum ((PositiveDensity × Circle) × SpecialLinearMatrix) n where
  toEquiv := ((Equiv.refl PositiveDensity).prodCongr
    (phaseEquiv.toEquiv.prodCongr (Equiv.refl SpecialLinearMatrix))).trans
      (Equiv.prodAssoc PositiveDensity Circle SpecialLinearMatrix).symm
  contMDiff_toFun := by
    change ContMDiff model _ n (fun d : SourceDatum => ((d.1, phaseEquiv d.2.1), d.2.2))
    exact (contMDiff_fst.prodMk
      ((contMDiff_phaseEquiv n).comp (contMDiff_fst.comp contMDiff_snd))).prodMk
        (contMDiff_snd.comp contMDiff_snd)
  contMDiff_invFun := by
    change ContMDiff _ model n (fun d : (PositiveDensity × Circle) × SpecialLinearMatrix =>
      (d.1.1, phaseEquiv.symm d.1.2, d.2))
    exact (contMDiff_fst.comp contMDiff_fst).prodMk
      (((contMDiff_phaseEquiv_symm n).comp (contMDiff_snd.comp contMDiff_fst)).prodMk
        contMDiff_snd)

/-- The intrinsic source product is diffeomorphic to nonzero-amplitude and determinant-one matrix pairs through the actual positive-square-root phase reconstruction. -/
def amplitudeCoordinatesDiffeomorph (n : WithTop ℕ∞) :
    Diffeomorph model ((𝓘(ℝ, ℂ)).prod 𝓘(ℝ, SpecialLinearCharts.Model))
      SourceDatum (NonzeroComplex × SpecialLinearMatrix) n :=
  (phaseCoordinatesDiffeomorph n).trans
    ((PolarAmplitudeManifold.amplitudeDiffeomorph n).symm.prodCongr
      (Diffeomorph.refl 𝓘(ℝ, SpecialLinearCharts.Model) SpecialLinearMatrix n))

/-- The literal source product is genuinely diffeomorphic to the intrinsic datum manifold by its actual amplitude and matrix conversion. -/
def datumDiffeomorph (n : WithTop ℕ∞) :
    Diffeomorph model PolarDatumManifold.model SourceDatum Datum n :=
  (amplitudeCoordinatesDiffeomorph n).trans (PolarDatumManifold.coordinateDiffeomorph n).symm

/-- The bundled source-to-datum diffeomorphism is exactly the previously defined literal source conversion. -/
theorem datumDiffeomorph_apply (n : WithTop ℕ∞) (d : SourceDatum) :
    datumDiffeomorph n d = toDatum d := rfl

/-- The inverse bundled diffeomorphism is exactly the previously defined density, four-pi angle, and matrix recovery. -/
theorem datumDiffeomorph_symm_apply (n : WithTop ℕ∞) (d : Datum) :
    (datumDiffeomorph n).symm d = ofDatum d := by
  apply (datumDiffeomorph n).injective
  change datumDiffeomorph n ((datumDiffeomorph n).symm d) = datumDiffeomorph n (ofDatum d)
  rw [Diffeomorph.apply_symm_apply, datumDiffeomorph_apply, toDatum_ofDatum]

/-- The intrinsic source-to-datum diffeomorphism retains exactly the pre-existing natural-topology homeomorphism. -/
theorem datumDiffeomorph_toHomeomorph (n : WithTop ℕ∞) :
    (datumDiffeomorph n).toHomeomorph = datumHomeomorph := by
  apply Homeomorph.ext
  intro d
  exact datumDiffeomorph_apply n d

/-- The actual amplitude of the source diffeomorphism is the positive density square root times the actual half-angle unit phase. -/
theorem datumDiffeomorph_amplitude (n : WithTop ℕ∞) (d : SourceDatum) :
    (datumDiffeomorph n d).t = (Real.sqrt (d.1 : ℝ) : ℂ) * (phaseEquiv d.2.1 : ℂ) := rfl

/-- The actual source-to-datum diffeomorphism preserves the determinant-one matrix coordinate exactly. -/
theorem datumDiffeomorph_matrix (n : WithTop ℕ∞) (d : SourceDatum) :
    (datumDiffeomorph n d).A = (d.2.2 : Mat2) := rfl

/-- The existing literal source-to-datum conversion is smooth for the independently constructed intrinsic source and datum atlases. -/
theorem contMDiff_toDatum (n : WithTop ℕ∞) :
    ContMDiff model PolarDatumManifold.model n toDatum :=
  (datumDiffeomorph n).contMDiff

/-- The existing density-angle-matrix recovery is smooth for the independently constructed intrinsic datum and source atlases. -/
theorem contMDiff_ofDatum (n : WithTop ℕ∞) :
    ContMDiff PolarDatumManifold.model model n ofDatum := by
  convert (datumDiffeomorph n).symm.contMDiff using 1
  funext d
  exact (datumDiffeomorph_symm_apply n d).symm

/-- The actual realization of literal source data into regular spinors is manifold-smooth to every order. -/
theorem contMDiff_realizeSource (n : WithTop ℕ∞) :
    ContMDiff model 𝓘(ℝ, DiracMatrices.Spinor) n SourcePolarRealization.realizeSource :=
  (PolarDatumManifold.contMDiff_realize n).comp (contMDiff_toDatum n)

/-- For a real normed source, intrinsic source-field smoothness is equivalent to the earlier independent amplitude-matrix coordinate regularity of its actual datum conversion. -/
theorem contMDiffAt_iff_datumCoordinates
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : WithTop ℕ∞} {f : E → SourceDatum} {x : E} :
    ContMDiffAt 𝓘(ℝ, E) model n f x ↔
      PolarDatumSmooth.CoordinateContDiffAt n (toDatum ∘ f) x := by
  have h := (datumDiffeomorph n).contMDiffAt_diffeomorph_comp_iff
    (I' := 𝓘(ℝ, E)) (f := f) (x := x) le_rfl
  exact h.symm.trans PolarDatumManifold.contMDiffAt_iff_coordinateContDiffAt

/-- The actual simultaneous two-pi full-angle shift and matrix negation is smooth directly from its intrinsic factor maps. -/
theorem contMDiff_shiftNeg (n : WithTop ℕ∞) : ContMDiff model model n shiftNeg := by
  have hm : ContMDiff 𝓘(ℝ, SpecialLinearCharts.Model) 𝓘(ℝ, SpecialLinearCharts.Model) n
      (fun A : SpecialLinearMatrix =>
        (⟨-(A : Mat2), by simp [Matrix.det_neg, A.property]⟩ : SpecialLinearMatrix)) := by
    apply SpecialLinearManifold.contMDiff_iff_value.mpr
    exact (SpecialLinearManifold.contMDiff_value n).neg
  exact contMDiff_fst.prodMk
    (((contMDiff_shift_two_pi n).comp (contMDiff_fst.comp contMDiff_snd)).prodMk
      (hm.comp (contMDiff_snd.comp contMDiff_snd)))

/-- The existing free source sign involution is a genuine bundled diffeomorphism of the intrinsic source product manifold. -/
def shiftNegDiffeomorph (n : WithTop ℕ∞) :
    Diffeomorph model model SourceDatum SourceDatum n where
  toEquiv := shiftNegHomeomorph.toEquiv
  contMDiff_toFun := contMDiff_shiftNeg n
  contMDiff_invFun := contMDiff_shiftNeg n

/-- The bundled source sign diffeomorphism is the actual simultaneous two-pi angle shift and matrix negation. -/
theorem shiftNegDiffeomorph_apply (n : WithTop ℕ∞) (d : SourceDatum) :
    shiftNegDiffeomorph n d = shiftNeg d := rfl

/-- The bundled source sign diffeomorphism retains exactly the previously proved natural sign homeomorphism. -/
theorem shiftNegDiffeomorph_toHomeomorph (n : WithTop ℕ∞) :
    (shiftNegDiffeomorph n).toHomeomorph = shiftNegHomeomorph := rfl

/-- Actual source realization is a local diffeomorphism for the intrinsic product atlas, by the genuine source-to-datum diffeomorphism and proved datum local inverses. -/
theorem realizeSource_isLocalDiffeomorph (n : WithTop ℕ∞) :
    IsLocalDiffeomorph model 𝓘(ℝ, DiracMatrices.Spinor) n
      SourcePolarRealization.realizeSource := by
  intro d
  have h := ((datumDiffeomorph n).isLocalDiffeomorph d).comp
    𝓘(ℝ, DiracMatrices.Spinor) RegularSpinor
    (SmoothPolarCovering.realize_isLocalDiffeomorph n (datumDiffeomorph n d))
  have heq : realize ∘ (datumDiffeomorph n) = SourcePolarRealization.realizeSource := by
    funext d
    rw [Function.comp_apply, datumDiffeomorph_apply]
    rfl
  rw [heq] at h
  exact h

/-- Actual source realization simultaneously retains its natural covering property, is a local diffeomorphism to every stated order, and has exactly two points in each fiber. -/
theorem realizeSource_smooth_two_sheeted (n : WithTop ℕ∞) :
    IsCoveringMap SourcePolarRealization.realizeSource ∧
      IsLocalDiffeomorph model 𝓘(ℝ, DiracMatrices.Spinor) n
        SourcePolarRealization.realizeSource ∧
      ∀ q : RegularSpinor,
        Nat.card (SourcePolarRealization.realizeSource ⁻¹' {q}) = 2 :=
  ⟨SourcePolarCovering.realizeSource_isCoveringMap, realizeSource_isLocalDiffeomorph n,
    SourcePolarCovering.realize_fiber_card⟩

/-- The actual literal source sign projection is a local diffeomorphism for the intrinsic source product and the previously specified natural source quotient atlas. -/
theorem quotient_mk_isLocalDiffeomorph (n : WithTop ℕ∞) :
    IsLocalDiffeomorph model 𝓘(ℝ, DiracMatrices.Spinor) n
      (Quotient.mk SourcePolarQuotient.signSetoid : SourceDatum →
        SourcePolarQuotient.SourceQuotient) := by
  have heq : (SourceQuotientManifold.regularDiffeomorph n).symm ∘
      SourcePolarRealization.realizeSource =
      (Quotient.mk SourcePolarQuotient.signSetoid : SourceDatum →
        SourcePolarQuotient.SourceQuotient) := by
    funext d
    change SourcePolarQuotient.regularHomeomorph.symm
      (SourcePolarQuotient.regularHomeomorph
        (Quotient.mk SourcePolarQuotient.signSetoid d)) = _
    exact SourcePolarQuotient.regularHomeomorph.symm_apply_apply _
  intro d
  have h := (realizeSource_isLocalDiffeomorph n d).comp
    𝓘(ℝ, DiracMatrices.Spinor) SourcePolarQuotient.SourceQuotient
    ((SourceQuotientManifold.regularDiffeomorph n).symm.isLocalDiffeomorph
      (SourcePolarRealization.realizeSource d))
  rw [heq] at h
  exact h

/-- The actual literal source sign projection is manifold-smooth to every order for the intrinsic product and natural quotient atlases. -/
theorem contMDiff_quotient_mk (n : WithTop ℕ∞) :
    ContMDiff model 𝓘(ℝ, DiracMatrices.Spinor) n
      (Quotient.mk SourcePolarQuotient.signSetoid : SourceDatum →
        SourcePolarQuotient.SourceQuotient) :=
  (quotient_mk_isLocalDiffeomorph n).contMDiff

/-- The actual literal source sign projection is simultaneously a natural covering map, an intrinsic local diffeomorphism, and a map with exactly two points in every fiber. -/
theorem quotient_mk_smooth_two_sheeted (n : WithTop ℕ∞) :
    IsCoveringMap (Quotient.mk SourcePolarQuotient.signSetoid : SourceDatum →
      SourcePolarQuotient.SourceQuotient) ∧
      IsLocalDiffeomorph model 𝓘(ℝ, DiracMatrices.Spinor) n
        (Quotient.mk SourcePolarQuotient.signSetoid : SourceDatum →
          SourcePolarQuotient.SourceQuotient) ∧
      ∀ q : SourcePolarQuotient.SourceQuotient,
        Nat.card ((Quotient.mk SourcePolarQuotient.signSetoid : SourceDatum →
          SourcePolarQuotient.SourceQuotient) ⁻¹' {q}) = 2 :=
  ⟨SourcePolarCovering.quotient_mk_isCoveringMap, quotient_mk_isLocalDiffeomorph n,
    SourcePolarCovering.quotient_fiber_card⟩

end FoliationQM.SourceDatumManifold
