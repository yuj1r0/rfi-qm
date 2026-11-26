module
public import FoliationQM.SourceDatumManifold
public import FoliationQM.PolarNoGlobalSection
public import Mathlib.Geometry.Manifold.LocalDiffeomorph

/-!
# Actual tangent equivalences and global representative obstructions

Sources: the concrete regular polar quotient in v13 `prop:takabayasi`
and `eq:takabayasi_polar`. Each of the four actual two-sheeted covering
maps has already been proved to be a local diffeomorphism for its stated
intrinsic source and target atlases. At every nonzero differentiability
order, its actual manifold Frechet derivative therefore forms a
continuous-linear equivalence of tangent spaces. The underlying maps
are proved equal to the actual `mfderiv` maps, and their invertibility
is stated explicitly. Every involved tangent space has real dimension
eight, as follows from the independently verified model dimensions.

These local tangent equivalences supply no global individual polar
representative. The previously proved explicit-loop obstruction to a
continuous section also excludes every global manifold-smooth section,
including order zero, for amplitude realization, amplitude sign
projection, literal source realization, and literal source sign
projection. This concerns the concrete polar two-sheeted covering; no
abstract Spin-to-Lorentz covering, principal-bundle classification, or
field equation is assumed or claimed.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Matrix.Norms.Operator Manifold
namespace FoliationQM.PolarCoveringDifferential
open DiracMatrices PolarSignQuotient SourcePolarDatum

/-- At nonzero differentiability order, the actual derivative of datum realization is a continuous-linear equivalence between its source and realized-spinor tangent spaces. -/
def realizeTangentEquiv (n : WithTop ℕ∞) (hn : n ≠ 0) (d : Datum) :
    TangentSpace PolarDatumManifold.model d ≃L[ℝ]
      TangentSpace 𝓘(ℝ, Spinor) (realize d) :=
  (SmoothPolarCovering.realize_isLocalDiffeomorph n).mfderivToContinuousLinearEquiv hn d

/-- The packaged realization tangent equivalence has exactly the actual manifold Frechet derivative as its underlying continuous-linear map. -/
theorem realizeTangentEquiv_toContinuousLinearMap (n : WithTop ℕ∞) (hn : n ≠ 0) (d : Datum) :
    (realizeTangentEquiv n hn d).toContinuousLinearMap =
      mfderiv PolarDatumManifold.model 𝓘(ℝ, Spinor) realize d :=
  (SmoothPolarCovering.realize_isLocalDiffeomorph n).mfderivToContinuousLinearEquiv_coe hn d

/-- The actual manifold Frechet derivative of datum realization is invertible at every datum when the stated differentiability order is nonzero. -/
theorem realize_mfderiv_isInvertible (n : WithTop ℕ∞) (hn : n ≠ 0) (d : Datum) :
    (mfderiv PolarDatumManifold.model 𝓘(ℝ, Spinor) realize d).IsInvertible :=
  (SmoothPolarCovering.realize_isLocalDiffeomorph n).isInvertible_mfderiv hn d

/-- At nonzero differentiability order, the actual derivative of the amplitude sign projection is a continuous-linear equivalence of its actual tangent spaces. -/
def quotientTangentEquiv (n : WithTop ℕ∞) (hn : n ≠ 0) (d : Datum) :
    TangentSpace PolarDatumManifold.model d ≃L[ℝ]
      TangentSpace 𝓘(ℝ, Spinor) (Quotient.mk signSetoid d) :=
  (SmoothPolarCovering.quotient_mk_isLocalDiffeomorph n).mfderivToContinuousLinearEquiv hn d

/-- The packaged amplitude-quotient tangent equivalence has exactly the actual derivative of the existing quotient projection as its underlying map. -/
theorem quotientTangentEquiv_toContinuousLinearMap (n : WithTop ℕ∞) (hn : n ≠ 0) (d : Datum) :
    (quotientTangentEquiv n hn d).toContinuousLinearMap =
      mfderiv PolarDatumManifold.model 𝓘(ℝ, Spinor)
        (Quotient.mk signSetoid : Datum → PolarQuotient) d :=
  (SmoothPolarCovering.quotient_mk_isLocalDiffeomorph n).mfderivToContinuousLinearEquiv_coe hn d

/-- The actual derivative of the amplitude sign projection is invertible at every datum for every stated nonzero differentiability order. -/
theorem quotient_mfderiv_isInvertible (n : WithTop ℕ∞) (hn : n ≠ 0) (d : Datum) :
    (mfderiv PolarDatumManifold.model 𝓘(ℝ, Spinor)
      (Quotient.mk signSetoid : Datum → PolarQuotient) d).IsInvertible :=
  (SmoothPolarCovering.quotient_mk_isLocalDiffeomorph n).isInvertible_mfderiv hn d

/-- At nonzero differentiability order, the actual derivative of literal density-angle-matrix realization is a continuous-linear equivalence of its actual tangent spaces. -/
def sourceRealizeTangentEquiv (n : WithTop ℕ∞) (hn : n ≠ 0) (d : SourceDatum) :
    TangentSpace SourceDatumManifold.model d ≃L[ℝ]
      TangentSpace 𝓘(ℝ, Spinor) (SourcePolarRealization.realizeSource d) :=
  (SourceDatumManifold.realizeSource_isLocalDiffeomorph n).mfderivToContinuousLinearEquiv hn d

/-- The literal-source realization tangent equivalence has exactly the actual manifold Frechet derivative as its underlying continuous-linear map. -/
theorem sourceRealizeTangentEquiv_toContinuousLinearMap
    (n : WithTop ℕ∞) (hn : n ≠ 0) (d : SourceDatum) :
    (sourceRealizeTangentEquiv n hn d).toContinuousLinearMap =
      mfderiv SourceDatumManifold.model 𝓘(ℝ, Spinor) SourcePolarRealization.realizeSource d :=
  (SourceDatumManifold.realizeSource_isLocalDiffeomorph n).mfderivToContinuousLinearEquiv_coe hn d

/-- The actual derivative of literal source realization is invertible at every source datum for every stated nonzero differentiability order. -/
theorem sourceRealize_mfderiv_isInvertible (n : WithTop ℕ∞) (hn : n ≠ 0) (d : SourceDatum) :
    (mfderiv SourceDatumManifold.model 𝓘(ℝ, Spinor)
      SourcePolarRealization.realizeSource d).IsInvertible :=
  (SourceDatumManifold.realizeSource_isLocalDiffeomorph n).isInvertible_mfderiv hn d

/-- At nonzero differentiability order, the actual derivative of the literal source sign projection is a continuous-linear equivalence of its actual tangent spaces. -/
def sourceQuotientTangentEquiv (n : WithTop ℕ∞) (hn : n ≠ 0) (d : SourceDatum) :
    TangentSpace SourceDatumManifold.model d ≃L[ℝ]
      TangentSpace 𝓘(ℝ, Spinor) (Quotient.mk SourcePolarQuotient.signSetoid d) :=
  (SourceDatumManifold.quotient_mk_isLocalDiffeomorph n).mfderivToContinuousLinearEquiv hn d

/-- The literal source-quotient tangent equivalence has exactly the actual derivative of the existing source quotient projection as its underlying map. -/
theorem sourceQuotientTangentEquiv_toContinuousLinearMap
    (n : WithTop ℕ∞) (hn : n ≠ 0) (d : SourceDatum) :
    (sourceQuotientTangentEquiv n hn d).toContinuousLinearMap =
      mfderiv SourceDatumManifold.model 𝓘(ℝ, Spinor)
        (Quotient.mk SourcePolarQuotient.signSetoid : SourceDatum →
          SourcePolarQuotient.SourceQuotient) d :=
  (SourceDatumManifold.quotient_mk_isLocalDiffeomorph n).mfderivToContinuousLinearEquiv_coe hn d

/-- The actual derivative of the literal source sign projection is invertible at every source datum for every stated nonzero differentiability order. -/
theorem sourceQuotient_mfderiv_isInvertible (n : WithTop ℕ∞) (hn : n ≠ 0) (d : SourceDatum) :
    (mfderiv SourceDatumManifold.model 𝓘(ℝ, Spinor)
      (Quotient.mk SourcePolarQuotient.signSetoid : SourceDatum →
        SourcePolarQuotient.SourceQuotient) d).IsInvertible :=
  (SourceDatumManifold.quotient_mk_isLocalDiffeomorph n).isInvertible_mfderiv hn d

/-- Every tangent space of the intrinsic nonzero-amplitude and determinant-one-matrix datum manifold has real dimension eight. -/
theorem datum_tangent_finrank (d : Datum) :
    Module.finrank ℝ (TangentSpace PolarDatumManifold.model d) = 8 := by
  change Module.finrank ℝ PolarDatumManifold.Model = 8
  exact PolarDatumManifold.model_finrank

/-- Every tangent space of the actual strict regular-spinor manifold has real dimension eight. -/
theorem regular_tangent_finrank (q : RegularSpinor) :
    Module.finrank ℝ (TangentSpace 𝓘(ℝ, Spinor) q) = 8 := by
  change Module.finrank ℝ Spinor = 8
  exact RegularSpinorManifold.model_finrank

/-- Every tangent space of the natural amplitude sign-quotient manifold has real dimension eight. -/
theorem quotient_tangent_finrank (q : PolarQuotient) :
    Module.finrank ℝ (TangentSpace 𝓘(ℝ, Spinor) q) = 8 := by
  change Module.finrank ℝ Spinor = 8
  exact RegularSpinorManifold.model_finrank

/-- Every tangent space of the intrinsic literal density, four-pi-angle and determinant-one-matrix manifold has real dimension eight. -/
theorem sourceDatum_tangent_finrank (d : SourceDatum) :
    Module.finrank ℝ (TangentSpace SourceDatumManifold.model d) = 8 := by
  change Module.finrank ℝ SourceDatumManifold.Model = 8
  exact SourceDatumManifold.model_finrank

/-- Every tangent space of the natural literal source sign-quotient manifold has real dimension eight. -/
theorem sourceQuotient_tangent_finrank (q : SourcePolarQuotient.SourceQuotient) :
    Module.finrank ℝ (TangentSpace 𝓘(ℝ, Spinor) q) = 8 := by
  change Module.finrank ℝ Spinor = 8
  exact RegularSpinorManifold.model_finrank

/-- Actual datum realization has no global manifold-smooth individual-representative section at any differentiability order, including zero. -/
theorem no_contMDiff_realize_section (n : WithTop ℕ∞) :
    ¬ ∃ s : RegularSpinor → Datum,
      ContMDiff 𝓘(ℝ, Spinor) PolarDatumManifold.model n s ∧
      Function.RightInverse s realize := by
  rintro ⟨s, hs, hr⟩
  exact PolarNoGlobalSection.no_continuous_section ⟨s, hs.continuous, hr⟩

/-- The actual amplitude sign projection has no global manifold-smooth individual-representative section at any differentiability order. -/
theorem no_contMDiff_quotient_section (n : WithTop ℕ∞) :
    ¬ ∃ s : PolarQuotient → Datum,
      ContMDiff 𝓘(ℝ, Spinor) PolarDatumManifold.model n s ∧
      Function.RightInverse s (Quotient.mk signSetoid) := by
  rintro ⟨s, hs, hr⟩
  exact PolarNoGlobalSection.no_continuous_quotient_section ⟨s, hs.continuous, hr⟩

/-- Actual literal-source realization has no global manifold-smooth individual-representative section at any differentiability order. -/
theorem no_contMDiff_sourceRealize_section (n : WithTop ℕ∞) :
    ¬ ∃ s : RegularSpinor → SourceDatum,
      ContMDiff 𝓘(ℝ, Spinor) SourceDatumManifold.model n s ∧
      Function.RightInverse s SourcePolarRealization.realizeSource := by
  rintro ⟨s, hs, hr⟩
  exact PolarNoGlobalSection.no_continuous_source_section ⟨s, hs.continuous, hr⟩

/-- The actual literal source sign projection has no global manifold-smooth individual-representative section at any differentiability order. -/
theorem no_contMDiff_sourceQuotient_section (n : WithTop ℕ∞) :
    ¬ ∃ s : SourcePolarQuotient.SourceQuotient → SourceDatum,
      ContMDiff 𝓘(ℝ, Spinor) SourceDatumManifold.model n s ∧
      Function.RightInverse s (Quotient.mk SourcePolarQuotient.signSetoid) := by
  rintro ⟨s, hs, hr⟩
  apply PolarNoGlobalSection.no_continuous_source_section
  refine ⟨s ∘ SourcePolarQuotient.regularHomeomorph.symm,
    hs.continuous.comp SourcePolarQuotient.regularHomeomorph.symm.continuous, ?_⟩
  intro q
  have h := congrArg SourcePolarQuotient.regularHomeomorph
    (hr (SourcePolarQuotient.regularHomeomorph.symm q))
  simpa only [SourcePolarQuotient.regularHomeomorph_apply_mk,
    Homeomorph.apply_symm_apply, Function.comp_apply, SourcePolarRealization.realizeSource] using h

end FoliationQM.PolarCoveringDifferential
