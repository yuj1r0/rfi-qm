module
public import FoliationQM.DensityFrameManifold
public import FoliationQM.PolarNoGlobalSection

/-!
# The global individual-frame obstruction after separating density

Source: the simultaneous sign identification in v13 `prop:takabayasi`.
The earlier explicit loop obstruction applies also to the intrinsic frame
factor. A global continuous frame representative would, together with the
actual recovered density, give a global continuous literal source lift.
This contradicts the already proved loop obstruction. The conclusions
concern individual representatives; the global quotient-valued polar
inverse remains a genuine diffeomorphism.
-/

@[expose] public section
noncomputable section
open scoped Matrix.Norms.Operator Manifold
open Function Topology
namespace FoliationQM.FrameRepresentativeObstruction
open SourcePolarProductQuotient SourcePolarDatum PolarAmplitudeTopology
open PolarSignQuotient

/-- The natural frame-sign quotient has no global continuous individual representative, as such a representative would contradict the actual polar loop obstruction. -/
theorem no_continuous_frame_section :
    ¬ ∃ s : FrameQuotient → FrameDatum, Continuous s ∧
      RightInverse s (Quotient.mk frameSetoid) := by
  rintro ⟨s, hs, hr⟩
  apply PolarNoGlobalSection.no_continuous_source_section
  let f : RegularSpinor → SourceDatum := fun q =>
    ((productRegularHomeomorph.symm q).1, s (productRegularHomeomorph.symm q).2)
  refine ⟨f, ?_, ?_⟩
  · exact (continuous_fst.comp productRegularHomeomorph.symm.continuous).prodMk
      (hs.comp (continuous_snd.comp productRegularHomeomorph.symm.continuous))
  · intro q
    change SourcePolarRealization.realizeSource
      ((productRegularHomeomorph.symm q).1, s (productRegularHomeomorph.symm q).2) = q
    rw [← productRegularHomeomorph_mk, hr]
    exact productRegularHomeomorph.apply_symm_apply q

/-- No differentiability order, including order zero, admits a global smooth individual frame section for the actual intrinsic quotient projection. -/
theorem no_contMDiff_frame_section (n : WithTop ℕ∞) :
    ¬ ∃ s : FrameQuotient → FrameDatum,
      ContMDiff FrameDatumManifold.model FrameDatumManifold.model n s ∧
        RightInverse s (Quotient.mk frameSetoid) := by
  rintro ⟨s, hs, hr⟩
  exact no_continuous_frame_section ⟨s, hs.continuous, hr⟩

/-- A frame representative cannot be selected continuously on the entire positive-density/frame-quotient product; restricting to density one would give a forbidden global frame section. -/
theorem no_continuous_product_frameRepresentative :
    ¬ ∃ s : DensityFrameManifold.Product → FrameDatum, Continuous s ∧
      ∀ p, Quotient.mk frameSetoid (s p) = p.2 := by
  rintro ⟨s, hs, hr⟩
  apply no_continuous_frame_section
  refine ⟨fun q => s ((⟨1, by norm_num⟩ : PositiveDensity), q),
    hs.comp (continuous_const.prodMk continuous_id), ?_⟩
  intro q
  exact hr _

/-- The arbitrary representative used only to choose intrinsic chart centers is not a global continuous frame representative. -/
theorem not_continuous_frameOut :
    ¬ Continuous (Quotient.out : FrameQuotient → FrameDatum) := by
  intro h
  exact no_continuous_frame_section ⟨Quotient.out, h, Quotient.out_eq⟩

end FoliationQM.FrameRepresentativeObstruction
