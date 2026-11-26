module

public import Mathlib.MeasureTheory.Function.Jacobian
public import Mathlib.MeasureTheory.Integral.IntegrableOn

/-!
# Weighted transport from actual Jacobian change of variables

An injective differentiable map on a measurable carrying set transports
the density determined by its actual absolute Jacobian to the density on
its image. Regional measurability suffices. Actual real integrability is
preserved separately, and a fixed-domain conclusion uses a genuine image
identity derived from forward and right-inverse preservation.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.WeightedJacobianPushforward

open Set Filter MeasureTheory MeasureTheory.Measure
open scoped ENNReal Topology

/-- The restricted positive-part density measure; physical nonnegativity is a separate geometric fact. -/
def weightedDensity {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (S : Set α) (D : α → ℝ) : Measure α :=
  (μ.restrict S).withDensity (fun x => ENNReal.ofReal (D x))

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [IsAddHaarMeasure μ]
  {S : Set E} {Phi : E → E} {J : E → E →L[ℝ] E} {D0 Dt : E → ℝ}

omit [FiniteDimensional ℝ E] [IsAddHaarMeasure μ] in
/-- The actual differentiable map is almost everywhere measurable under the source density measure. -/
theorem aemeasurable_weighted_map (hs : MeasurableSet S)
    (hPhi : ∀ x ∈ S, HasFDerivWithinAt Phi (J x) S x) (D0 : E → ℝ) :
    AEMeasurable Phi (weightedDensity μ S D0) := by
  have hc : ContinuousOn Phi S := fun x hx => (hPhi x hx).continuousWithinAt
  exact (hc.aemeasurable hs).mono_ac
    (withDensity_absolutelyContinuous (μ.restrict S) (fun x => ENNReal.ofReal (D0 x)))

/-- Genuine Jacobian change of variables and the derived density law give the actual weighted pushforward. -/
theorem map_weightedDensity_of_density_jacobian (hs : MeasurableSet S)
    (hPhi : ∀ x ∈ S, HasFDerivWithinAt Phi (J x) S x) (hinj : InjOn Phi S)
    (hD0 : AEMeasurable D0 (μ.restrict S))
    (hDt : AEMeasurable Dt (μ.restrict (Phi '' S)))
    (hLaw : ∀ᵐ x ∂μ.restrict S, D0 x = |(J x).det| * Dt (Phi x)) :
    (weightedDensity μ S D0).map Phi = weightedDensity μ (Phi '' S) Dt := by
  have hc : ContinuousOn Phi S := fun x hx => (hPhi x hx).continuousWithinAt
  have hMap := aemeasurable_weighted_map μ hs hPhi D0
  apply Measure.ext_of_lintegral
  intro H hH
  rw [lintegral_map' hH.aemeasurable hMap]
  change (∫⁻ x, H (Phi x) ∂(μ.restrict S).withDensity (fun x => ENNReal.ofReal (D0 x))) =
    ∫⁻ x, H x ∂(μ.restrict (Phi '' S)).withDensity (fun x => ENNReal.ofReal (Dt x))
  have hHPhi : AEMeasurable (fun x => H (Phi x)) (μ.restrict S) := by
    simpa only [Function.comp_def] using hH.comp_aemeasurable (hc.aemeasurable hs)
  rw [lintegral_withDensity_eq_lintegral_mul₀ hD0.ennreal_ofReal hHPhi,
    lintegral_withDensity_eq_lintegral_mul₀ hDt.ennreal_ofReal hH.aemeasurable,
    lintegral_image_eq_lintegral_abs_det_fderiv_mul μ hs hPhi hinj]
  apply lintegral_congr_ae
  filter_upwards [hLaw] with x hx
  simp only [Pi.mul_apply, hx, ENNReal.ofReal_mul (abs_nonneg _), mul_assoc]

/-- The actual weighted pushforward preserves the full extended mass, without a finiteness assumption. -/
theorem total_mass_eq (hs : MeasurableSet S)
    (hPhi : ∀ x ∈ S, HasFDerivWithinAt Phi (J x) S x) (hinj : InjOn Phi S)
    (hD0 : AEMeasurable D0 (μ.restrict S))
    (hDt : AEMeasurable Dt (μ.restrict (Phi '' S)))
    (hLaw : ∀ᵐ x ∂μ.restrict S, D0 x = |(J x).det| * Dt (Phi x)) :
    weightedDensity μ (Phi '' S) Dt univ = weightedDensity μ S D0 univ := by
  rw [← map_weightedDensity_of_density_jacobian μ hs hPhi hinj hD0 hDt hLaw,
    Measure.map_apply_of_aemeasurable (aemeasurable_weighted_map μ hs hPhi D0)
      MeasurableSet.univ]
  rfl

/-- Genuine initial integrability and the actual real density law give genuine target integrability. -/
theorem integrableOn_image_of_density_jacobian (hs : MeasurableSet S)
    (hPhi : ∀ x ∈ S, HasFDerivWithinAt Phi (J x) S x) (hinj : InjOn Phi S)
    (hInitial : IntegrableOn D0 S μ)
    (hLaw : ∀ᵐ x ∂μ.restrict S, D0 x = |(J x).det| * Dt (Phi x)) :
    IntegrableOn Dt (Phi '' S) μ := by
  apply (integrableOn_image_iff_integrableOn_abs_det_fderiv_smul μ hs hPhi hinj Dt).mpr
  apply hInitial.congr
  filter_upwards [hLaw] with x hx
  simpa only [smul_eq_mul] using hx

/-- The actual change of variables conserves the real flux and certifies its target integrability. -/
theorem integrableOn_image_and_integral_eq_initial (hs : MeasurableSet S)
    (hPhi : ∀ x ∈ S, HasFDerivWithinAt Phi (J x) S x) (hinj : InjOn Phi S)
    (hInitial : IntegrableOn D0 S μ)
    (hLaw : ∀ᵐ x ∂μ.restrict S, D0 x = |(J x).det| * Dt (Phi x)) :
    IntegrableOn Dt (Phi '' S) μ ∧ (∫ y in Phi '' S, Dt y ∂μ) = ∫ x in S, D0 x ∂μ := by
  refine ⟨integrableOn_image_of_density_jacobian μ hs hPhi hinj hInitial hLaw, ?_⟩
  rw [integral_image_eq_integral_abs_det_fderiv_smul μ hs hPhi hinj Dt]
  apply integral_congr_ae
  filter_upwards [hLaw] with x hx
  simpa only [smul_eq_mul] using hx.symm

/-- Actual forward preservation and a region-preserving right inverse give equality with the whole region. -/
theorem image_eq_of_forward_inverse_preservation {α : Type*} {S : Set α} {Phi psi : α → α}
    (hforward : MapsTo Phi S S) (hback : MapsTo psi S S)
    (hright : ∀ y ∈ S, Phi (psi y) = y) : Phi '' S = S := by
  apply Subset.antisymm
  · rintro y ⟨x, hx, rfl⟩
    exact hforward hx
  · intro y hy
    exact ⟨psi y, hback hy, hright y hy⟩

/-- A literal image identity turns the derived moving-image law into the full fixed-domain law. -/
theorem map_weightedDensity_of_image_eq (hs : MeasurableSet S)
    (hPhi : ∀ x ∈ S, HasFDerivWithinAt Phi (J x) S x) (hinj : InjOn Phi S)
    (hD0 : AEMeasurable D0 (μ.restrict S)) (hDt : AEMeasurable Dt (μ.restrict S))
    (hLaw : ∀ᵐ x ∂μ.restrict S, D0 x = |(J x).det| * Dt (Phi x))
    (hImage : Phi '' S = S) :
    (weightedDensity μ S D0).map Phi = weightedDensity μ S Dt := by
  have htarget : AEMeasurable Dt (μ.restrict (Phi '' S)) := by rwa [hImage]
  simpa only [hImage] using
    map_weightedDensity_of_density_jacobian μ hs hPhi hinj hD0 htarget hLaw

/-- Actual forward and inverse preservation establish the full fixed-domain weighted transport law. -/
theorem map_weightedDensity_of_forward_inverse_preservation (hs : MeasurableSet S)
    (hPhi : ∀ x ∈ S, HasFDerivWithinAt Phi (J x) S x) (hinj : InjOn Phi S)
    (hD0 : AEMeasurable D0 (μ.restrict S)) (hDt : AEMeasurable Dt (μ.restrict S))
    (hLaw : ∀ᵐ x ∂μ.restrict S, D0 x = |(J x).det| * Dt (Phi x))
    {psi : E → E} (hforward : MapsTo Phi S S) (hback : MapsTo psi S S)
    (hright : ∀ y ∈ S, Phi (psi y) = y) :
    (weightedDensity μ S D0).map Phi = weightedDensity μ S Dt :=
  map_weightedDensity_of_image_eq μ hs hPhi hinj hD0 hDt hLaw
    (image_eq_of_forward_inverse_preservation hforward hback hright)

end FoliationQM.WeightedJacobianPushforward
