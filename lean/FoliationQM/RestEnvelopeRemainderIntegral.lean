module

public import FoliationQM.RestEnvelopeRemainder
public import FoliationQM.OpenIntegrationByParts

/-!
# Genuine integral bounds for the actual rest-envelope remainder

Source: v13 `cor:schrodinger`, component kinds C and D. The actual temporal
derivative and dressed KG source are integrable before any integral estimate
is used. Compact physical regions need only the original field's local C²
regularity at their actual normal-coordinate images. Finite measure factors
are retained, and no uniform family bound or limiting PDE is asserted here.
-/

@[expose] public section
noncomputable section

namespace FoliationQM.RestEnvelopeRemainderIntegral

open MeasureTheory Filter PolarSecondDifferential
open RestEnvelopeDifferential RestEnvelopeKG RestEnvelopeRemainder
open LaboratoryCoordinates LaboratoryKG
open Madelung (coordinateVector)
open scoped ContDiff Topology

/-- Multiplication by the actual inverse rest carrier preserves integrability of the dressed KG source. -/
theorem integrable_neutralizedKG (p : MassiveParameters) {u : Covector → ℂ}
    {μ : Measure Covector} (hK : Integrable (laboratoryKG p (dressedField p u)) μ) :
    Integrable (neutralizedKG p u) μ := by
  have hc : Continuous (fun x => (carrierField p x)⁻¹) :=
    (contDiff_carrierField p).continuous.inv₀ (carrierField_ne_zero p)
  exact hK.bdd_mul (c := 1) hc.aestronglyMeasurable
    (Eventually.of_forall fun x => by simp [norm_carrierField p x])

/-- True temporal and source integrability imply integrability of the actual Schrödinger residual. -/
theorem integrable_residual (p : MassiveParameters) {u : Covector → ℂ}
    {μ : Measure Covector} (hreg : ∀ᵐ x ∂μ, ContDiffAt ℝ 2 u x)
    (hD : Integrable (secondDirectionalDerivative u (coordinateVector 0)) μ)
    (hK : Integrable (laboratoryKG p (dressedField p u)) μ) :
    Integrable (schrodingerResidual p u) μ := by
  apply ((hD.const_mul (temporalCoefficient p : ℂ)).sub
    ((integrable_neutralizedKG p hK).const_mul (sourceCoefficient p : ℂ))).congr
  filter_upwards [hreg] with x hx
  have h := corrected_residual p hx
  change (temporalCoefficient p : ℂ) *
      secondDirectionalDerivative u (coordinateVector 0) x -
      (sourceCoefficient p : ℂ) * neutralizedKG p u x = schrodingerResidual p u x
  exact (eq_sub_iff_add_eq.mpr h).symm

/-- The genuine norm integral of the residual is bounded by the actual temporal and KG norm integrals. -/
theorem integral_norm_residual_le (p : MassiveParameters) {u : Covector → ℂ}
    {μ : Measure Covector} (hreg : ∀ᵐ x ∂μ, ContDiffAt ℝ 2 u x)
    (hD : Integrable (secondDirectionalDerivative u (coordinateVector 0)) μ)
    (hK : Integrable (laboratoryKG p (dressedField p u)) μ) :
    (∫ x, ‖schrodingerResidual p u x‖ ∂μ) ≤
      temporalCoefficient p * (∫ x, ‖secondDirectionalDerivative u (coordinateVector 0) x‖ ∂μ) +
      sourceCoefficient p * (∫ x, ‖laboratoryKG p (dressedField p u) x‖ ∂μ) := by
  have hR := integrable_residual p hreg hD hK
  have h := integral_mono_ae hR.norm
    ((hD.norm.const_mul (temporalCoefficient p)).add
      (hK.norm.const_mul (sourceCoefficient p)))
    (hreg.mono fun x hx => norm_residual_le p hx)
  simpa only [Pi.add_apply, integral_add (hD.norm.const_mul _) (hK.norm.const_mul _),
    integral_const_mul] using! h

/-- For an actual homogeneous KG field, residual integrability and its exact norm integral follow from the temporal derivative. -/
theorem integrable_residual_and_norm_integral_of_KG (p : MassiveParameters)
    {u : Covector → ℂ} {μ : Measure Covector}
    (hreg : ∀ᵐ x ∂μ, ContDiffAt ℝ 2 u x)
    (hD : Integrable (secondDirectionalDerivative u (coordinateVector 0)) μ)
    (hKG : ∀ᵐ x ∂μ, laboratoryKG p (dressedField p u) x = 0) :
    Integrable (schrodingerResidual p u) μ ∧
      (∫ x, ‖schrodingerResidual p u x‖ ∂μ) =
        temporalCoefficient p *
          (∫ x, ‖secondDirectionalDerivative u (coordinateVector 0) x‖ ∂μ) := by
  have hK : Integrable (laboratoryKG p (dressedField p u)) μ :=
    (integrable_zero _ _ μ).congr (hKG.mono fun x hx => hx.symm)
  refine ⟨integrable_residual p hreg hD hK, ?_⟩
  calc
    (∫ x, ‖schrodingerResidual p u x‖ ∂μ) =
        ∫ x, temporalCoefficient p *
          ‖secondDirectionalDerivative u (coordinateVector 0) x‖ ∂μ := by
      apply integral_congr_ae
      filter_upwards [hreg, hKG] with x hx hk
      exact norm_residual_of_KG p hx hk
    _ = _ := integral_const_mul _ _

/-- A measurable bounded actual temporal derivative on a finite measure gives the residual bound with the exact measure mass. -/
theorem integral_norm_residual_le_of_bound (p : MassiveParameters)
    {u : Covector → ℂ} {μ : Measure Covector} [IsFiniteMeasure μ]
    (hreg : ∀ᵐ x ∂μ, ContDiffAt ℝ 2 u x)
    (hKG : ∀ᵐ x ∂μ, laboratoryKG p (dressedField p u) x = 0)
    (hDmeas : AEStronglyMeasurable (secondDirectionalDerivative u (coordinateVector 0)) μ)
    {M : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ᵐ x ∂μ, ‖secondDirectionalDerivative u (coordinateVector 0) x‖ ≤ M) :
    Integrable (secondDirectionalDerivative u (coordinateVector 0)) μ ∧
      Integrable (schrodingerResidual p u) μ ∧
      (∫ x, ‖schrodingerResidual p u x‖ ∂μ) ≤
        temporalCoefficient p * M * μ.real Set.univ := by
  have hD : Integrable (secondDirectionalDerivative u (coordinateVector 0)) μ :=
    (integrable_const M).mono hDmeas (hbound.mono fun x hx => by
      simpa only [Real.norm_eq_abs, abs_of_nonneg hM] using hx)
  obtain ⟨hR, heq⟩ := integrable_residual_and_norm_integral_of_KG p hreg hD hKG
  refine ⟨hD, hR, ?_⟩
  have h := mul_le_mul_of_nonneg_left
    (integral_mono_ae hD.norm (integrable_const M) hbound) (temporalCoefficient_nonneg p)
  rw [heq]
  simpa only [integral_const, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using h

private theorem integrableOn_source_data (p : MassiveParameters) {ψ : Covector → ℂ}
    {K : Set Covector} (hK : IsCompact K)
    (hψ : ∀ x ∈ K, ContDiffAt ℝ 2 ψ (toNormal p.c x)) :
    IntegrableOn (secondDirectionalDerivative (envelope p ψ) (coordinateVector 0)) K ∧
      IntegrableOn (fun x => FlatIntegrationByParts.kgOperator p ψ coordinateVector
        (toNormal p.c x)) K := by
  constructor
  · apply ContinuousOn.integrableOn_compact hK
    intro x hx
    exact ((OpenIntegrationByParts.contDiffAt_directionalDerivative
      (contDiffAt_envelope p (hψ x hx)) (coordinateVector 0)).fderiv_right
      (m := 0) (by norm_num)).continuousAt.clm_apply continuousAt_const
      |>.continuousWithinAt
  · apply ContinuousOn.integrableOn_compact hK
    intro x hx
    have hc := ((OpenIntegrationByParts.continuousAt_box (hψ x hx)
      coordinateVector).const_mul ((p.hbar : ℂ) ^ 2)).add
        ((hψ x hx).continuousAt.const_mul ((p.m : ℂ) ^ 2 * (p.c : ℂ) ^ 2))
    exact (hc.comp (toNormal p.c).continuous.continuousAt).continuousWithinAt

private theorem source_kg_ae (p : MassiveParameters) {ψ : Covector → ℂ}
    {K : Set Covector} (hK : MeasurableSet K)
    (hψ : ∀ x ∈ K, ContDiffAt ℝ 2 ψ (toNormal p.c x)) :
    laboratoryKG p (dressedField p (envelope p ψ)) =ᵐ[volume.restrict K]
      (fun x => FlatIntegrationByParts.kgOperator p ψ coordinateVector (toNormal p.c x)) := by
  apply ae_restrict_of_forall_mem hK
  intro x hx
  rw [dressedField_envelope]
  exact laboratoryKG_pullback p (hψ x hx)

/-- Original local C² regularity on a compact physical region gives all genuine source integrals and the exact inhomogeneous norm bound. -/
theorem integrableOn_source_remainder_and_bound (p : MassiveParameters)
    {ψ : Covector → ℂ} {K : Set Covector} (hK : IsCompact K)
    (hψ : ∀ x ∈ K, ContDiffAt ℝ 2 ψ (toNormal p.c x)) :
    IntegrableOn (secondDirectionalDerivative (envelope p ψ) (coordinateVector 0)) K ∧
      IntegrableOn (fun x => FlatIntegrationByParts.kgOperator p ψ coordinateVector
        (toNormal p.c x)) K ∧
      IntegrableOn (schrodingerResidual p (envelope p ψ)) K ∧
      (∫ x in K, ‖schrodingerResidual p (envelope p ψ) x‖) ≤
        temporalCoefficient p *
          (∫ x in K, ‖secondDirectionalDerivative (envelope p ψ) (coordinateVector 0) x‖) +
        sourceCoefficient p *
          (∫ x in K, ‖FlatIntegrationByParts.kgOperator p ψ coordinateVector (toNormal p.c x)‖) := by
  obtain ⟨hD, hG⟩ := integrableOn_source_data p hK hψ
  have heq := source_kg_ae p hK.measurableSet hψ
  have hKG := hG.congr heq.symm
  have hreg := ae_restrict_of_forall_mem (μ := volume) hK.measurableSet
    (fun x hx => contDiffAt_envelope p (hψ x hx))
  refine ⟨hD, hG, integrable_residual p hreg hD hKG, ?_⟩
  have h := integral_norm_residual_le p hreg hD hKG
  rw [integral_congr_ae (heq.mono fun x hx => congrArg norm hx)] at h
  exact h

/-- An actual original KG field with a compact-region temporal bound has a genuine residual integral bounded by the region's volume. -/
theorem integral_norm_source_remainder_le_of_bound (p : MassiveParameters)
    {ψ : Covector → ℂ} {K : Set Covector} (hK : IsCompact K)
    (hψ : ∀ x ∈ K, ContDiffAt ℝ 2 ψ (toNormal p.c x))
    (hKG : ∀ x ∈ K,
      FlatIntegrationByParts.kgOperator p ψ coordinateVector (toNormal p.c x) = 0)
    {M : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ x ∈ K,
      ‖secondDirectionalDerivative (envelope p ψ) (coordinateVector 0) x‖ ≤ M) :
    IntegrableOn (schrodingerResidual p (envelope p ψ)) K ∧
      (∫ x in K, ‖schrodingerResidual p (envelope p ψ) x‖) ≤
        temporalCoefficient p * M * volume.real K := by
  have : IsFiniteMeasure (volume.restrict K) := isFiniteMeasure_restrict.mpr hK.measure_ne_top
  have hD := (integrableOn_source_data p hK hψ).1
  have heq := source_kg_ae p hK.measurableSet hψ
  have hzero := ae_restrict_of_forall_mem (μ := volume) hK.measurableSet hKG
  have hk : ∀ᵐ x ∂volume.restrict K,
      laboratoryKG p (dressedField p (envelope p ψ)) x = 0 := heq.trans hzero
  have hreg := ae_restrict_of_forall_mem (μ := volume) hK.measurableSet
    (fun x hx => contDiffAt_envelope p (hψ x hx))
  obtain ⟨_, hR, h⟩ := integral_norm_residual_le_of_bound p hreg hk
    hD.aestronglyMeasurable hM (ae_restrict_of_forall_mem hK.measurableSet hbound)
  exact ⟨hR, by simpa only [measureReal_restrict_apply_univ] using h⟩

end FoliationQM.RestEnvelopeRemainderIntegral
