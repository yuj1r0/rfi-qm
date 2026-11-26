module

public import FoliationQM.CanonicalScalarEnergy
public import FoliationQM.SpatialFisherEnergy

/-! In part (i) of v13 `thm:adm_positivity` the spatial Fisher term is
integrated inside the canonical slice Hamiltonian. On a regular chart it
is bounded pointwise by the actual Legendre energy density. Finiteness of
that energy therefore suffices for a genuine finite Fisher integral. -/

@[expose] public section
noncomputable section
namespace FoliationQM.ADMSliceHamiltonian
open MeasureTheory LorentzCoordinates LogDensityTransport OsmoticSliceFields SpatialFisherEnergy

/-- Finite canonical slice energy controls an integrable nonnegative Fisher term
and bounds its spatial integral by the integral of the original canonical density. -/
theorem finite_energy_bound (p : MassiveParameters) (t : ℝ) {ρ S : Covector → ℝ} {U : Set Spatial}
    (hU : MeasurableSet U) (hρ : ∀ y ∈ U, ContDiffAt ℝ 1 ρ (slicePoint t y))
    (hS : ∀ y ∈ U, DifferentiableAt ℝ S (slicePoint t y)) (hp : ∀ y ∈ U, 0 < ρ (slicePoint t y))
    (hH : IntegrableOn (fun y => CanonicalScalarEnergy.fieldEnergy p (ActionDensity.actionField p ρ S)
      (slicePoint t y)) U) :
    IntegrableOn (fisherDensity p (ρ ∘ slicePoint t)) U ∧
    0 ≤ energy p (ρ ∘ slicePoint t) U ∧ energy p (ρ ∘ slicePoint t) U ≤
      ∫ y in U, CanonicalScalarEnergy.fieldEnergy p (ActionDensity.actionField p ρ S) (slicePoint t y) := by
  have hF : ContinuousOn (fisherDensity p (ρ ∘ slicePoint t)) U := by
    intro y hy
    exact (continuousAt_fisherDensity p ((hρ y hy).comp y (contDiff_slicePoint t 1).contDiffAt)
      (hp y hy)).continuousWithinAt
  have hl : ∀ᵐ y ∂volume.restrict U, fisherDensity p (ρ ∘ slicePoint t) y ≤
      CanonicalScalarEnergy.fieldEnergy p (ActionDensity.actionField p ρ S) (slicePoint t y) := by
    filter_upwards [ae_restrict_mem hU] with y hy
    exact CanonicalScalarEnergy.fisherDensity_le_fieldEnergy p t (hρ y hy).differentiableAt_one (hS y hy) (hp y hy)
  have hn : ∀ᵐ y ∂volume.restrict U, 0 ≤ fisherDensity p (ρ ∘ slicePoint t) y := by
    filter_upwards [ae_restrict_mem hU] with y hy
    exact mul_nonneg (mul_nonneg (by positivity) (hp y hy).le) (speedSq_nonneg _)
  have hi := hH.mono_nonneg (hF.aestronglyMeasurable hU) hn hl
  exact ⟨hi, integral_nonneg_of_ae hn, CanonicalScalarEnergy.fisherEnergy_le_hamiltonian p t hU
    (fun y hy => (hρ y hy).differentiableAt_one) hS hp hi hH⟩

/-- Inside a finite canonical Hamiltonian, the Fisher contribution of a regular
connected open slice is positive exactly when its spatial density varies. -/
theorem positive_fisher_iff (p : MassiveParameters) (t : ℝ) {ρ S : Covector → ℝ} {U : Set Spatial}
    (hU : IsOpen U) (hc : IsPreconnected U) (hρ : ∀ y ∈ U, ContDiffAt ℝ 1 ρ (slicePoint t y))
    (hS : ∀ y ∈ U, DifferentiableAt ℝ S (slicePoint t y)) (hp : ∀ y ∈ U, 0 < ρ (slicePoint t y))
    (hH : IntegrableOn (fun y => CanonicalScalarEnergy.fieldEnergy p (ActionDensity.actionField p ρ S)
      (slicePoint t y)) U) :
    0 < energy p (ρ ∘ slicePoint t) U ↔ ∃ y ∈ U, ∃ z ∈ U, ρ (slicePoint t y) ≠ ρ (slicePoint t z) := by
  have hi := (finite_energy_bound p t hU.measurableSet hρ hS hp hH).1
  exact energy_pos_iff p hU hc (fun y hy => (hρ y hy).comp y (contDiff_slicePoint t 1).contDiffAt) hp hi

end FoliationQM.ADMSliceHamiltonian
