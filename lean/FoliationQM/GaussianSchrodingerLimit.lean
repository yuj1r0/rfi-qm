module

public import FoliationQM.GaussianSpectralMoments
public import FoliationQM.SpectralSchrodingerLimit
public import FoliationQM.NonrelativisticParameterFamily

/-!
# The actual fixed-width Gaussian Klein–Gordon limit

Source: v13 `cor:schrodinger`, component kinds C and D. The existing Gaussian
spectrum is fixed while the actual positive speed ramp diverges. Its original
KG packets and their physical rest envelopes converge to the same-spectrum
Schrödinger field, with the same initial Gaussian and all proved controls.
-/

@[expose] public section
noncomputable section

namespace FoliationQM.GaussianSchrodingerLimit

open Filter Set LorentzCoordinates PolarSecondDifferential
open ReducedMassShellFrequency NonrelativisticParameterFamily
open RestEnvelopeKG LaboratoryKG SpectralEnvelopeEstimates
open GaussianPositiveFrequencyPacket
open Madelung (coordinateVector)
open OsmoticSliceFields (slicePoint)
open scoped Topology ContDiff

/-- The original Gaussian KG packets at one fixed width along the actual positive speed ramp. -/
def originalFamily (p : MassiveParameters) (σ : ℝ) (n : ℕ) : Covector → ℂ :=
  packet ((ramp p n).m * (ramp p n).c / (ramp p n).hbar) σ

/-- The actual Schrödinger-frequency graph wave with the same fixed Gaussian spectrum. -/
def limitField (p : MassiveParameters) (σ : ℝ) : Covector → ℂ :=
  FrequencyGraphFourier.wave (schrodingerFrequency p) (spectrum σ)

/-- Every actual rest envelope and the limiting field share the same existing Gaussian initial profile. -/
theorem initial_profile (p : MassiveParameters) {σ : ℝ} (hσ : 0 < σ) :
    (∀ n y, envelope (ramp p n) (originalFamily p σ n) (slicePoint 0 y) =
      (GaussianCauchySlice.amplitude σ y : ℂ)) ∧
    (∀ y, limitField p σ (slicePoint 0 y) = (GaussianCauchySlice.amplitude σ y : ℂ)) := by
  have hs := GaussianSpectralMoments.spectrum_data hσ
  have hg (y : Spatial) :
      (∫ k, GaussianSpatialFourier.character y k * spectrum σ k) =
        (GaussianCauchySlice.amplitude σ y : ℂ) := by
    simpa only [packet, MassShellFourier.initial_value] using
      GaussianPositiveFrequencyPacket.initial_value 0 hσ y
  constructor
  · intro n y
    change envelope (ramp p n)
      (MassShellFourier.wave ((ramp p n).m * (ramp p n).c / (ramp p n).hbar) (spectrum σ))
      (slicePoint 0 y) = _
    rw [(SpectralRestEnvelope.source_data (ramp p n) hs.1 hs.2).2.2,
      FrequencyGraphFourier.initial_value]
    exact hg y
  · intro y
    change FrequencyGraphFourier.wave (schrodingerFrequency p) (spectrum σ) (slicePoint 0 y) = _
    rw [FrequencyGraphFourier.initial_value]
    exact hg y

/-- One fixed Gaussian width gives actual compact field and derivative convergence, common temporal control, local L¹ convergence and the controlled source Schrödinger limit. -/
theorem controlled_limit (p : MassiveParameters) {σ : ℝ} (hσ : 0 < σ) :
    ((∀ K : Set Covector, IsCompact K →
      TendstoUniformlyOn (fun n => envelope (ramp p n) (originalFamily p σ n))
        (limitField p σ) atTop K ∧
      TendstoUniformlyOn
        (fun n => directionalDerivative (envelope (ramp p n) (originalFamily p σ n))
          (coordinateVector 0))
        (directionalDerivative (limitField p σ) (coordinateVector 0)) atTop K ∧
      ∀ i : Fin 3, TendstoUniformlyOn
        (fun n => secondDirectionalDerivative (envelope (ramp p n) (originalFamily p σ n))
          (coordinateVector i.succ))
        (secondDirectionalDerivative (limitField p σ) (coordinateVector i.succ)) atTop K) ∧
      0 ≤ (p.hbar / (2 * p.m)) ^ 2 * moment (spectrum σ) 2 ∧
      ∀ n x, ‖secondDirectionalDerivative (envelope (ramp p n) (originalFamily p σ n))
          (coordinateVector 0) x‖ ≤ (p.hbar / (2 * p.m)) ^ 2 * moment (spectrum σ) 2) ∧
    (ContDiff ℝ ∞ (limitField p σ) ∧
      ScalarLocalTesting.LocalL1 univ
        (fun n => envelope (ramp p n) (originalFamily p σ n)) (limitField p σ) ∧
      (∀ K : Set Covector, IsCompact K →
        TendstoUniformlyOn
          (fun n => schrodingerResidual p (envelope (ramp p n) (originalFamily p σ n)))
          (fun _ => 0) atTop K) ∧
      ∀ x, Complex.I * (p.hbar : ℂ) *
          directionalDerivative (limitField p σ) (coordinateVector 0) x =
        -(((p.hbar ^ 2 / (2 * p.m) : ℝ) : ℂ) * spatialLaplacian (limitField p σ) x)) := by
  have hs := GaussianSpectralMoments.spectrum_data hσ
  have hr := ramp_spec p
  have hm : ∀ n, (ramp p n).m = p.m := fun n => (hr.1 n).1
  have hh : ∀ n, (ramp p n).hbar = p.hbar := fun n => (hr.1 n).2.1
  constructor
  · simpa only [originalFamily, limitField, packet] using
      SpectralSchrodingerLimit.compact_convergence (P := ramp p) p hs.1 hs.2 hm hh hr.2
  · simpa only [originalFamily, limitField, packet] using
      SpectralSchrodingerLimit.source_limit (P := ramp p) p hs.1 hs.2 hm hh hr.2

end FoliationQM.GaussianSchrodingerLimit
