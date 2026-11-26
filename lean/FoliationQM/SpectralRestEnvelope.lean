module

public import FoliationQM.PolynomialSpectralMoments
public import FoliationQM.StationaryAction

/-!
# The actual spectral rest envelope and its Schrödinger comparison

Source: v13 `cor:schrodinger`, component kinds C and D. Polynomial moments
of one continuous angular amplitude give the original positive-branch KG
wave and its literal rest-removed envelope. The same amplitude at the
Schrödinger frequency gives a smooth solution of the actual limiting PDE.
Every integral combination below has genuine integrability; no convergence,
spectral support, positivity, or normalization assumption is introduced.
-/

@[expose] public section
noncomputable section

namespace FoliationQM.SpectralRestEnvelope

open MeasureTheory LorentzCoordinates PolarSecondDifferential
open ReducedMassShellFrequency PolynomialSpectralMoments
open RestEnvelopeKG LaboratoryCoordinates LaboratoryKG
open Madelung (coordinateVector)
open scoped ContDiff

/-- One actual spectral KG wave is smooth, solves the dimensional equation, and has exactly the reduced-frequency graph wave as its rest envelope. -/
theorem source_data (p : MassiveParameters) {A : Spatial → ℂ}
    (hA : Continuous A) (hpoly : PolynomialMoments A) :
    ContDiff ℝ ∞ (MassShellFourier.wave (p.m * p.c / p.hbar) A) ∧
      (∀ x, FlatIntegrationByParts.kgOperator p
        (MassShellFourier.wave (p.m * p.c / p.hbar) A) coordinateVector x = 0) ∧
      envelope p (MassShellFourier.wave (p.m * p.c / p.hbar) A) =
        FrequencyGraphFourier.wave (reducedFrequency p) A := by
  have hm := massShell_moments (p.m * p.c / p.hbar) hA hpoly
  have hw : Continuous (GaussianKGMode.rate (p.m * p.c / p.hbar)) := by
    unfold GaussianKGMode.rate speedSq spatialDot
    fun_prop
  have hg : FrequencyGraphFourier.HasMoments
      (GaussianKGMode.rate (p.m * p.c / p.hbar)) A := by
    simpa only [FrequencyGraphFourier.HasMoments, FrequencyGraphFourier.graph,
      MassShellFourier.HasMoments, MassShellFourier.shell] using hm
  refine ⟨MassShellFourier.smooth_wave _ hA hm, ?_, ?_⟩
  · intro x
    apply (StationaryAction.kgOperator_eq_zero_iff p _ coordinateVector x).mpr
    simpa only [div_pow, mul_pow] using
      MassShellFourier.klein_gordon (p.m * p.c / p.hbar) hA hm x
  · funext x
    have hi : Integrable (fun k =>
        MassShellFourier.mode (p.m * p.c / p.hbar) k (toNormal p.c x) * A k) := by
      simpa only [MassShellFourier.mode, ReducedPlaneWave.mode] using
        FrequencyGraphFourier.integrable_mode hw hA hg (toNormal p.c x)
    have hscale := hi.integral_smul ((RestEnvelopeDifferential.carrierField p x)⁻¹)
    simp only [smul_eq_mul] at hscale
    change (RestEnvelopeDifferential.carrierField p x)⁻¹ *
      (∫ k, MassShellFourier.mode (p.m * p.c / p.hbar) k (toNormal p.c x) * A k) =
        ∫ k, ReducedPlaneWave.mode (reducedFrequency p k) k x * A k
    rw [← hscale]
    apply integral_congr_ae
    exact ae_of_all _ fun k => by
      have he := congrFun (ReducedPlaneWave.envelope_mode p k) x
      change (RestEnvelopeDifferential.carrierField p x)⁻¹ *
        MassShellFourier.mode (p.m * p.c / p.hbar) k (toNormal p.c x) = _ at he
      change (RestEnvelopeDifferential.carrierField p x)⁻¹ *
        (MassShellFourier.mode (p.m * p.c / p.hbar) k (toNormal p.c x) * A k) = _
      rw [← mul_assoc, he]

/-- The same continuous amplitude with genuine polynomial moments gives a smooth graph wave whose actual physical Schrödinger residual vanishes everywhere. -/
theorem schrodinger_wave (p : MassiveParameters) {A : Spatial → ℂ}
    (hA : Continuous A) (hpoly : PolynomialMoments A) :
    ContDiff ℝ ∞ (FrequencyGraphFourier.wave (schrodingerFrequency p) A) ∧
      ∀ x, schrodingerResidual p
        (FrequencyGraphFourier.wave (schrodingerFrequency p) A) x = 0 := by
  have hw := (continuous_frequencies p).2
  have hm := (reduced_nr_moments p hA hpoly).2
  refine ⟨FrequencyGraphFourier.smooth_wave hw hA hm, ?_⟩
  intro x
  let w := schrodingerFrequency p
  let first := FrequencyGraphFourier.differentiated w 0 A
  let second := fun i => FrequencyGraphFourier.differentiated w i
    (FrequencyGraphFourier.differentiated w i A)
  have hd (i : Fin 4) := FrequencyGraphFourier.differentiated_data hw hA hm i
  have hd₂ (i : Fin 4) := FrequencyGraphFourier.differentiated_data hw (hd i).1 (hd i).2 i
  have hf : Integrable (fun k => ReducedPlaneWave.mode (w k) k x * first k) :=
    FrequencyGraphFourier.integrable_mode hw (hd 0).1 (hd 0).2 x
  have hi (i : Fin 4) : Integrable (fun k =>
      ReducedPlaneWave.mode (w k) k x * second i k) :=
    FrequencyGraphFourier.integrable_mode hw (hd₂ i).1 (hd₂ i).2 x
  let f := fun k => ReducedPlaneWave.mode (w k) k x * first k
  let g := fun i k => ReducedPlaneWave.mode (w k) k x * second i k
  have h12 : Integrable (fun k => g 1 k + g 2 k) := (hi 1).add (hi 2)
  have h123 : Integrable (fun k => g 1 k + g 2 k + g 3 k) := h12.add (hi 3)
  have ht : Integrable (fun k => (Complex.I * (p.hbar : ℂ)) * f k) := hf.const_mul _
  have hs : Integrable (fun k => ((p.hbar ^ 2 / (2 * p.m) : ℝ) : ℂ) *
      (g 1 k + g 2 k + g 3 k)) := h123.const_mul _
  simp only [schrodingerResidual, FrequencyGraphFourier.first_coordinate hw hA hm,
    spatialLaplacian, FrequencyGraphFourier.second_coordinate hw hA hm,
    Fin.sum_univ_three, FrequencyGraphFourier.wave]
  change Complex.I * (p.hbar : ℂ) * (∫ k, f k) +
    ((p.hbar ^ 2 / (2 * p.m) : ℝ) : ℂ) *
      ((∫ k, g 1 k) + (∫ k, g 2 k) + (∫ k, g 3 k)) = 0
  rw [← integral_add (hi 1) (hi 2), ← integral_add h12 (hi 3),
    ← integral_const_mul, ← integral_const_mul, ← integral_add ht hs]
  apply integral_eq_zero_of_ae
  refine ae_of_all _ fun k => ?_
  simp only [f, g, first, second, FrequencyGraphFourier.differentiated,
    FrequencyGraphFourier.graph, assemble, Pi.neg_apply, w, schrodingerFrequency,
    speedSq, spatialDot]
  push_cast
  ring_nf
  rfl

end FoliationQM.SpectralRestEnvelope
