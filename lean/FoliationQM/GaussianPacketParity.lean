module

public import FoliationQM.GaussianPacketPolarDomain

/-!
# Reflection symmetry of the massive Gaussian rest packet

V13's Gaussian width test compares the actual material dilatation with the
spatial logarithmic score. At the packet center, spatial reflection forces
the latter to vanish at every time. The argument uses the same Fourier
solution at all spatial points on each laboratory slice.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.GaussianPacketParity

open LorentzCoordinates GaussianPacketPolarDomain OsmoticSliceFields GaussianPositiveFrequencyPacket
open DressedMassDensityVariation ObserverFluxDensity LogDensityTransport MeasureTheory

/-- On every normal-time slice, reversing all spatial coordinates leaves the
positive-frequency rest packet unchanged. -/
theorem packet_even (μ σ s : ℝ) (y : Spatial) :
    packet μ σ (slicePoint s (-y)) = packet μ σ (slicePoint s y) := by
  let f := fun k => MassShellFourier.mode μ k (slicePoint s y) * GaussianPositiveFrequencyPacket.spectrum σ k
  change (∫ k, MassShellFourier.mode μ k (slicePoint s (-y)) * GaussianPositiveFrequencyPacket.spectrum σ k) = ∫ k, f k
  rw [← integral_neg_eq_self (μ := (volume : Measure Spatial)) f]
  apply integral_congr_ae
  filter_upwards with k
  have he : GaussianPositiveFrequencyPacket.spectrum σ (-k) = GaussianPositiveFrequencyPacket.spectrum σ k := by
    simp only [GaussianPositiveFrequencyPacket.spectrum, GaussianMassShellMoments.weight_neg]
  simp only [f, he, MassShellFourier.mode, GaussianMassShellMoments.rate_neg]
  congr 1
  congr 1
  simp [spatialDot, slicePoint, assemble]

/-- A spatially even scalar field has zero ambient spatial gradient on the
central time axis. This includes the total derivative at nonsmooth points. -/
theorem central_gradient (f : Covector → ℝ) (s : ℝ)
    (he : ∀ y : Spatial, f (slicePoint s (-y)) = f (slicePoint s y)) :
    spatialGradient f (slicePoint s 0) = 0 := by
  by_cases hf : DifferentiableAt ℝ f (slicePoint s 0)
  · let g := fun y => f (slicePoint s y)
    have hd : HasFDerivAt g ((fderiv ℝ f (slicePoint s 0)).comp SpatialFisherEnergy.sliceTangent) 0 :=
      hf.hasFDerivAt.comp 0 (SpatialFisherEnergy.hasFDerivAt_slicePoint s 0)
    have hneg : HasFDerivAt (fun y : Spatial => -y) (-(ContinuousLinearMap.id ℝ Spatial)) 0 :=
      (hasFDerivAt_id (𝕜 := ℝ) (0 : Spatial)).neg
    have hd' : HasFDerivAt g ((fderiv ℝ f (slicePoint s 0)).comp SpatialFisherEnergy.sliceTangent)
        (-(0 : Spatial)) := by simpa using hd
    have hr := hd'.comp (0 : Spatial) hneg
    have heq : g ∘ (fun y : Spatial => -y) = g := funext he
    rw [heq] at hr
    have h := hd.unique hr
    ext i
    have hz := congrArg (fun L : Spatial →L[ℝ] ℝ => L (Pi.single i 1)) h
    simp only [ContinuousLinearMap.comp_apply, neg_apply,
      ContinuousLinearMap.id_apply, map_neg, SpatialFisherEnergy.sliceTangent_unit] at hz
    change fderiv ℝ f (slicePoint s 0) (Madelung.coordinateVector i.succ) = 0
    linarith
  · ext i
    change fderiv ℝ f (slicePoint s 0) (Madelung.coordinateVector i.succ) = 0
    rw [fderiv_zero_of_not_differentiableAt hf]
    rfl

/-- The physical spatial score of the rest packet vanishes at its center at every normal time. -/
theorem center_spatial_score (p : MassiveParameters) {σ : ℝ} (_hσ : 0 < σ) (s : ℝ) :
    spatialScore (density p σ) (slicePoint s 0) = 0 := by
  apply central_gradient
  intro y
  change Real.log (Complex.normSq (packet _ σ (slicePoint s (-y)))) = _
  rw [packet_even]
  rfl

/-- The central spatial phase derivatives and the physical drift both vanish
on the entire time axis by reflection symmetry. -/
theorem center_drift (p : MassiveParameters) (σ s : ℝ) :
    phaseDrift p.c (action p σ) (slicePoint s 0) = 0 := by
  have hs := central_gradient (action p σ) s (fun y => by
    change PolarLocalInverse.localAction p 1 (packet _ σ (slicePoint s (-y))) = _
    rw [packet_even]
    rfl)
  ext i
  have hi := congrFun hs i
  change phaseDifferential (action p σ) (slicePoint s 0) i.succ = 0 at hi
  simp [phaseDrift, hi]

end FoliationQM.GaussianPacketParity
