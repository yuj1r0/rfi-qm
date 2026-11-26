module

public import FoliationQM.ObserverCurrentFactor
public import FoliationQM.ObserverFisherProduct
public import FoliationQM.ObserverNormalizedShape
public import FoliationQM.SpatialFisherEnergy

/-!
# Spatial Fisher comparison for the actual laboratory current

The laboratory time is the coordinate x⁰ = ct. On an open slice chart the
coordinate current density is locally equal to gρ, so differentiation of
the measured density gives the sum of the two actual spatial scores. The
comparison of normalized shapes uses the same restricted Lebesgue measure.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.ObserverSliceFisher

open Set Filter MeasureTheory LorentzCoordinates OsmoticSliceFields ObserverCurrentFactor
open FisherNormalization
open scoped Topology ContDiff

/-- The factor −∂₀S/(mc) restricted to the fixed laboratory time. -/
def sliceFactor (p : MassiveParameters) (S : Covector → ℝ) (t : ℝ) (y : Spatial) : ℝ :=
  factor p S (Madelung.coordinateVector 0) (slicePoint t y)

/-- The laboratory density obtained from the actual current of the polar field. -/
def measured (p : MassiveParameters) (ρ S : Covector → ℝ) (t : ℝ) (y : Spatial) : ℝ :=
  ObserverFluxDensity.labDensity p (ActionDensity.actionField p ρ S) (slicePoint t y)

variable {p : MassiveParameters} {S ρ : Covector → ℝ} {t : ℝ} {U : Set Spatial}

/-- On the regular polar chart the observed current has exactly the required slice weight. -/
theorem measured_eq {y : Spatial} (hr : DifferentiableAt ℝ ρ (slicePoint t y))
    (hs : DifferentiableAt ℝ S (slicePoint t y)) (hp : 0 < ρ (slicePoint t y)) :
    measured p ρ S t y = sliceFactor p S t y * (ρ ∘ slicePoint t) y :=
  labDensity_eq_factor p hr hs hp

/-- A twice differentiable phase in the C² sense supplies the required first
spatial derivative of the actual normal-momentum factor. -/
theorem differentiableAt_sliceFactor {y : Spatial} (hS : ContDiffAt ℝ 2 S (slicePoint t y)) :
    DifferentiableAt ℝ (sliceFactor p S t) y := by
  have h := (hS.fderiv_right (m := 1) (by norm_num)).differentiableAt_one
  have hdir : DifferentiableAt ℝ (fun z => fderiv ℝ S z (Madelung.coordinateVector 0)) (slicePoint t y) :=
    h.clm_apply (differentiableAt_const _)
  have hfac : DifferentiableAt ℝ (fun z => -(fderiv ℝ S z (Madelung.coordinateVector 0)) / (p.m*p.c))
      (slicePoint t y) := by
    simpa only [div_eq_mul_inv, Pi.neg_apply] using hdir.neg.mul_const (p.m*p.c)⁻¹
  exact hfac.comp y (SpatialFisherEnergy.hasFDerivAt_slicePoint t y).differentiableAt

/-- In each spatial direction the score of the measured current is the sum of
the intrinsic score and the score of the physical observer factor. -/
theorem measured_score (hU : IsOpen U)
    (hr : ∀ y ∈ U, DifferentiableAt ℝ ρ (slicePoint t y))
    (hs : ∀ y ∈ U, ContDiffAt ℝ 2 S (slicePoint t y))
    (hp : ∀ y ∈ U, 0 < ρ (slicePoint t y))
    {y : Spatial} (hy : y ∈ U) (hg : 0 < sliceFactor p S t y) (v : Spatial) :
    score (measured p ρ S t) y v = score (ρ ∘ slicePoint t) y v + score (sliceFactor p S t) y v := by
  have hd z hz := (hs z hz).differentiableAt (by norm_num)
  have he : (fun z => Real.log (measured p ρ S t z)) =ᶠ[𝓝 y]
      fun z => Real.log (sliceFactor p S t z * (ρ ∘ slicePoint t) z) := by
    filter_upwards [hU.mem_nhds hy] with z hz
    rw [measured_eq (hr z hz) (hd z hz) (hp z hz)]
  have hs' := ObserverFisherProduct.score_mul (differentiableAt_sliceFactor (p := p) (hs y hy))
    ((hr y hy).comp y (SpatialFisherEnergy.hasFDerivAt_slicePoint t y).differentiableAt)
    hg (hp y hy) v
  exact (congrArg (fun L : Spatial →L[ℝ] ℝ => L v) he.fderiv_eq).trans hs'

/-- Integration in the three coordinate directions gives the measured current's
finite homogeneous Fisher trace on the selected open laboratory region. -/
theorem measured_trace (hU : IsOpen U)
    (hr : ∀ y ∈ U, DifferentiableAt ℝ ρ (slicePoint t y))
    (hs : ∀ y ∈ U, ContDiffAt ℝ 2 S (slicePoint t y))
    (hp : ∀ y ∈ U, 0 < ρ (slicePoint t y)) (hg : ∀ y ∈ U, 0 < sliceFactor p S t y)
    (hi : IntegrableOn (fun y => sliceFactor p S t y * (ρ ∘ slicePoint t) y *
      ∑ i : Fin 3, (score (ρ ∘ slicePoint t) y (Pi.single i 1) +
        score (sliceFactor p S t) y (Pi.single i 1)) ^ 2) U) :
    IntegrableOn (traceIntegrand (measured p ρ S t) (fun i : Fin 3 => Pi.single i 1)) U ∧
      fisherTrace (measured p ρ S t) (fun i : Fin 3 => Pi.single i 1) (volume.restrict U) =
        ∫ y in U, sliceFactor p S t y * (ρ ∘ slicePoint t) y *
          ∑ i : Fin 3, (score (ρ ∘ slicePoint t) y (Pi.single i 1) +
            score (sliceFactor p S t) y (Pi.single i 1)) ^ 2 := by
  have he : traceIntegrand (measured p ρ S t) (fun i : Fin 3 => Pi.single i 1) =ᵐ[volume.restrict U]
      fun y => sliceFactor p S t y * (ρ ∘ slicePoint t) y * ∑ i : Fin 3,
        (score (ρ ∘ slicePoint t) y (Pi.single i 1) + score (sliceFactor p S t) y (Pi.single i 1)) ^ 2 := by
    filter_upwards [ae_restrict_mem hU.measurableSet] with y hy
    simp only [traceIntegrand, measured_eq (hr y hy) ((hs y hy).differentiableAt (by norm_num)) (hp y hy),
      measured_score hU hr hs hp hy (hg y hy)]
  exact ⟨hi.congr he.symm, integral_congr_ae he⟩

/-- For the actual current, separate mass normalization gives equal shapes
exactly when the phase-derived observer factor is constant almost everywhere. -/
theorem measured_shape_iff_const (hU : MeasurableSet U)
    (hr : ∀ y ∈ U, DifferentiableAt ℝ ρ (slicePoint t y))
    (hs : ∀ y ∈ U, DifferentiableAt ℝ S (slicePoint t y))
    (hp : ∀ y ∈ U, 0 < ρ (slicePoint t y))
    (hm : 0 < ObserverNormalizedShape.mass (volume.restrict U) (ρ ∘ slicePoint t))
    (ho : 0 < ObserverNormalizedShape.mass (volume.restrict U) (measured p ρ S t)) :
    ObserverNormalizedShape.shape (volume.restrict U) (measured p ρ S t) =ᵐ[volume.restrict U]
      ObserverNormalizedShape.shape (volume.restrict U) (ρ ∘ slicePoint t) ↔
        ∃ a : ℝ, 0 < a ∧ sliceFactor p S t =ᵐ[volume.restrict U] fun _ => a := by
  have he : measured p ρ S t =ᵐ[volume.restrict U] fun y => sliceFactor p S t y * (ρ ∘ slicePoint t) y :=
    (ae_restrict_mem hU).mono fun y hy => measured_eq (hr y hy) (hs y hy) (hp y hy)
  have hm' := integral_congr_ae he
  have ho' : 0 < ObserverNormalizedShape.mass (volume.restrict U)
      (fun y => sliceFactor p S t y * (ρ ∘ slicePoint t) y) := ho.trans_eq hm'
  rw [← ObserverNormalizedShape.shape_ae_eq_iff_const _ _ _ ((ae_restrict_mem hU).mono fun y hy =>
    hp y hy) hm ho']
  have he' : ObserverNormalizedShape.shape (volume.restrict U) (measured p ρ S t) =ᵐ[volume.restrict U]
      ObserverNormalizedShape.shape (volume.restrict U) (fun y => sliceFactor p S t y * (ρ ∘ slicePoint t) y) := by
    filter_upwards [he] with y hy
    change measured p ρ S t y / _ = _ / _
    simp only [ObserverNormalizedShape.mass, hm', hy]
  exact ⟨fun h => he'.symm.trans h, fun h => he'.trans h⟩

end FoliationQM.ObserverSliceFisher
