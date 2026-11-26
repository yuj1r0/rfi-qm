module

public import FoliationQM.ObserverFluxDensity
public import FoliationQM.OsmoticSliceFields
public import Mathlib.MeasureTheory.Measure.WithDensity

/-! For v13 part (iii), evaluate both sides of the probability element on
the edges of the same region parametrized in laboratory coordinates.
Coordinate volume and proper Gram volume weight the original measure on
that parameter space. Their respective physical densities give equal measures.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.DressedSliceMeasure

open LorentzCoordinates ObserverRestVolume ObserverFluxDensity ScalarDressedCurrent
open DressedMassDensityVariation OsmoticSliceFields MeasureTheory

/-- The three tangent edge columns of a laboratory spatial parametrization. -/
def edges (f : Spatial → Spatial) (y : Spatial) : Matrix (Fin 3) (Fin 3) ℝ :=
  fun i j => fderiv ℝ f y (Pi.single j 1) i

/-- Proper volume of the actual parameter edges after projection along U. -/
def properJacobian (c : ℝ) (U : Covector) (f : Spatial → Spatial) (y : Spatial) : ℝ :=
  Real.sqrt (spatialGram (combine (projected c U) (edges f y))).det

/-- In the ordinary laboratory parametrization the edge matrix is the identity. -/
theorem edges_id (y : Spatial) : edges id y = 1 := by
  ext i j
  simp [edges, Matrix.one_apply, Pi.single_apply]

/-- Equality of the two nonnegative weighted measures on the parameter space
of corresponding laboratory and comoving tangent elements of a fixed-time slice. -/
theorem measure_eq (p : MassiveParameters) (ρ S : Covector → ℝ) (t : ℝ) (f : Spatial → Spatial)
    (μ : Measure Spatial)
    (hchart : ∀ᵐ y ∂μ, DifferentiableAt ℝ f y ∧
      DifferentiableAt ℝ ρ (slicePoint t (f y)) ∧ DifferentiableAt ℝ S (slicePoint t (f y)) ∧
      0 < ρ (slicePoint t (f y)) ∧
      0 < minkowski (phaseDifferential S (slicePoint t (f y))) (phaseDifferential S (slicePoint t (f y))) ∧
      phaseDifferential S (slicePoint t (f y)) 0 < 0) :
    let X := fun y => slicePoint t (f y)
    μ.withDensity (fun y => ENNReal.ofReal (labDensity p (ActionDensity.actionField p ρ S) (X y)
      * |(edges f y).det|)) =
      μ.withDensity (fun y => ENNReal.ofReal (restDensity p ρ S (X y) *
        properJacobian p.c (DressedClockWorldline.velocity p S (X y)) f y)) := by
  apply withDensity_congr_ae
  filter_upwards [hchart] with y hy
  rcases hy with ⟨_, hρ, hS, hp, ht, hf⟩
  exact congrArg ENNReal.ofReal (probability_element p hρ hS hp ht hf (edges f y))

/-- Weighting the respective volume measures by laboratory and rest density
yields the same measure on every measurable parameter region. -/
theorem density_times_volume (p : MassiveParameters) (ρ S : Covector → ℝ) (t : ℝ) (f : Spatial → Spatial)
    (μ : Measure Spatial)
    (hchart : ∀ᵐ y ∂μ, DifferentiableAt ℝ f y ∧
      DifferentiableAt ℝ ρ (slicePoint t (f y)) ∧ DifferentiableAt ℝ S (slicePoint t (f y)) ∧
      0 < ρ (slicePoint t (f y)) ∧
      0 < minkowski (phaseDifferential S (slicePoint t (f y))) (phaseDifferential S (slicePoint t (f y))) ∧
      phaseDifferential S (slicePoint t (f y)) 0 < 0)
    (hJ : AEMeasurable (fun y => ENNReal.ofReal |(edges f y).det|) μ)
    (hP : AEMeasurable (fun y => ENNReal.ofReal (properJacobian p.c
      (DressedClockWorldline.velocity p S (slicePoint t (f y))) f y)) μ)
    (hσ : AEMeasurable (fun y => ENNReal.ofReal
      (labDensity p (ActionDensity.actionField p ρ S) (slicePoint t (f y)))) μ)
    (hr : AEMeasurable (fun y => ENNReal.ofReal (restDensity p ρ S (slicePoint t (f y)))) μ) :
    let X := fun y => slicePoint t (f y)
    (μ.withDensity (fun y => ENNReal.ofReal |(edges f y).det|)).withDensity
      (fun y => ENNReal.ofReal (labDensity p (ActionDensity.actionField p ρ S) (X y))) =
    (μ.withDensity (fun y => ENNReal.ofReal (properJacobian p.c (DressedClockWorldline.velocity p S (X y)) f y))).withDensity
      (fun y => ENNReal.ofReal (restDensity p ρ S (X y))) := by
  dsimp only
  rw [← withDensity_mul₀ hJ hσ, ← withDensity_mul₀ hP hr]
  apply withDensity_congr_ae
  filter_upwards [hchart] with y hy
  rcases hy with ⟨_, hρ, hS, hp, ht, hf⟩
  have hjp : 0 ≤ properJacobian p.c (DressedClockWorldline.velocity p S (slicePoint t (f y))) f y :=
    Real.sqrt_nonneg _
  simp only [Pi.mul_apply]
  rw [← ENNReal.ofReal_mul (abs_nonneg _), ← ENNReal.ofReal_mul hjp]
  apply congrArg ENNReal.ofReal
  simpa only [properJacobian, mul_comm] using probability_element p hρ hS hp ht hf (edges f y)

end FoliationQM.DressedSliceMeasure
