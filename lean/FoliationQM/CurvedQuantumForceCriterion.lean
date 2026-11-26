module

public import FoliationQM.CurvedDefectSupremum
public import FoliationQM.CurvedIntegratedForceEnvelope

/-!
# The actual uniform-gradient sufficient condition for quantum force

The envelope is constructed from the exact spatial supremum of the
computed full spacetime defect differential. Its coefficient is common
to the family under explicit inverse-raising, temporal and velocity-ratio
controls. Measurability and interval integrability refer to that actual
supremum. The compact builder proves those properties from the actual KG
regularity; general moving regions retain them as explicit hypotheses.

The uniform-positive-normalization result holds for every family index.
The uniform-small-defect result derives the normalization lower bound
eventually and accordingly asserts its force bound eventually.
Neither theorem assumes the desired force envelope or a separate jet.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.CurvedQuantumForceCriterion

open LorentzMatrixGroup CurvedPolarKG CurvedNormalizedQuantumForce CurvedCoordinateDynamics
  CurvedCoordinateTrajectories CurvedAuxiliaryNorm CurvedQuantumForceBound
  CurvedDefectSupremum
open scoped Topology Matrix.Norms.Operator

/-- A strictly positive common coefficient in the source form C c², with a harmless unit enlargement of the proved algebraic coefficient. -/
def sourceCoefficient (c umin δ Bv Bg : ℝ) : ℝ :=
  1 + 3 * c ^ 2 * (1 + Bv) * Bg / (2 * umin ^ 2 * δ)

/-- The source coefficient is positive under the explicit uniform control assumptions. -/
theorem sourceCoefficient_pos {c umin δ Bv Bg : ℝ} (hmin : 0 < umin)
    (hδ : 0 < δ) (hBv : 0 ≤ Bv) (hBg : 0 ≤ Bg) :
    0 < sourceCoefficient c umin δ Bv Bg := by
  unfold sourceCoefficient
  positivity

/-- Multiplying the positive source coefficient by c² dominates the exact uniform force coefficient. -/
theorem coefficient_le_source {c umin δ Bv Bg : ℝ} :
    3 * c ^ 4 * (1 + Bv) * Bg / (2 * umin ^ 2 * δ) ≤
      sourceCoefficient c umin δ Bv Bg * c ^ 2 := by
  have he : sourceCoefficient c umin δ Bv Bg * c ^ 2 =
      3 * c ^ 4 * (1 + Bv) * Bg / (2 * umin ^ 2 * δ) + c ^ 2 := by
    unfold sourceCoefficient
    ring
  rw [he]
  exact le_add_of_nonneg_right (sq_nonneg c)


/-- The Euclidean norm of the actual three-component KG coordinate force at the chart point (ct,z). -/
def spatialForceNorm (p : MassiveParameters) (g : Covector → Mat4)
    (R S : Covector → ℝ) (t : ℝ) (z : Fin 3 → ℝ) : ℝ :=
  norm2 (spatialPart (coordinateForce p.c g (normalizedVelocity p g R S)
    (coordinatePoint p.c t z)))

/-- The family function is the exact supremum of the actual full defect differential on the selected time slice. -/
def gradientSupFamily {ι : Type*} (P : ι → MassiveParameters) (g : Covector → Mat4)
    (amp phase : ι → Covector → ℝ) (T : ℝ) (K : ℝ → Set (Fin 3 → ℝ))
    (hreg : ∀ i, RegularOnTube (P i) g (amp i) (phase i) T K)
    (hDbnd : ∀ i, DifferentialBoundedOnTube (P i) g (amp i) T K) (i : ι) (t : ℝ) : ℝ :=
  gradientSup (P i) g (amp i) (phase i) T K (hreg i) (hDbnd i) t

/-- The actual full-gradient supremum is nonnegative for every family index and time. -/
theorem gradientSupFamily_nonneg {ι : Type*} (P : ι → MassiveParameters)
    (g : Covector → Mat4) (amp phase : ι → Covector → ℝ) (T : ℝ)
    (K : ℝ → Set (Fin 3 → ℝ))
    (hreg : ∀ i, RegularOnTube (P i) g (amp i) (phase i) T K)
    (hDbnd : ∀ i, DifferentialBoundedOnTube (P i) g (amp i) T K) (i : ι) (t : ℝ) :
    0 ≤ gradientSupFamily P g amp phase T K hreg hDbnd i t :=
  norm_nonneg _

/-- The exact slice supremum bounds the actual KG force at every point of the slice, with the explicit positive source coefficient. -/
theorem point_force_le (p : MassiveParameters) (g : Covector → Mat4)
    (R S : Covector → ℝ) (T : ℝ) (K : ℝ → Set (Fin 3 → ℝ))
    (hreg : RegularOnTube p g R S T K) (hDbnd : DifferentialBoundedOnTube p g R T K)
    {umin δ Bv Bg t : ℝ} {z : Fin 3 → ℝ}
    (ht : t ∈ Set.Icc 0 T) (hz : z ∈ K t)
    (hmin : 0 < umin) (hδ : 0 < δ) (hBv : 0 ≤ Bv) (hBg : 0 ≤ Bg)
    (hu : umin ≤ |normalizedVelocity p g R S (coordinatePoint p.c t z) 0|)
    (hq : δ ≤ 1 + defect p g R (coordinatePoint p.c t z))
    (hratio : ∀ j : Fin 3,
      |normalizedVelocity p g R S (coordinatePoint p.c t z) j.succ /
        normalizedVelocity p g R S (coordinatePoint p.c t z) 0| ≤ Bv)
    (hA : ‖raiseMap ((g (coordinatePoint p.c t z))⁻¹)‖ ≤ Bg) :
    spatialForceNorm p g R S t z ≤
      (sourceCoefficient p.c umin δ Bv Bg * p.c ^ 2) *
        gradientSup p g R S T K hreg hDbnd t := by
  have hC := sourceCoefficient_pos (c := p.c) hmin hδ hBv hBg
  calc
    _ ≤ (3 * p.c ^ 4 * (1 + Bv) * Bg / (2 * umin ^ 2 * δ)) *
        norm2 (CurvedGradientCovariance.components (defect p g R) (coordinatePoint p.c t z)) :=
      norm_coordinate_force_le (hreg t ht z hz) hmin hu hδ hq hBv hBg hratio hA
    _ ≤ (sourceCoefficient p.c umin δ Bv Bg * p.c ^ 2) *
        norm2 (CurvedGradientCovariance.components (defect p g R) (coordinatePoint p.c t z)) :=
      mul_le_mul_of_nonneg_right coefficient_le_source (norm2_nonneg _)
    _ ≤ _ := mul_le_mul_of_nonneg_left (gradient_norm_le_sup hreg hDbnd ht hz)
      (mul_nonneg hC.le (sq_nonneg p.c))

open MeasureTheory Filter

/-- Uniform geometric and normalization controls turn the actual full-gradient integral criterion into a nonnegative measurable integrable force envelope for every family index, with vanishing integral. -/
theorem uniform_force_criterion {ι : Type*} {l : Filter ι}
    (P : ι → MassiveParameters) (g : Covector → Mat4)
    (amp phase : ι → Covector → ℝ) (T : ℝ) (K : ℝ → Set (Fin 3 → ℝ))
    (hreg : ∀ i, RegularOnTube (P i) g (amp i) (phase i) T K)
    (hDbnd : ∀ i, DifferentialBoundedOnTube (P i) g (amp i) T K)
    {c umin δ Bv Bg : ℝ} (hc : ∀ i, (P i).c = c)
    (hmin : 0 < umin) (hδ : 0 < δ) (hBv : 0 ≤ Bv) (hBg : 0 ≤ Bg)
    (hu : ∀ i t, t ∈ Set.Icc 0 T → ∀ z ∈ K t,
      umin ≤ |normalizedVelocity (P i) g (amp i) (phase i)
        (coordinatePoint (P i).c t z) 0|)
    (hq : ∀ i t, t ∈ Set.Icc 0 T → ∀ z ∈ K t,
      δ ≤ 1 + defect (P i) g (amp i) (coordinatePoint (P i).c t z))
    (hratio : ∀ i t, t ∈ Set.Icc 0 T → ∀ z ∈ K t, ∀ j : Fin 3,
      |normalizedVelocity (P i) g (amp i) (phase i) (coordinatePoint (P i).c t z) j.succ /
        normalizedVelocity (P i) g (amp i) (phase i) (coordinatePoint (P i).c t z) 0| ≤ Bv)
    (hA : ∀ i t, t ∈ Set.Icc 0 T → ∀ z ∈ K t,
      ‖raiseMap ((g (coordinatePoint (P i).c t z))⁻¹)‖ ≤ Bg)
    (hMeas : ∀ i, Measurable (gradientSupFamily P g amp phase T K hreg hDbnd i))
    (hInt : ∀ i, IntervalIntegrable (gradientSupFamily P g amp phase T K hreg hDbnd i) volume 0 T)
    (hLim : Tendsto (fun i => ∫ t in 0..T,
      gradientSupFamily P g amp phase T K hreg hDbnd i t) l (𝓝 0)) :
    let C := sourceCoefficient c umin δ Bv Bg
    let B := gradientSupFamily P g amp phase T K hreg hDbnd
    let A := CurvedIntegratedForceEnvelope.envelope (C * c ^ 2) B
    0 < C ∧ (∀ i t, 0 ≤ A i t) ∧ (∀ i, Measurable (A i)) ∧
      (∀ i, IntervalIntegrable (A i) volume 0 T) ∧
      (∀ i t, t ∈ Set.Icc 0 T → ∀ z ∈ K t,
        spatialForceNorm (P i) g (amp i) (phase i) t z ≤ A i t) ∧
      (∀ i, (∫ t in 0..T, A i t) = (C * c ^ 2) * ∫ t in 0..T, B i t) ∧
      Tendsto (fun i => ∫ t in 0..T, A i t) l (𝓝 0) := by
  dsimp only
  have hC := sourceCoefficient_pos (c := c) hmin hδ hBv hBg
  have hCc : 0 ≤ sourceCoefficient c umin δ Bv Bg * c ^ 2 :=
    mul_nonneg hC.le (sq_nonneg c)
  refine ⟨hC, CurvedIntegratedForceEnvelope.envelope_nonneg hCc
    (gradientSupFamily_nonneg P g amp phase T K hreg hDbnd),
    fun i => CurvedIntegratedForceEnvelope.measurable_envelope _ (hMeas i),
    fun i => CurvedIntegratedForceEnvelope.intervalIntegrable_envelope _ (hInt i),
    ?_, fun i => CurvedIntegratedForceEnvelope.integral_envelope _ _ i T,
    CurvedIntegratedForceEnvelope.tendsto_integral_envelope _ hLim⟩
  intro i t ht z hz
  have H := point_force_le (P i) g (amp i) (phase i) T K (hreg i) (hDbnd i)
    ht hz hmin hδ hBv hBg (hu i t ht z hz) (hq i t ht z hz)
    (hratio i t ht z hz) (hA i t ht z hz)
  change spatialForceNorm (P i) g (amp i) (phase i) t z ≤
    (sourceCoefficient c umin δ Bv Bg * c ^ 2) *
      gradientSup (P i) g (amp i) (phase i) T K (hreg i) (hDbnd i) t
  have he : sourceCoefficient (P i).c umin δ Bv Bg * (P i).c ^ 2 =
      sourceCoefficient c umin δ Bv Bg * c ^ 2 := by rw [hc i]
  rwa [he] at H

end FoliationQM.CurvedQuantumForceCriterion
