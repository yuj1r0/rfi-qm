module

public import FoliationQM.CurvedQuantumForceCriterion

/-!
# The actual small-defect sufficient condition for quantum force

Uniform convergence of the computed scalar defect on the common tube
gives a normalization lower bound eventually. The force envelope is
constructed at every family index from the exact full differential
supremum, but its physical force estimate is asserted only eventually.
The geometric controls remain explicit, including the inverse-raising
operator bound on the selected, possibly noncompact, moving region.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.CurvedSmallDefectCriterion

open LorentzMatrixGroup CurvedPolarKG CurvedNormalizedQuantumForce CurvedCoordinateDynamics
  CurvedCoordinateTrajectories CurvedAuxiliaryNorm CurvedQuantumForceBound
  CurvedDefectSupremum CurvedQuantumForceCriterion MeasureTheory Filter
open scoped Topology Matrix.Norms.Operator BoundedContinuousFunction

/-- Smallness of the actual scalar defect supremum gives a uniform positive normalization bound eventually, including on empty tubes. -/
theorem eventually_normalization_lower_bound {ι : Type*} {l : Filter ι}
    (P : ι → MassiveParameters) (g : Covector → Mat4)
    (amp phase : ι → Covector → ℝ) (T : ℝ) (K : ℝ → Set (Fin 3 → ℝ))
    (hreg : ∀ i, RegularOnTube (P i) g (amp i) (phase i) T K)
    (hqbnd : ∀ i, DefectBoundedOnTube (P i) g (amp i) T K)
    (hSmall : Tendsto (fun i => defectSup (P i) g (amp i) (phase i) T K
      (hreg i) (hqbnd i)) l (𝓝 0)) :
    ∀ᶠ i in l, ∀ t ∈ Set.Icc 0 T, ∀ z ∈ K t,
      (1 / 2 : ℝ) ≤ 1 + defect (P i) g (amp i) (coordinatePoint (P i).c t z) := by
  have H := CurvedIntegratedForceEnvelope.eventually_half_le_one_add
    (fun i => scalarDefect (P i) g (amp i) (phase i) T K (hreg i) (hqbnd i)) hSmall
  filter_upwards [H] with i hi
  intro t ht z hz
  exact hi ⟨(t, z), ht, hz⟩

/-- The actual uniform-small-defect and integrated full-gradient conditions produce an all-index measurable integrable envelope with vanishing integral, and eventually bound the actual KG force on every slice point. -/
theorem small_defect_force_criterion {ι : Type*} {l : Filter ι}
    (P : ι → MassiveParameters) (g : Covector → Mat4)
    (amp phase : ι → Covector → ℝ) (T : ℝ) (K : ℝ → Set (Fin 3 → ℝ))
    (hreg : ∀ i, RegularOnTube (P i) g (amp i) (phase i) T K)
    (hDbnd : ∀ i, DifferentialBoundedOnTube (P i) g (amp i) T K)
    (hqbnd : ∀ i, DefectBoundedOnTube (P i) g (amp i) T K)
    {c umin Bv Bg : ℝ} (hc : ∀ i, (P i).c = c)
    (hmin : 0 < umin) (hBv : 0 ≤ Bv) (hBg : 0 ≤ Bg)
    (hu : ∀ i t, t ∈ Set.Icc 0 T → ∀ z ∈ K t,
      umin ≤ |normalizedVelocity (P i) g (amp i) (phase i)
        (coordinatePoint (P i).c t z) 0|)
    (hratio : ∀ i t, t ∈ Set.Icc 0 T → ∀ z ∈ K t, ∀ j : Fin 3,
      |normalizedVelocity (P i) g (amp i) (phase i) (coordinatePoint (P i).c t z) j.succ /
        normalizedVelocity (P i) g (amp i) (phase i) (coordinatePoint (P i).c t z) 0| ≤ Bv)
    (hA : ∀ i t, t ∈ Set.Icc 0 T → ∀ z ∈ K t,
      ‖raiseMap ((g (coordinatePoint (P i).c t z))⁻¹)‖ ≤ Bg)
    (hMeas : ∀ i, Measurable (gradientSupFamily P g amp phase T K hreg hDbnd i))
    (hInt : ∀ i, IntervalIntegrable (gradientSupFamily P g amp phase T K hreg hDbnd i)
      volume 0 T)
    (hLim : Tendsto (fun i => ∫ t in 0..T,
      gradientSupFamily P g amp phase T K hreg hDbnd i t) l (𝓝 0))
    (hSmall : Tendsto (fun i => defectSup (P i) g (amp i) (phase i) T K
      (hreg i) (hqbnd i)) l (𝓝 0)) :
    let C := sourceCoefficient c umin (1 / 2) Bv Bg
    let B := gradientSupFamily P g amp phase T K hreg hDbnd
    let A := CurvedIntegratedForceEnvelope.envelope (C * c ^ 2) B
    0 < C ∧ (∀ i t, 0 ≤ A i t) ∧ (∀ i, Measurable (A i)) ∧
      (∀ i, IntervalIntegrable (A i) volume 0 T) ∧
      (∀ᶠ i in l, ∀ t ∈ Set.Icc 0 T, ∀ z ∈ K t,
        (1 / 2 : ℝ) ≤ 1 + defect (P i) g (amp i) (coordinatePoint (P i).c t z) ∧
        spatialForceNorm (P i) g (amp i) (phase i) t z ≤ A i t) ∧
      (∀ i, (∫ t in 0..T, A i t) = (C * c ^ 2) * ∫ t in 0..T, B i t) ∧
      Tendsto (fun i => ∫ t in 0..T, A i t) l (𝓝 0) := by
  dsimp only
  have hhalf : (0 : ℝ) < 1 / 2 := by norm_num
  have hC := sourceCoefficient_pos (c := c) hmin hhalf hBv hBg
  have hCc : 0 ≤ sourceCoefficient c umin (1 / 2) Bv Bg * c ^ 2 :=
    mul_nonneg hC.le (sq_nonneg c)
  refine ⟨hC, CurvedIntegratedForceEnvelope.envelope_nonneg hCc
    (gradientSupFamily_nonneg P g amp phase T K hreg hDbnd),
    fun i => CurvedIntegratedForceEnvelope.measurable_envelope _ (hMeas i),
    fun i => CurvedIntegratedForceEnvelope.intervalIntegrable_envelope _ (hInt i),
    ?_, fun i => CurvedIntegratedForceEnvelope.integral_envelope _ _ i T,
    CurvedIntegratedForceEnvelope.tendsto_integral_envelope _ hLim⟩
  have H := eventually_normalization_lower_bound P g amp phase T K hreg hqbnd hSmall
  filter_upwards [H] with i hi
  intro t ht z hz
  refine ⟨hi t ht z hz, ?_⟩
  have hf := point_force_le (P i) g (amp i) (phase i) T K (hreg i) (hDbnd i)
    ht hz hmin hhalf hBv hBg (hu i t ht z hz) (hi t ht z hz)
    (hratio i t ht z hz) (hA i t ht z hz)
  change spatialForceNorm (P i) g (amp i) (phase i) t z ≤
    (sourceCoefficient c umin (1 / 2) Bv Bg * c ^ 2) *
      gradientSup (P i) g (amp i) (phase i) T K (hreg i) (hDbnd i) t
  have he : sourceCoefficient (P i).c umin (1 / 2) Bv Bg * (P i).c ^ 2 =
      sourceCoefficient c umin (1 / 2) Bv Bg * c ^ 2 := by rw [hc i]
  rwa [he] at hf

end FoliationQM.CurvedSmallDefectCriterion
