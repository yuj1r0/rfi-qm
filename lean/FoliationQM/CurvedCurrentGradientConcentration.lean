module

public import FoliationQM.CurvedCurrentWeakConcentration
public import FoliationQM.CurvedSmallDefectCriterion

/-!
# Actual gradient criteria for geometric current concentration

The full spacetime defect-gradient supremum constructs the force envelope with all
uniform inverse, temporal, ratio and normalization controls retained. One
initial-current almost-everywhere label event gives the whole-time phase
and spatial tube conditions. The genuine current-family theorem then gives
finite Wasserstein and weak concentration. Small-defect force control is
used only eventually along the stated filter.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.CurvedCurrentGradientConcentration

open LorentzMatrixGroup CurvedCoordinateCurrent CurvedCurrentTransport
  CurvedCurrentConcentration CurvedCurrentWeakConcentration CurvedNormalizedQuantumForce
  CurvedPolarKG CurvedQuantumForceCriterion CurvedDefectSupremum CurvedCoordinateTrajectories
  CurvedAuxiliaryNorm CurvedEuclideanTrajectories ProbabilityTrajectoryEstimate
  MeasureTheory Set Filter
open scoped Topology Matrix.Norms.Operator

variable {ι : Type*} {T Lx Lv c : ℝ}
  {Ω : ℝ → Set (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3))}
  {Y W : ℝ → EuclideanSpace ℝ (Fin 3)}

/-- The actual uniform full-gradient criterion yields concentration of the genuine normalized current family. -/
theorem family_concentration_of_uniform_gradient
    (P : ι → MassiveParameters) (g : Covector → Mat4)
    (amp phase : ι → Covector → ℝ) (Phi : ι → ℝ × (Fin 3 → ℝ) → (Fin 3 → ℝ))
    (domains : ι → Set (Fin 3 → ℝ))
    (H : ∀ i, FiniteFlowData (P i) g (amp i) (phase i) (Phi i) T (domains i))
    (l : Filter ι) (K : ℝ → Set (Fin 3 → ℝ))
    (hreg : ∀ i, RegularOnTube (P i) g (amp i) (phase i) T K)
    (hDbnd : ∀ i, DifferentialBoundedOnTube (P i) g (amp i) T K)
    {umin δ Bv Bg : ℝ} (hc : ∀ i, (P i).c = c)
    (hmin : 0 < umin) (hδ : 0 < δ) (hBv : 0 ≤ Bv) (hBg : 0 ≤ Bg)
    (hu : ∀ i s, s ∈ Icc 0 T → ∀ z ∈ K s,
      umin ≤ |normalizedVelocity (P i) g (amp i) (phase i)
        (coordinatePoint (P i).c s z) 0|)
    (hq : ∀ i s, s ∈ Icc 0 T → ∀ z ∈ K s,
      δ ≤ 1 + defect (P i) g (amp i) (coordinatePoint (P i).c s z))
    (hratio : ∀ i s, s ∈ Icc 0 T → ∀ z ∈ K s, ∀ j : Fin 3,
      |normalizedVelocity (P i) g (amp i) (phase i) (coordinatePoint (P i).c s z) j.succ /
        normalizedVelocity (P i) g (amp i) (phase i) (coordinatePoint (P i).c s z) 0| ≤ Bv)
    (hRaise : ∀ i s, s ∈ Icc 0 T → ∀ z ∈ K s,
      ‖raiseMap ((g (coordinatePoint (P i).c s z))⁻¹)‖ ≤ Bg)
    (hMeas : ∀ i, Measurable (gradientSupFamily P g amp phase T K hreg hDbnd i))
    (hInt : ∀ i, IntervalIntegrable (gradientSupFamily P g amp phase T K hreg hDbnd i)
      volume 0 T)
    (hLim : Tendsto (fun i => ∫ s in 0..T,
      gradientSupFamily P g amp phase T K hreg hDbnd i s) l (𝓝 0))
    (hT : 0 < T) (hLx : 0 ≤ Lx) (hLv : 0 ≤ Lv)
    (hRef : ReferenceCurve (geodesic c g) Ω T Y W)
    (hG : ∀ s ∈ Icc 0 T, ∀ z ∈ Ω s, ∀ w ∈ Ω s,
      ‖geodesic c g s z.1 z.2 - geodesic c g s w.1 w.2‖ ≤
        Lx * ‖z.1 - w.1‖ + Lv * ‖z.2 - w.2‖)
    (hRegion : ∀ᶠ i in l,
      (∀ᵐ a ∂(initialProbability (H i) : Measure (Fin 3 → ℝ)),
        (∀ s ∈ Icc 0 T,
          (WithLp.toLp 2 (Phi i (s, a)),
            WithLp.toLp 2 (spatialVelocity (P i) g (amp i) (phase i) (s, Phi i (s, a)))) ∈ Ω s) ∧
        (∀ s ∈ Icc 0 T, Phi i (s, a) ∈ K s)) ∧
      Integrable (fun a => ‖WithLp.toLp 2 a - Y 0‖)
        (initialProbability (H i) : Measure (Fin 3 → ℝ)) ∧
      Integrable (fun a =>
        ‖WithLp.toLp 2 (spatialVelocity (P i) g (amp i) (phase i) (0, a)) - W 0‖)
        (initialProbability (H i) : Measure (Fin 3 → ℝ)))
    (hdx : Tendsto (fun i => ∫ a, ‖WithLp.toLp 2 a - Y 0‖
      ∂(initialProbability (H i) : Measure (Fin 3 → ℝ))) l (𝓝 0))
    (hdb : Tendsto (fun i => ∫ a,
      ‖WithLp.toLp 2 (spatialVelocity (P i) g (amp i) (phase i) (0, a)) - W 0‖
        ∂(initialProbability (H i) : Measure (Fin 3 → ℝ))) l (𝓝 0)) :
    Concentrates (fun i t => currentProbability (H i) t) Y T l := by
  let C := sourceCoefficient c umin δ Bv Bg
  let B := gradientSupFamily P g amp phase T K hreg hDbnd
  let F := CurvedIntegratedForceEnvelope.envelope (C * c ^ 2) B
  have hcriterion := uniform_force_criterion P g amp phase T K hreg hDbnd hc
    hmin hδ hBv hBg hu hq hratio hRaise hMeas hInt hLim
  rcases hcriterion with ⟨_, hFn, _, hFI, hFb, _, hFlim⟩
  have hGood : ∀ᶠ i in l, SourceControl (H i) Ω (F i) (Y 0) (W 0) := by
    filter_upwards [hRegion] with i hi
    refine {
      force_integrable := hFI i
      force_nonneg := fun s _ => hFn i s
      label_controls := ?_
      position_integrable := hi.2.1
      velocity_integrable := hi.2.2 }
    filter_upwards [hi.1] with a ha
    refine ⟨ha.1, ?_⟩
    filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
    exact hFb i s hs (Phi i (s, a)) (ha.2 s hs)
  exact family_weak_concentration_of_eventually P g amp phase Phi domains H l hc
    hT hLx hLv hRef hG hGood hdx hdb hFlim

/-- Actual small scalar defect and integrated full-gradient control give eventual physical force control and genuine current concentration. -/
theorem family_concentration_of_small_defect
    (P : ι → MassiveParameters) (g : Covector → Mat4)
    (amp phase : ι → Covector → ℝ) (Phi : ι → ℝ × (Fin 3 → ℝ) → (Fin 3 → ℝ))
    (domains : ι → Set (Fin 3 → ℝ))
    (H : ∀ i, FiniteFlowData (P i) g (amp i) (phase i) (Phi i) T (domains i))
    (l : Filter ι) (K : ℝ → Set (Fin 3 → ℝ))
    (hreg : ∀ i, RegularOnTube (P i) g (amp i) (phase i) T K)
    (hDbnd : ∀ i, DifferentialBoundedOnTube (P i) g (amp i) T K)
    (hqbnd : ∀ i, DefectBoundedOnTube (P i) g (amp i) T K)
    {umin Bv Bg : ℝ} (hc : ∀ i, (P i).c = c)
    (hmin : 0 < umin) (hBv : 0 ≤ Bv) (hBg : 0 ≤ Bg)
    (hu : ∀ i s, s ∈ Icc 0 T → ∀ z ∈ K s,
      umin ≤ |normalizedVelocity (P i) g (amp i) (phase i)
        (coordinatePoint (P i).c s z) 0|)
    (hratio : ∀ i s, s ∈ Icc 0 T → ∀ z ∈ K s, ∀ j : Fin 3,
      |normalizedVelocity (P i) g (amp i) (phase i) (coordinatePoint (P i).c s z) j.succ /
        normalizedVelocity (P i) g (amp i) (phase i) (coordinatePoint (P i).c s z) 0| ≤ Bv)
    (hRaise : ∀ i s, s ∈ Icc 0 T → ∀ z ∈ K s,
      ‖raiseMap ((g (coordinatePoint (P i).c s z))⁻¹)‖ ≤ Bg)
    (hMeas : ∀ i, Measurable (gradientSupFamily P g amp phase T K hreg hDbnd i))
    (hInt : ∀ i, IntervalIntegrable (gradientSupFamily P g amp phase T K hreg hDbnd i)
      volume 0 T)
    (hLim : Tendsto (fun i => ∫ s in 0..T,
      gradientSupFamily P g amp phase T K hreg hDbnd i s) l (𝓝 0))
    (hSmall : Tendsto (fun i => defectSup (P i) g (amp i) (phase i) T K
      (hreg i) (hqbnd i)) l (𝓝 0))
    (hT : 0 < T) (hLx : 0 ≤ Lx) (hLv : 0 ≤ Lv)
    (hRef : ReferenceCurve (geodesic c g) Ω T Y W)
    (hG : ∀ s ∈ Icc 0 T, ∀ z ∈ Ω s, ∀ w ∈ Ω s,
      ‖geodesic c g s z.1 z.2 - geodesic c g s w.1 w.2‖ ≤
        Lx * ‖z.1 - w.1‖ + Lv * ‖z.2 - w.2‖)
    (hRegion : ∀ᶠ i in l,
      (∀ᵐ a ∂(initialProbability (H i) : Measure (Fin 3 → ℝ)),
        (∀ s ∈ Icc 0 T,
          (WithLp.toLp 2 (Phi i (s, a)),
            WithLp.toLp 2 (spatialVelocity (P i) g (amp i) (phase i) (s, Phi i (s, a)))) ∈ Ω s) ∧
        (∀ s ∈ Icc 0 T, Phi i (s, a) ∈ K s)) ∧
      Integrable (fun a => ‖WithLp.toLp 2 a - Y 0‖)
        (initialProbability (H i) : Measure (Fin 3 → ℝ)) ∧
      Integrable (fun a =>
        ‖WithLp.toLp 2 (spatialVelocity (P i) g (amp i) (phase i) (0, a)) - W 0‖)
        (initialProbability (H i) : Measure (Fin 3 → ℝ)))
    (hdx : Tendsto (fun i => ∫ a, ‖WithLp.toLp 2 a - Y 0‖
      ∂(initialProbability (H i) : Measure (Fin 3 → ℝ))) l (𝓝 0))
    (hdb : Tendsto (fun i => ∫ a,
      ‖WithLp.toLp 2 (spatialVelocity (P i) g (amp i) (phase i) (0, a)) - W 0‖
        ∂(initialProbability (H i) : Measure (Fin 3 → ℝ))) l (𝓝 0)) :
    Concentrates (fun i t => currentProbability (H i) t) Y T l := by
  let C := sourceCoefficient c umin (1 / 2) Bv Bg
  let B := gradientSupFamily P g amp phase T K hreg hDbnd
  let F := CurvedIntegratedForceEnvelope.envelope (C * c ^ 2) B
  have hcriterion := CurvedSmallDefectCriterion.small_defect_force_criterion
    P g amp phase T K hreg hDbnd hqbnd hc hmin hBv hBg hu hratio hRaise
    hMeas hInt hLim hSmall
  rcases hcriterion with ⟨_, hFn, _, hFI, hFb, _, hFlim⟩
  have hGood : ∀ᶠ i in l, SourceControl (H i) Ω (F i) (Y 0) (W 0) := by
    filter_upwards [hRegion, hFb] with i hi hforce
    refine {
      force_integrable := hFI i
      force_nonneg := fun s _ => hFn i s
      label_controls := ?_
      position_integrable := hi.2.1
      velocity_integrable := hi.2.2 }
    filter_upwards [hi.1] with a ha
    refine ⟨ha.1, ?_⟩
    filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
    exact (hforce s hs (Phi i (s, a)) (ha.2 s hs)).2
  exact family_weak_concentration_of_eventually P g amp phase Phi domains H l hc
    hT hLx hLv hRef hG hGood hdx hdb hFlim

end FoliationQM.CurvedCurrentGradientConcentration
