module

public import FoliationQM.CurvedWassersteinTrajectoryEstimate
public import FoliationQM.UniformWeakConcentration
public import FoliationQM.WassersteinMetricTransfer

/-!
# Weak and metric concentration for actual polar KG curves

The physical inputs are the actual first-order curves, force envelopes,
initial moments and common reference field used by the preceding transport
estimate. Uniform weak convergence and metric comparison are derived from
that estimate. Each bounded continuous test converges uniformly in time;
the probability-valued family converges in its genuine weak topology at
each time. Alternative metrics retain their actual distance comparison and
the corresponding change of constant.

The supplied transported probability is not yet identified here with
geometric current flux. That source obligation remains separately tracked.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.CurvedWeakConcentration

open LorentzMatrixGroup CurvedCoordinateDynamics CurvedCoordinateTrajectories CurvedQuantumForceCriterion
  CurvedEuclideanTrajectories CurvedProbabilityTrajectoryEstimate
  ProbabilityTrajectoryEstimate WeightedPhaseError WassersteinCoupling
  UniformTransportConcentration MeasureTheory Set Filter
open scoped ENNReal NNReal Topology Matrix.Norms.Operator BoundedContinuousFunction

variable {Label : Type*} [MeasurableSpace Label]
  {p : MassiveParameters} {g : Covector → Mat4} {R S : Covector → ℝ}
  {T Lx Lv : ℝ} {Ω : ℝ → Set (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3))}
  {Γ : ℝ → Label → Covector} {Y W : ℝ → EuclideanSpace ℝ (Fin 3)} {A : ℝ → ℝ}
  {F : Type*} [MetricSpace F] [MeasurableSpace F] [BorelSpace F]

/-- Actual regional metric comparison transfers the physical time supremum, retaining a strictly positive comparison coefficient. -/
theorem metric_sup_bound (μ : Measure Label) [IsProbabilityMeasure μ]
    (hT : 0 < T) (hLx : 0 ≤ Lx) (hLv : 0 ≤ Lv)
    (hRef : ReferenceCurve (geodesic p.c g) Ω T Y W)
    (hG : ∀ s ∈ Icc 0 T, ∀ z ∈ Ω s, ∀ w ∈ Ω s,
      ‖geodesic p.c g s z.1 z.2 - geodesic p.c g s w.1 w.2‖ ≤
        Lx * ‖z.1 - w.1‖ + Lv * ‖z.2 - w.2‖)
    (hA : IntervalIntegrable A volume 0 T) (hAn : ∀ s ∈ Icc 0 T, 0 ≤ A s)
    (hCurves : ∀ᵐ a ∂μ, PolarCurveOn p g R S T Ω (fun s => Γ s a) ∧
      ∀ᵐ s ∂volume.restrict (Icc 0 T),
        spatialForceNorm p g R S s (spatialPart (Γ s a)) ≤ A s)
    (hX : ∀ t ∈ Icc 0 T, AEMeasurable (fun a => position (fun s => Γ s a) t) μ)
    (ha : Integrable (fun a => ‖position (fun s => Γ s a) 0 - Y 0‖) μ)
    (hb : Integrable (fun a => ‖velocity p g R S (fun s => Γ s a) 0 - W 0‖) μ)
    (f : ℝ → EuclideanSpace ℝ (Fin 3) → F) (L : ℝ≥0) (hL : 0 < (L : ℝ))
    (hMaps : ∀ t ∈ Icc 0 T,
      AEMeasurable (f t) (μ.map (fun a => position (fun s => Γ s a) t)) ∧
      ∀ᵐ x ∂(μ.map (fun a => position (fun s => Γ s a) t)),
        edist (f t x) (f t (Y t)) ≤ (L : ℝ≥0∞) * edist x (Y t)) :
    let ν := fun t => (μ.map (fun a => position (fun s => Γ s a) t)).map (f t)
    0 < (L : ℝ) * Real.exp (rate T Lx Lv * T) ∧
    (∀ t ∈ Icc 0 T, eW1 (ν t) (Measure.dirac (f t (Y t))) ≠ ∞) ∧
    0 ≤ timeSup (fun t => (eW1 (ν t) (Measure.dirac (f t (Y t)))).toReal) T ∧
    timeSup (fun t => (eW1 (ν t) (Measure.dirac (f t (Y t)))).toReal) T ≤
      ((L : ℝ) * Real.exp (rate T Lx Lv * T)) *
        ((∫ a, ‖position (fun s => Γ s a) 0 - Y 0‖ ∂μ) +
          T * (∫ a, ‖velocity p g R S (fun s => Γ s a) 0 - W 0‖ ∂μ) +
          T * ∫ s in 0..T, A s) := by
  dsimp only
  refine ⟨mul_pos hL (Real.exp_pos _), ?_⟩
  apply finite_cost_sup_bound hT.le
  intro t ht
  have hs := CurvedWassersteinTrajectoryEstimate.finite_cost_and_bound
    μ hT hLx hLv hRef hG hA hAn hCurves hX ha hb t ht
  have hm := WassersteinMetricTransfer.eW1_map_dirac_finite_and_toReal_le_of_ae
    (μ.map (fun a => position (fun s => Γ s a) t))
    (hMaps t ht).1 (hMaps t ht).2 hs.1
  refine ⟨hm.1, hm.2.trans ?_⟩
  exact (mul_le_mul_of_nonneg_left hs.2 L.coe_nonneg).trans_eq (mul_assoc _ _ _).symm

section Family

variable {ι : Type*}

/-- Actual eventual polar KG controls imply uniform convergence of every bounded continuous test and genuine probability weak convergence, together with finite uniform Wasserstein concentration. -/
theorem family_weak_concentration_of_eventually
    (P : ι → MassiveParameters) (g : Covector → Mat4)
    (amp phase : ι → Covector → ℝ) (Γ : ι → ℝ → Label → Covector)
    (μ : ι → Measure Label) [∀ i, IsProbabilityMeasure (μ i)] (l : Filter ι)
    {c : ℝ} (hc : ∀ i, (P i).c = c) {A : ι → ℝ → ℝ}
    (hT : 0 < T) (hLx : 0 ≤ Lx) (hLv : 0 ≤ Lv)
    (hRef : ReferenceCurve (geodesic c g) Ω T Y W)
    (hG : ∀ s ∈ Icc 0 T, ∀ z ∈ Ω s, ∀ w ∈ Ω s,
      ‖geodesic c g s z.1 z.2 - geodesic c g s w.1 w.2‖ ≤
        Lx * ‖z.1 - w.1‖ + Lv * ‖z.2 - w.2‖)
    (hGood : ∀ᶠ i in l,
      IntervalIntegrable (A i) volume 0 T ∧
      (∀ s ∈ Icc 0 T, 0 ≤ A i s) ∧
      (∀ᵐ a ∂μ i, PolarCurveOn (P i) g (amp i) (phase i) T Ω (fun s => Γ i s a) ∧
        ∀ᵐ s ∂volume.restrict (Icc 0 T),
          spatialForceNorm (P i) g (amp i) (phase i) s (spatialPart (Γ i s a)) ≤ A i s) ∧
      (∀ t ∈ Icc 0 T, AEMeasurable (fun a => position (fun s => Γ i s a) t) (μ i)) ∧
      Integrable (fun a => ‖position (fun s => Γ i s a) 0 - Y 0‖) (μ i) ∧
      Integrable (fun a => ‖velocity (P i) g (amp i) (phase i) (fun s => Γ i s a) 0 - W 0‖)
        (μ i))
    (hdx : Tendsto (fun i => ∫ a, ‖position (fun s => Γ i s a) 0 - Y 0‖ ∂μ i) l (𝓝 0))
    (hdb : Tendsto (fun i =>
      ∫ a, ‖velocity (P i) g (amp i) (phase i) (fun s => Γ i s a) 0 - W 0‖ ∂μ i) l (𝓝 0))
    (hJ : Tendsto (fun i => ∫ s in 0..T, A i s) l (𝓝 0)) :
    let ν : ι → ℝ → ProbabilityMeasure (EuclideanSpace ℝ (Fin 3)) :=
      fun i t => ((μ i).map (fun a => position (fun s => Γ i s a) t)).toProbabilityMeasure
    (∀ᶠ i in l, ∀ t ∈ Icc 0 T, eW1 (ν i t : Measure _) (Measure.dirac (Y t)) ≠ ∞) ∧
    TendstoUniformlyOn (fun i t => (eW1 (ν i t : Measure _) (Measure.dirac (Y t))).toReal)
      (fun _ => 0) l (Icc 0 T) ∧
    Tendsto (fun i => timeSup (fun t =>
      (eW1 (ν i t : Measure _) (Measure.dirac (Y t))).toReal) T) l (𝓝 0) ∧
    (∀ f : EuclideanSpace ℝ (Fin 3) →ᵇ ℝ,
      TendstoUniformlyOn (fun i t => ∫ x, f x ∂(ν i t : Measure _))
        (fun t => f (Y t)) l (Icc 0 T)) ∧
    (∀ t ∈ Icc 0 T, Tendsto (fun i => ν i t) l
      (𝓝 (Measure.dirac (Y t)).toProbabilityMeasure)) := by
  dsimp only
  have h := CurvedWassersteinTrajectoryEstimate.family_concentration_of_eventually
    P g amp phase Γ μ l hc hT hLx hLv hRef hG hGood hdx hdb hJ
  refine ⟨h.1, h.2.1, h.2.2, ?_, ?_⟩
  · exact UniformWeakConcentration.tendstoUniformlyOn_integral_of_uniform_cost
      (fun i t => ((μ i).map (fun a => position (fun s => Γ i s a) t)).toProbabilityMeasure)
      l hRef.position_continuous h.1 h.2.1
  · exact UniformWeakConcentration.tendsto_probabilityMeasure_of_uniform_cost
      (fun i t => ((μ i).map (fun a => position (fun s => Γ i s a) t)).toProbabilityMeasure)
      l hRef.position_continuous h.1 h.2.1

/-- A time-dependent target realization with one uniform regional distance bound inherits physical concentration; the actual source majorant is derived from the polar curves. -/
theorem family_metric_concentration_of_eventually
    (P : ι → MassiveParameters) (g : Covector → Mat4)
    (amp phase : ι → Covector → ℝ) (Γ : ι → ℝ → Label → Covector)
    (μ : ι → Measure Label) [∀ i, IsProbabilityMeasure (μ i)] (l : Filter ι)
    {c : ℝ} (hc : ∀ i, (P i).c = c) {A : ι → ℝ → ℝ}
    (hT : 0 < T) (hLx : 0 ≤ Lx) (hLv : 0 ≤ Lv)
    (hRef : ReferenceCurve (geodesic c g) Ω T Y W)
    (hG : ∀ s ∈ Icc 0 T, ∀ z ∈ Ω s, ∀ w ∈ Ω s,
      ‖geodesic c g s z.1 z.2 - geodesic c g s w.1 w.2‖ ≤
        Lx * ‖z.1 - w.1‖ + Lv * ‖z.2 - w.2‖)
    (hGood : ∀ᶠ i in l,
      IntervalIntegrable (A i) volume 0 T ∧
      (∀ s ∈ Icc 0 T, 0 ≤ A i s) ∧
      (∀ᵐ a ∂μ i, PolarCurveOn (P i) g (amp i) (phase i) T Ω (fun s => Γ i s a) ∧
        ∀ᵐ s ∂volume.restrict (Icc 0 T),
          spatialForceNorm (P i) g (amp i) (phase i) s (spatialPart (Γ i s a)) ≤ A i s) ∧
      (∀ t ∈ Icc 0 T, AEMeasurable (fun a => position (fun s => Γ i s a) t) (μ i)) ∧
      Integrable (fun a => ‖position (fun s => Γ i s a) 0 - Y 0‖) (μ i) ∧
      Integrable (fun a => ‖velocity (P i) g (amp i) (phase i) (fun s => Γ i s a) 0 - W 0‖)
        (μ i))
    (hdx : Tendsto (fun i => ∫ a, ‖position (fun s => Γ i s a) 0 - Y 0‖ ∂μ i) l (𝓝 0))
    (hdb : Tendsto (fun i =>
      ∫ a, ‖velocity (P i) g (amp i) (phase i) (fun s => Γ i s a) 0 - W 0‖ ∂μ i) l (𝓝 0))
    (hJ : Tendsto (fun i => ∫ s in 0..T, A i s) l (𝓝 0))
    (f : ℝ → EuclideanSpace ℝ (Fin 3) → F) (L : ℝ≥0)
    (hMaps : ∀ᶠ i in l, ∀ t ∈ Icc 0 T,
      AEMeasurable (f t) ((μ i).map (fun a => position (fun s => Γ i s a) t)) ∧
      ∀ᵐ x ∂((μ i).map (fun a => position (fun s => Γ i s a) t)),
        edist (f t x) (f t (Y t)) ≤ (L : ℝ≥0∞) * edist x (Y t)) :
    let ν := fun i t => ((μ i).map (fun a => position (fun s => Γ i s a) t)).map (f t)
    (∀ᶠ i in l, ∀ t ∈ Icc 0 T, eW1 (ν i t) (Measure.dirac (f t (Y t))) ≠ ∞) ∧
    TendstoUniformlyOn (fun i t => (eW1 (ν i t) (Measure.dirac (f t (Y t)))).toReal)
      (fun _ => 0) l (Icc 0 T) ∧
    Tendsto (fun i => timeSup (fun t =>
      (eW1 (ν i t) (Measure.dirac (f t (Y t)))).toReal) T) l (𝓝 0) := by
  dsimp only
  apply WassersteinMetricTransfer.family_concentration_of_eventual_bound
    (f := f) (L := L) (Y := Y)
    (ν := fun i t => (μ i).map (fun a => position (fun s => Γ i s a) t))
    (B := fun i => Real.exp (rate T Lx Lv * T) *
      ((∫ a, ‖position (fun s => Γ i s a) 0 - Y 0‖ ∂μ i) +
        T * (∫ a, ‖velocity (P i) g (amp i) (phase i) (fun s => Γ i s a) 0 - W 0‖ ∂μ i) +
        T * ∫ s in 0..T, A i s))
    l hT.le ?_ hMaps (source_majorant_tendsto l T Lx Lv hdx hdb hJ)
  filter_upwards [hGood] with i hi
  exact CurvedWassersteinTrajectoryEstimate.finite_cost_and_bound
    (p := P i) (g := g) (R := amp i) (S := phase i) (Γ := Γ i)
    (μ i) hT hLx hLv
    (by simpa only [hc i] using hRef)
    (by simpa only [hc i] using hG)
    hi.1 hi.2.1 hi.2.2.1 hi.2.2.2.1 hi.2.2.2.2.1 hi.2.2.2.2.2

end Family
end FoliationQM.CurvedWeakConcentration
