module

public import FoliationQM.CurvedCurrentConcentration
public import FoliationQM.UniformWeakConcentration
public import FoliationQM.WassersteinMetricTransfer

/-!
# Weak and metric concentration of actual geometric current

The probability family is the normalized geometric current constructed from
actual polar Klein–Gordon flow data. Its derived finite transport bounds give
uniform convergence of each bounded continuous test and genuine weak
convergence at every interval time. Alternative metric realizations retain
actual almost-everywhere measurability and a uniform regional distance factor.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.CurvedCurrentWeakConcentration

open LorentzMatrixGroup CurvedCoordinateCurrent CurvedCoordinateDynamics
  CurvedCurrentTransport CurvedCurrentConcentration CurvedEuclideanTrajectories
  ProbabilityTrajectoryEstimate WeightedPhaseError WassersteinCoupling
  UniformTransportConcentration MeasureTheory Set Filter
open scoped ENNReal NNReal Topology Matrix.Norms.Operator BoundedContinuousFunction

variable {ι : Type*}

/-- Finite uniform Wasserstein concentration, uniform bounded-continuous tests, and actual probability weak convergence. -/
def Concentrates (ν : ι → ℝ → ProbabilityMeasure (EuclideanSpace ℝ (Fin 3)))
    (Y : ℝ → EuclideanSpace ℝ (Fin 3)) (T : ℝ) (l : Filter ι) : Prop :=
  (∀ᶠ i in l, ∀ t ∈ Icc 0 T,
    eW1 (ν i t : Measure _) (Measure.dirac (Y t)) ≠ ∞) ∧
  TendstoUniformlyOn (fun i t => (eW1 (ν i t : Measure _) (Measure.dirac (Y t))).toReal)
    (fun _ => 0) l (Icc 0 T) ∧
  Tendsto (fun i => timeSup (fun t =>
    (eW1 (ν i t : Measure _) (Measure.dirac (Y t))).toReal) T) l (𝓝 0) ∧
  (∀ f : EuclideanSpace ℝ (Fin 3) →ᵇ ℝ,
    TendstoUniformlyOn (fun i t => ∫ x, f x ∂(ν i t : Measure _))
      (fun t => f (Y t)) l (Icc 0 T)) ∧
  (∀ t ∈ Icc 0 T, Tendsto (fun i => ν i t) l
    (𝓝 (Measure.dirac (Y t)).toProbabilityMeasure))

variable {p : MassiveParameters} {g : Covector → Mat4} {R S : Covector → ℝ}
  {Phi : ℝ × (Fin 3 → ℝ) → (Fin 3 → ℝ)} {A : Set (Fin 3 → ℝ)}
  {T Lx Lv : ℝ} {Ω : ℝ → Set (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3))}
  {Y W : ℝ → EuclideanSpace ℝ (Fin 3)} {F : ℝ → ℝ}
  {Target : Type*} [MetricSpace Target] [MeasurableSpace Target] [BorelSpace Target]

/-- A genuine regional metric realization transfers the actual current supremum with its positive coefficient. -/
theorem metric_sup_bound (h : FiniteFlowData p g R S Phi T A)
    (hT : 0 < T) (hLx : 0 ≤ Lx) (hLv : 0 ≤ Lv)
    (hRef : ReferenceCurve (geodesic p.c g) Ω T Y W)
    (hG : ∀ s ∈ Icc 0 T, ∀ z ∈ Ω s, ∀ w ∈ Ω s,
      ‖geodesic p.c g s z.1 z.2 - geodesic p.c g s w.1 w.2‖ ≤
        Lx * ‖z.1 - w.1‖ + Lv * ‖z.2 - w.2‖)
    (hControl : SourceControl h Ω F (Y 0) (W 0))
    (f : ℝ → EuclideanSpace ℝ (Fin 3) → Target) (L : ℝ≥0) (hL : 0 < (L : ℝ))
    (hMaps : ∀ t ∈ Icc 0 T,
      AEMeasurable (f t) (currentProbability h t : Measure _) ∧
      ∀ᵐ x ∂(currentProbability h t : Measure _),
        edist (f t x) (f t (Y t)) ≤ (L : ℝ≥0∞) * edist x (Y t)) :
    let ν := fun t => (currentProbability h t : Measure _).map (f t)
    0 < (L : ℝ) * Real.exp (rate T Lx Lv * T) ∧
    (∀ t ∈ Icc 0 T, eW1 (ν t) (Measure.dirac (f t (Y t))) ≠ ∞) ∧
    0 ≤ timeSup (fun t => (eW1 (ν t) (Measure.dirac (f t (Y t)))).toReal) T ∧
    timeSup (fun t => (eW1 (ν t) (Measure.dirac (f t (Y t)))).toReal) T ≤
      ((L : ℝ) * Real.exp (rate T Lx Lv * T)) *
        ((∫ a, ‖WithLp.toLp 2 a - Y 0‖ ∂(initialProbability h : Measure _)) +
          T * (∫ a, ‖WithLp.toLp 2 (spatialVelocity p g R S (0, a)) - W 0‖
            ∂(initialProbability h : Measure _)) + T * ∫ s in 0..T, F s) := by
  dsimp only
  refine ⟨mul_pos hL (Real.exp_pos _), ?_⟩
  apply finite_cost_sup_bound hT.le
  intro t ht
  have hs := CurvedCurrentConcentration.finite_cost_and_bound h hT hLx hLv hRef hG hControl t ht
  rw [← currentProbability_eq_density h ht] at hs
  have hm := WassersteinMetricTransfer.eW1_map_dirac_finite_and_toReal_le_of_ae
    (f := f t) (L := L) (y := Y t)
    (currentProbability h t : Measure (EuclideanSpace ℝ (Fin 3)))
    (hMaps t ht).1 (hMaps t ht).2 hs.1
  refine ⟨hm.1, hm.2.trans ?_⟩
  exact (mul_le_mul_of_nonneg_left hs.2 L.coe_nonneg).trans_eq (mul_assoc _ _ _).symm

/-- Actual current source controls and initial moments imply all five concentration conclusions. -/
theorem family_weak_concentration_of_eventually
    (P : ι → MassiveParameters) (g : Covector → Mat4)
    (amp phase : ι → Covector → ℝ)
    (Phi : ι → ℝ × (Fin 3 → ℝ) → (Fin 3 → ℝ)) (domains : ι → Set (Fin 3 → ℝ))
    (H : ∀ i, FiniteFlowData (P i) g (amp i) (phase i) (Phi i) T (domains i)) (l : Filter ι)
    {c : ℝ} (hc : ∀ i, (P i).c = c) {F : ι → ℝ → ℝ}
    (hT : 0 < T) (hLx : 0 ≤ Lx) (hLv : 0 ≤ Lv)
    (hRef : ReferenceCurve (geodesic c g) Ω T Y W)
    (hG : ∀ s ∈ Icc 0 T, ∀ z ∈ Ω s, ∀ w ∈ Ω s,
      ‖geodesic c g s z.1 z.2 - geodesic c g s w.1 w.2‖ ≤
        Lx * ‖z.1 - w.1‖ + Lv * ‖z.2 - w.2‖)
    (hGood : ∀ᶠ i in l, SourceControl (H i) Ω (F i) (Y 0) (W 0))
    (hdx : Tendsto (fun i => ∫ a, ‖WithLp.toLp 2 a - Y 0‖
      ∂(initialProbability (H i) : Measure _)) l (𝓝 0))
    (hdb : Tendsto (fun i => ∫ a,
      ‖WithLp.toLp 2 (spatialVelocity (P i) g (amp i) (phase i) (0, a)) - W 0‖
        ∂(initialProbability (H i) : Measure _)) l (𝓝 0))
    (hJ : Tendsto (fun i => ∫ s in 0..T, F i s) l (𝓝 0)) :
    Concentrates (fun i t => currentProbability (H i) t) Y T l := by
  have h := CurvedCurrentConcentration.family_concentration_of_eventually
    P g amp phase Phi domains H l hc hT hLx hLv hRef hG hGood hdx hdb hJ
  refine ⟨h.1, h.2.1, h.2.2, ?_, ?_⟩
  · exact UniformWeakConcentration.tendstoUniformlyOn_integral_of_uniform_cost
      (fun i t => currentProbability (H i) t) l hRef.position_continuous h.1 h.2.1
  · exact UniformWeakConcentration.tendsto_probabilityMeasure_of_uniform_cost
      (fun i t => currentProbability (H i) t) l hRef.position_continuous h.1 h.2.1

/-- A uniformly controlled actual metric realization inherits current concentration along the explicit family filter. -/
theorem family_metric_concentration_of_eventually
    (P : ι → MassiveParameters) (g : Covector → Mat4)
    (amp phase : ι → Covector → ℝ)
    (Phi : ι → ℝ × (Fin 3 → ℝ) → (Fin 3 → ℝ)) (domains : ι → Set (Fin 3 → ℝ))
    (H : ∀ i, FiniteFlowData (P i) g (amp i) (phase i) (Phi i) T (domains i)) (l : Filter ι)
    {c : ℝ} (hc : ∀ i, (P i).c = c) {F : ι → ℝ → ℝ}
    (hT : 0 < T) (hLx : 0 ≤ Lx) (hLv : 0 ≤ Lv)
    (hRef : ReferenceCurve (geodesic c g) Ω T Y W)
    (hG : ∀ s ∈ Icc 0 T, ∀ z ∈ Ω s, ∀ w ∈ Ω s,
      ‖geodesic c g s z.1 z.2 - geodesic c g s w.1 w.2‖ ≤
        Lx * ‖z.1 - w.1‖ + Lv * ‖z.2 - w.2‖)
    (hGood : ∀ᶠ i in l, SourceControl (H i) Ω (F i) (Y 0) (W 0))
    (hdx : Tendsto (fun i => ∫ a, ‖WithLp.toLp 2 a - Y 0‖
      ∂(initialProbability (H i) : Measure _)) l (𝓝 0))
    (hdb : Tendsto (fun i => ∫ a,
      ‖WithLp.toLp 2 (spatialVelocity (P i) g (amp i) (phase i) (0, a)) - W 0‖
        ∂(initialProbability (H i) : Measure _)) l (𝓝 0))
    (hJ : Tendsto (fun i => ∫ s in 0..T, F i s) l (𝓝 0))
    (f : ℝ → EuclideanSpace ℝ (Fin 3) → Target) (L : ℝ≥0)
    (hMaps : ∀ᶠ i in l, ∀ t ∈ Icc 0 T,
      AEMeasurable (f t) (currentProbability (H i) t : Measure _) ∧
      ∀ᵐ x ∂(currentProbability (H i) t : Measure _),
        edist (f t x) (f t (Y t)) ≤ (L : ℝ≥0∞) * edist x (Y t)) :
    let ν := fun i t => (currentProbability (H i) t : Measure _).map (f t)
    (∀ᶠ i in l, ∀ t ∈ Icc 0 T, eW1 (ν i t) (Measure.dirac (f t (Y t))) ≠ ∞) ∧
    TendstoUniformlyOn (fun i t => (eW1 (ν i t) (Measure.dirac (f t (Y t)))).toReal)
      (fun _ => 0) l (Icc 0 T) ∧
    Tendsto (fun i => timeSup (fun t =>
      (eW1 (ν i t) (Measure.dirac (f t (Y t)))).toReal) T) l (𝓝 0) := by
  dsimp only
  apply WassersteinMetricTransfer.family_concentration_of_eventual_bound
    (f := f) (L := L) (Y := Y)
    (ν := fun i t => (currentProbability (H i) t : Measure _))
    (B := fun i => Real.exp (rate T Lx Lv * T) *
      ((∫ a, ‖WithLp.toLp 2 a - Y 0‖ ∂(initialProbability (H i) : Measure _)) +
        T * (∫ a, ‖WithLp.toLp 2 (spatialVelocity (P i) g (amp i) (phase i) (0, a)) - W 0‖
          ∂(initialProbability (H i) : Measure _)) + T * ∫ s in 0..T, F i s))
    l hT.le ?_ hMaps (source_majorant_tendsto l T Lx Lv hdx hdb hJ)
  filter_upwards [hGood] with i hi
  intro t ht
  rw [currentProbability_eq_density (H i) ht]
  exact CurvedCurrentConcentration.finite_cost_and_bound
    (H i) hT hLx hLv (by simpa only [hc i] using hRef)
    (by simpa only [hc i] using hG) hi t ht

end FoliationQM.CurvedCurrentWeakConcentration
