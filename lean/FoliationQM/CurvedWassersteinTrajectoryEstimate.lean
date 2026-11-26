module

public import FoliationQM.CurvedProbabilityTrajectoryEstimate
public import FoliationQM.WassersteinTrajectoryEstimate

/-!

# Genuine Wasserstein concentration for actual polar KG curves

Actual first-order KG curve data and genuine initial moment integrability
give finite transport cost to the reference geodesic. The exact finite-time
bound and its supremum follow from the proved physical probability moment
estimate and the genuine coupling-based Dirac identity.

The family theorem retains an explicit asymptotic filter, common speed of
light and background geodesic field, and one eventual event of actual
analytic hypotheses. It never replaces eventual normalization or force
control by an all-index claim. Identification of the supplied probability
with geometric conserved current flux remains a separate bridge.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.CurvedWassersteinTrajectoryEstimate

open LorentzMatrixGroup CurvedCoordinateDynamics CurvedCoordinateTrajectories CurvedQuantumForceCriterion
  CurvedEuclideanTrajectories CurvedProbabilityTrajectoryEstimate
  ProbabilityTrajectoryEstimate WeightedPhaseError WassersteinCoupling
  UniformTransportConcentration MeasureTheory Set Filter
open scoped ENNReal Topology Matrix.Norms.Operator

variable {Label : Type*} [MeasurableSpace Label]
  {p : MassiveParameters} {g : Covector → Mat4} {R S : Covector → ℝ}
  {T Lx Lv : ℝ} {Ω : ℝ → Set (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3))}
  {Γ : ℝ → Label → Covector} {Y W : ℝ → EuclideanSpace ℝ (Fin 3)} {A : ℝ → ℝ}

/-- Actual polar KG trajectories give finite genuine Dirac transport cost and the exact source bound, using derived transported moments rather than an assumed Wasserstein estimate. -/
theorem finite_cost_and_bound (μ : Measure Label) [IsProbabilityMeasure μ]
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
    (hb : Integrable (fun a => ‖velocity p g R S (fun s => Γ s a) 0 - W 0‖) μ) :
    ∀ t ∈ Icc 0 T,
      eW1 (μ.map (fun a => position (fun s => Γ s a) t)) (Measure.dirac (Y t)) ≠ ∞ ∧
      (eW1 (μ.map (fun a => position (fun s => Γ s a) t)) (Measure.dirac (Y t))).toReal ≤
        Real.exp (rate T Lx Lv * T) *
          ((∫ a, ‖position (fun s => Γ s a) 0 - Y 0‖ ∂μ) +
            T * (∫ a, ‖velocity p g R S (fun s => Γ s a) 0 - W 0‖ ∂μ) +
            T * ∫ s in 0..T, A s) := by
  intro t ht
  have hm := mapped_position_moment_bound_of_polar μ hT hLx hLv hRef hG hA hAn
    hCurves hX ha hb t ht
  obtain ⟨hfinite, heq⟩ := WassersteinDirac.eW1_dirac_finite_and_toReal_norm hm.2.1
  exact ⟨hfinite, heq.trans_le hm.2.2⟩

/-- The actual supremum over the closed time interval satisfies the exact physical source bound, with genuine finiteness of every transport cost explicitly retained. -/
theorem sup_bound (μ : Measure Label) [IsProbabilityMeasure μ]
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
    (hb : Integrable (fun a => ‖velocity p g R S (fun s => Γ s a) 0 - W 0‖) μ) :
    (∀ t ∈ Icc 0 T,
      eW1 (μ.map (fun a => position (fun s => Γ s a) t)) (Measure.dirac (Y t)) ≠ ∞) ∧
    0 ≤ timeSup (fun t =>
      (eW1 (μ.map (fun a => position (fun s => Γ s a) t)) (Measure.dirac (Y t))).toReal) T ∧
    timeSup (fun t =>
      (eW1 (μ.map (fun a => position (fun s => Γ s a) t)) (Measure.dirac (Y t))).toReal) T ≤
      Real.exp (rate T Lx Lv * T) *
        ((∫ a, ‖position (fun s => Γ s a) 0 - Y 0‖ ∂μ) +
          T * (∫ a, ‖velocity p g R S (fun s => Γ s a) 0 - W 0‖ ∂μ) +
          T * ∫ s in 0..T, A s) :=
  finite_cost_sup_bound hT.le
    (finite_cost_and_bound μ hT hLx hLv hRef hG hA hAn hCurves hX ha hb)

section Family

variable {ι : Type*}

/-- An explicit-filter family of actual polar KG curves with common speed of light and eventual analytic controls has eventually finite genuine transport costs converging uniformly in time, with the actual time supremum also tending to zero. -/
theorem family_concentration_of_eventually
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
    let ν := fun i t => (μ i).map (fun a => position (fun s => Γ i s a) t)
    (∀ᶠ i in l, ∀ t ∈ Icc 0 T, eW1 (ν i t) (Measure.dirac (Y t)) ≠ ∞) ∧
      TendstoUniformlyOn (fun i t => (eW1 (ν i t) (Measure.dirac (Y t))).toReal)
        (fun _ => 0) l (Icc 0 T) ∧
      Tendsto (fun i => timeSup (fun t => (eW1 (ν i t) (Measure.dirac (Y t))).toReal) T)
        l (𝓝 0) := by
  dsimp only
  apply WassersteinTrajectoryEstimate.family_concentration_of_eventually
    (X := fun i t a => position (fun s => Γ i s a) t)
    (V := fun i t a => velocity (P i) g (amp i) (phase i) (fun s => Γ i s a) t)
    (f := fun i t a => force (P i) g (amp i) (phase i) (fun s => Γ i s a) t)
    μ l hT hLx hLv hRef hG ?_ hdx hdb hJ
  filter_upwards [hGood] with i hi
  refine ⟨hi.1, hi.2.1, ?_, hi.2.2.2⟩
  filter_upwards [hi.2.2.1] with a ha
  simpa only [hc i] using controlledCurve_of_polar ha.1 ha.2

end Family
end FoliationQM.CurvedWassersteinTrajectoryEstimate
