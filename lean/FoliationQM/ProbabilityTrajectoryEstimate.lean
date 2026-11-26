module

public import FoliationQM.PhaseTrajectoryEstimate
public import FoliationQM.ProbabilityTransportMoment

/-!
# Trajectory estimates on one full-measure set of initial labels

The structures below contain actual analytic trajectory hypotheses. Their
error estimates follow from the verified coordinate ODE and integral
Grönwall theorem. A single full-measure set of labels carries the hypotheses
throughout the time interval, so the resulting estimates hold for every time
on that same set. No interchange of uncountably many almost-everywhere
statements is used.

Actual measurability of the position maps and integrability of the initial
errors then give finite moments of the genuine pushforward probability
measures, together with the exact averaged error bound.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.ProbabilityTrajectoryEstimate

open WeightedPhaseError MeasureTheory Set
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Actual analytic inputs for one forced coordinate trajectory on the common time interval and phase region. -/
structure ControlledCurve (G : ℝ → E → E → E) (A : ℝ → ℝ)
    (Ω : ℝ → Set (E × E)) (T : ℝ) (X V f : ℝ → E) : Prop where
  /-- The actual position is continuous, including at both interval endpoints. -/
  position_continuous : ContinuousOn X (Icc 0 T)
  /-- The actual velocity is continuous, including at both interval endpoints. -/
  velocity_continuous : ContinuousOn V (Icc 0 T)
  /-- The position derivative is the actual velocity at every interior time. -/
  position_derivative : ∀ s ∈ Ioo 0 T, HasDerivAt X (V s) s
  /-- The velocity derivative is the actual acceleration field plus force at every interior time. -/
  velocity_derivative : ∀ s ∈ Ioo 0 T, HasDerivAt V (G s (X s) (V s) + f s) s
  /-- The actual acceleration field evaluated along the path is continuous. -/
  field_continuous : ContinuousOn (fun s => G s (X s) (V s)) (Icc 0 T)
  /-- The actual along-curve force is continuous. -/
  force_continuous : ContinuousOn f (Icc 0 T)
  /-- The actual position and velocity stay in the specified common phase region. -/
  no_exit : ∀ s ∈ Icc 0 T, (X s, V s) ∈ Ω s
  /-- The same scalar envelope bounds the actual force for almost every interval time. -/
  force_bound : ∀ᵐ s ∂volume.restrict (Icc 0 T), ‖f s‖ ≤ A s

/-- Actual analytic inputs for the unforced reference trajectory in the common phase region. -/
structure ReferenceCurve (G : ℝ → E → E → E) (Ω : ℝ → Set (E × E))
    (T : ℝ) (Y W : ℝ → E) : Prop where
  /-- The reference position is continuous on the closed interval. -/
  position_continuous : ContinuousOn Y (Icc 0 T)
  /-- The reference velocity is continuous on the closed interval. -/
  velocity_continuous : ContinuousOn W (Icc 0 T)
  /-- The reference position derivative is its actual velocity. -/
  position_derivative : ∀ s ∈ Ioo 0 T, HasDerivAt Y (W s) s
  /-- The reference velocity follows the actual unforced acceleration field. -/
  velocity_derivative : ∀ s ∈ Ioo 0 T, HasDerivAt W (G s (Y s) (W s)) s
  /-- The actual acceleration field evaluated along the reference is continuous. -/
  field_continuous : ContinuousOn (fun s => G s (Y s) (W s)) (Icc 0 T)
  /-- The reference position and velocity stay in the same common phase region. -/
  no_exit : ∀ s ∈ Icc 0 T, (Y s, W s) ∈ Ω s

variable [CompleteSpace E]
  {G : ℝ → E → E → E} {A : ℝ → ℝ} {Ω : ℝ → Set (E × E)}
  {T Lx Lv : ℝ} {X V f Y W : ℝ → E}

/-- Actual controlled and reference curves satisfy the exact weighted phase estimate; the structures contain no assumed error inequality. -/
theorem ControlledCurve.phase_error_bound
    (h : ControlledCurve G A Ω T X V f) (hRef : ReferenceCurve G Ω T Y W)
    (hT : 0 < T) (hLx : 0 ≤ Lx) (hLv : 0 ≤ Lv)
    (hG : ∀ s ∈ Icc 0 T, ∀ z ∈ Ω s, ∀ w ∈ Ω s,
      ‖G s z.1 z.2 - G s w.1 w.2‖ ≤ Lx * ‖z.1 - w.1‖ + Lv * ‖z.2 - w.2‖)
    (hA : IntervalIntegrable A volume 0 T) (hAn : ∀ s ∈ Icc 0 T, 0 ≤ A s) :
    ∀ t ∈ Icc 0 T, ‖X t - Y t‖ + T * ‖V t - W t‖ ≤
      Real.exp (rate T Lx Lv * T) *
        (‖X 0 - Y 0‖ + T * ‖V 0 - W 0‖ + T * ∫ s in 0..T, A s) :=
  PhaseTrajectoryEstimate.phase_error_bound_of_continuous hT hLx hLv
    h.position_continuous hRef.position_continuous h.velocity_continuous hRef.velocity_continuous
    h.position_derivative hRef.position_derivative h.velocity_derivative hRef.velocity_derivative
    h.field_continuous hRef.field_continuous h.force_continuous
    (PhaseTrajectoryEstimate.endpoint_bound_of_no_exit h.no_exit hRef.no_exit hG)
    h.force_bound hA hAn

/-- The actual position error of a controlled curve obeys the same integrated-force estimate. -/
theorem ControlledCurve.position_error_bound
    (h : ControlledCurve G A Ω T X V f) (hRef : ReferenceCurve G Ω T Y W)
    (hT : 0 < T) (hLx : 0 ≤ Lx) (hLv : 0 ≤ Lv)
    (hG : ∀ s ∈ Icc 0 T, ∀ z ∈ Ω s, ∀ w ∈ Ω s,
      ‖G s z.1 z.2 - G s w.1 w.2‖ ≤ Lx * ‖z.1 - w.1‖ + Lv * ‖z.2 - w.2‖)
    (hA : IntervalIntegrable A volume 0 T) (hAn : ∀ s ∈ Icc 0 T, 0 ≤ A s) :
    ∀ t ∈ Icc 0 T, ‖X t - Y t‖ ≤ Real.exp (rate T Lx Lv * T) *
      (‖X 0 - Y 0‖ + T * ‖V 0 - W 0‖ + T * ∫ s in 0..T, A s) := by
  intro t ht
  have H := h.phase_error_bound hRef hT hLx hLv hG hA hAn t ht
  have hv := mul_nonneg hT.le (norm_nonneg (V t - W t))
  linarith

section Labels

variable {Label : Type*} [MeasurableSpace Label]
  {X V f : ℝ → Label → E}

/-- One full-measure set of labels carrying the actual curve hypotheses gives the weighted phase estimate at every interval time on that same set. -/
theorem ae_phase_error_bound (μ : Measure Label)
    (hT : 0 < T) (hLx : 0 ≤ Lx) (hLv : 0 ≤ Lv)
    (hRef : ReferenceCurve G Ω T Y W)
    (hG : ∀ s ∈ Icc 0 T, ∀ z ∈ Ω s, ∀ w ∈ Ω s,
      ‖G s z.1 z.2 - G s w.1 w.2‖ ≤ Lx * ‖z.1 - w.1‖ + Lv * ‖z.2 - w.2‖)
    (hA : IntervalIntegrable A volume 0 T) (hAn : ∀ s ∈ Icc 0 T, 0 ≤ A s)
    (hCurves : ∀ᵐ a ∂μ,
      ControlledCurve G A Ω T (fun s => X s a) (fun s => V s a) (fun s => f s a)) :
    ∀ᵐ a ∂μ, ∀ t ∈ Icc 0 T, ‖X t a - Y t‖ + T * ‖V t a - W t‖ ≤
      Real.exp (rate T Lx Lv * T) *
        (‖X 0 a - Y 0‖ + T * ‖V 0 a - W 0‖ + T * ∫ s in 0..T, A s) :=
  hCurves.mono fun _ h => h.phase_error_bound hRef hT hLx hLv hG hA hAn

/-- One common full-measure label set gives the actual position estimate simultaneously for all interval times. -/
theorem ae_position_error_bound (μ : Measure Label)
    (hT : 0 < T) (hLx : 0 ≤ Lx) (hLv : 0 ≤ Lv)
    (hRef : ReferenceCurve G Ω T Y W)
    (hG : ∀ s ∈ Icc 0 T, ∀ z ∈ Ω s, ∀ w ∈ Ω s,
      ‖G s z.1 z.2 - G s w.1 w.2‖ ≤ Lx * ‖z.1 - w.1‖ + Lv * ‖z.2 - w.2‖)
    (hA : IntervalIntegrable A volume 0 T) (hAn : ∀ s ∈ Icc 0 T, 0 ≤ A s)
    (hCurves : ∀ᵐ a ∂μ,
      ControlledCurve G A Ω T (fun s => X s a) (fun s => V s a) (fun s => f s a)) :
    ∀ᵐ a ∂μ, ∀ t ∈ Icc 0 T, ‖X t a - Y t‖ ≤ Real.exp (rate T Lx Lv * T) *
      (‖X 0 a - Y 0‖ + T * ‖V 0 a - W 0‖ + T * ∫ s in 0..T, A s) :=
  hCurves.mono fun _ h => h.position_error_bound hRef hT hLx hLv hG hA hAn

/-- The fixed-time almost-everywhere estimate is projected from the single common label set, without exchanging time and measure quantifiers. -/
theorem ae_position_error_bound_at (μ : Measure Label)
    (hT : 0 < T) (hLx : 0 ≤ Lx) (hLv : 0 ≤ Lv)
    (hRef : ReferenceCurve G Ω T Y W)
    (hG : ∀ s ∈ Icc 0 T, ∀ z ∈ Ω s, ∀ w ∈ Ω s,
      ‖G s z.1 z.2 - G s w.1 w.2‖ ≤ Lx * ‖z.1 - w.1‖ + Lv * ‖z.2 - w.2‖)
    (hA : IntervalIntegrable A volume 0 T) (hAn : ∀ s ∈ Icc 0 T, 0 ≤ A s)
    (hCurves : ∀ᵐ a ∂μ,
      ControlledCurve G A Ω T (fun s => X s a) (fun s => V s a) (fun s => f s a))
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    ∀ᵐ a ∂μ, ‖X t a - Y t‖ ≤ Real.exp (rate T Lx Lv * T) *
      (‖X 0 a - Y 0‖ + T * ‖V 0 a - W 0‖ + T * ∫ s in 0..T, A s) :=
  (ae_position_error_bound μ hT hLx hLv hRef hG hA hAn hCurves).mono fun _ h => h t ht

variable [MeasurableSpace E] [BorelSpace E]

/-- Actual measurable position maps and finite initial errors give a finite error moment of every genuine pushforward probability measure and its exact averaged trajectory bound. -/
theorem mapped_position_moment_bound (μ : Measure Label) [IsProbabilityMeasure μ]
    (hT : 0 < T) (hLx : 0 ≤ Lx) (hLv : 0 ≤ Lv)
    (hRef : ReferenceCurve G Ω T Y W)
    (hG : ∀ s ∈ Icc 0 T, ∀ z ∈ Ω s, ∀ w ∈ Ω s,
      ‖G s z.1 z.2 - G s w.1 w.2‖ ≤ Lx * ‖z.1 - w.1‖ + Lv * ‖z.2 - w.2‖)
    (hA : IntervalIntegrable A volume 0 T) (hAn : ∀ s ∈ Icc 0 T, 0 ≤ A s)
    (hCurves : ∀ᵐ a ∂μ,
      ControlledCurve G A Ω T (fun s => X s a) (fun s => V s a) (fun s => f s a))
    (hX : ∀ t ∈ Icc 0 T, AEMeasurable (X t) μ)
    (ha : Integrable (fun a => ‖X 0 a - Y 0‖) μ)
    (hb : Integrable (fun a => ‖V 0 a - W 0‖) μ) :
    ∀ t ∈ Icc 0 T,
      Integrable (fun x => ‖x - Y t‖) (μ.map (X t)) ∧
        (∫ x, ‖x - Y t‖ ∂μ.map (X t)) ≤ Real.exp (rate T Lx Lv * T) *
          ((∫ a, ‖X 0 a - Y 0‖ ∂μ) + T * (∫ a, ‖V 0 a - W 0‖ ∂μ) +
            T * ∫ s in 0..T, A s) := by
  intro t ht
  exact ProbabilityTransportMoment.mapped_moment_bound (hX t ht) ha hb
    (ae_position_error_bound_at μ hT hLx hLv hRef hG hA hAn hCurves ht)

/-- The genuine transported probability measure has a finite first norm moment at every interval time, derived from the controlled dynamics and initial errors rather than assumed. -/
theorem transported_norm_integrable (μ : Measure Label) [IsProbabilityMeasure μ]
    (hT : 0 < T) (hLx : 0 ≤ Lx) (hLv : 0 ≤ Lv)
    (hRef : ReferenceCurve G Ω T Y W)
    (hG : ∀ s ∈ Icc 0 T, ∀ z ∈ Ω s, ∀ w ∈ Ω s,
      ‖G s z.1 z.2 - G s w.1 w.2‖ ≤ Lx * ‖z.1 - w.1‖ + Lv * ‖z.2 - w.2‖)
    (hA : IntervalIntegrable A volume 0 T) (hAn : ∀ s ∈ Icc 0 T, 0 ≤ A s)
    (hCurves : ∀ᵐ a ∂μ,
      ControlledCurve G A Ω T (fun s => X s a) (fun s => V s a) (fun s => f s a))
    (hX : ∀ t ∈ Icc 0 T, AEMeasurable (X t) μ)
    (ha : Integrable (fun a => ‖X 0 a - Y 0‖) μ)
    (hb : Integrable (fun a => ‖V 0 a - W 0‖) μ) :
    ∀ t ∈ Icc 0 T, Integrable (fun x : E => ‖x‖) (μ.map (X t)) := by
  intro t ht
  exact ProbabilityTransportMoment.norm_integrable_of_error
    (mapped_position_moment_bound μ hT hLx hLv hRef hG hA hAn hCurves hX ha hb t ht).1

end Labels
end FoliationQM.ProbabilityTrajectoryEstimate
