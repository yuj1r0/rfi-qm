module

public import FoliationQM.ProbabilityTrajectoryEstimate

/-!
# Controlled trajectories averaged over a finite label measure

Source: v13 `rem:wkb_rates_tails` and `eq:wasserstein_concentration_bound`, kinds C/D.

Actual dynamics give integrable transported errors before averaging. The
constant forcing contribution retains the total label mass, including when
that mass is zero. Restricting a probability to good labels therefore does
not require renormalization or any moment on the discarded labels.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.RestrictedTrajectoryMoment

open ProbabilityTrajectoryEstimate WeightedPhaseError MeasureTheory Set

variable {Label E : Type*} [MeasurableSpace Label]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E]
  {G : ℝ → E → E → E} {F : ℝ → ℝ} {Ω : ℝ → Set (E × E)}
  {T Lx Lv : ℝ} {X V f : ℝ → Label → E} {Y W : ℝ → E}

/-- Genuine finite-measure initial moments and controlled dynamics imply the exact error bound, with the total-mass forcing factor. -/
theorem finite_measure_position_moment_bound (ν : Measure Label) [IsFiniteMeasure ν]
    (hT : 0 < T) (hLx : 0 ≤ Lx) (hLv : 0 ≤ Lv)
    (hRef : ReferenceCurve G Ω T Y W)
    (hG : ∀ s ∈ Icc 0 T, ∀ z ∈ Ω s, ∀ w ∈ Ω s,
      ‖G s z.1 z.2 - G s w.1 w.2‖ ≤ Lx * ‖z.1 - w.1‖ + Lv * ‖z.2 - w.2‖)
    (hF : IntervalIntegrable F volume 0 T) (hFn : ∀ s ∈ Icc 0 T, 0 ≤ F s)
    (hCurves : ∀ᵐ a ∂ν,
      ControlledCurve G F Ω T (fun s => X s a) (fun s => V s a) (fun s => f s a))
    (hX : ∀ t ∈ Icc 0 T, AEMeasurable (X t) ν)
    (hx : Integrable (fun a => ‖X 0 a - Y 0‖) ν)
    (hv : Integrable (fun a => ‖V 0 a - W 0‖) ν) :
    ∀ t ∈ Icc 0 T, Integrable (fun a => ‖X t a - Y t‖) ν ∧
      (∫ a, ‖X t a - Y t‖ ∂ν) ≤ Real.exp (rate T Lx Lv * T) *
        ((∫ a, ‖X 0 a - Y 0‖ ∂ν) + T * (∫ a, ‖V 0 a - W 0‖ ∂ν) +
          ν.real univ * (T * ∫ s in 0..T, F s)) := by
  intro t ht
  have hb := ae_position_error_bound_at ν hT hLx hLv hRef hG hF hFn hCurves ht
  exact ⟨ProbabilityTransportMoment.integrable_error_of_bound (hX t ht) hx hv hb,
    ProbabilityTransportMoment.averaged_error_bound (hX t ht) hx hv hb⟩

/-- The same genuine finite-measure estimate transfers to the actual measurable pushforward. -/
theorem mapped_finite_measure_position_moment_bound (ν : Measure Label) [IsFiniteMeasure ν]
    (hT : 0 < T) (hLx : 0 ≤ Lx) (hLv : 0 ≤ Lv)
    (hRef : ReferenceCurve G Ω T Y W)
    (hG : ∀ s ∈ Icc 0 T, ∀ z ∈ Ω s, ∀ w ∈ Ω s,
      ‖G s z.1 z.2 - G s w.1 w.2‖ ≤ Lx * ‖z.1 - w.1‖ + Lv * ‖z.2 - w.2‖)
    (hF : IntervalIntegrable F volume 0 T) (hFn : ∀ s ∈ Icc 0 T, 0 ≤ F s)
    (hCurves : ∀ᵐ a ∂ν,
      ControlledCurve G F Ω T (fun s => X s a) (fun s => V s a) (fun s => f s a))
    (hX : ∀ t ∈ Icc 0 T, AEMeasurable (X t) ν)
    (hx : Integrable (fun a => ‖X 0 a - Y 0‖) ν)
    (hv : Integrable (fun a => ‖V 0 a - W 0‖) ν) :
    ∀ t ∈ Icc 0 T, Integrable (fun x => ‖x - Y t‖) (ν.map (X t)) ∧
      (∫ x, ‖x - Y t‖ ∂ν.map (X t)) ≤ Real.exp (rate T Lx Lv * T) *
        ((∫ a, ‖X 0 a - Y 0‖ ∂ν) + T * (∫ a, ‖V 0 a - W 0‖ ∂ν) +
          ν.real univ * (T * ∫ s in 0..T, F s)) := by
  intro t ht
  have hb := finite_measure_position_moment_bound ν hT hLx hLv hRef hG hF hFn
    hCurves hX hx hv t ht
  refine ⟨ProbabilityTransportMoment.mapped_error_integrable (hX t ht) hb.1, ?_⟩
  rw [ProbabilityTransportMoment.mapped_error_integral (hX t ht)]
  exact hb.2

end FoliationQM.RestrictedTrajectoryMoment
