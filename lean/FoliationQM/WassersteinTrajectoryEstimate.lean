module

public import FoliationQM.ProbabilityTrajectoryEstimate
public import FoliationQM.WassersteinDirac
public import FoliationQM.UniformTransportConcentration

/-!
# Genuine transport concentration from controlled trajectories

The actual trajectory equations, common full-measure label event, measurable
position maps and integrable initial errors yield finite transport cost to
the reference position. Its real value is identified with the proved error
moment before estimating it. The same estimate controls the actual time
supremum and gives uniform convergence along an explicit filter when the
three actual initial and integrated-force errors vanish.

For families, the analytic hypotheses need hold only eventually. Each good
index has one common full-measure set of labels valid throughout the time
interval. No exchange of label and time exceptional sets is required.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.WassersteinTrajectoryEstimate

open MeasureTheory Set Filter WeightedPhaseError ProbabilityTrajectoryEstimate
  WassersteinCoupling UniformTransportConcentration
open scoped Topology ENNReal

variable {E Label : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [MeasurableSpace Label]
  {G : ℝ → E → E → E} {Ω : ℝ → Set (E × E)} {Y W : ℝ → E}
  {T Lx Lv : ℝ}

section Single

variable {X V f : ℝ → Label → E} {A : ℝ → ℝ}

/-- Actual controlled trajectories give finite genuine transport cost at every interval time and the exact averaged trajectory bound for its real value. -/
theorem finite_cost_and_bound (μ : Measure Label) [IsProbabilityMeasure μ]
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
      eW1 (μ.map (X t)) (Measure.dirac (Y t)) ≠ ∞ ∧
        (eW1 (μ.map (X t)) (Measure.dirac (Y t))).toReal ≤
          Real.exp (rate T Lx Lv * T) *
            ((∫ a, ‖X 0 a - Y 0‖ ∂μ) + T * (∫ a, ‖V 0 a - W 0‖ ∂μ) +
              T * ∫ s in 0..T, A s) := by
  intro t ht
  have hm := mapped_position_moment_bound μ hT hLx hLv hRef hG hA hAn
    hCurves hX ha hb t ht
  have hd := WassersteinDirac.eW1_dirac_finite_and_toReal_norm hm.1
  exact ⟨hd.1, hd.2.trans_le hm.2⟩

/-- The actual supremum over the nonempty closed time interval obeys the same trajectory estimate, with genuine transport finiteness retained at every time. -/
theorem sup_bound (μ : Measure Label) [IsProbabilityMeasure μ]
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
    (∀ t ∈ Icc 0 T, eW1 (μ.map (X t)) (Measure.dirac (Y t)) ≠ ∞) ∧
      0 ≤ timeSup (fun t => (eW1 (μ.map (X t)) (Measure.dirac (Y t))).toReal) T ∧
      timeSup (fun t => (eW1 (μ.map (X t)) (Measure.dirac (Y t))).toReal) T ≤
        Real.exp (rate T Lx Lv * T) *
          ((∫ a, ‖X 0 a - Y 0‖ ∂μ) + T * (∫ a, ‖V 0 a - W 0‖ ∂μ) +
            T * ∫ s in 0..T, A s) :=
  finite_cost_sup_bound hT.le
    (finite_cost_and_bound μ hT hLx hLv hRef hG hA hAn hCurves hX ha hb)

end Single

section Family

variable {ι : Type*} {X V f : ι → ℝ → Label → E} {A : ι → ℝ → ℝ}

/-- Eventual actual dynamical inputs and vanishing actual initial-position, initial-velocity and integrated-force errors give uniform finite transport concentration and convergence of the actual time supremum along the supplied filter. -/
theorem family_concentration_of_eventually (μ : ι → Measure Label)
    [∀ i, IsProbabilityMeasure (μ i)] (l : Filter ι)
    (hT : 0 < T) (hLx : 0 ≤ Lx) (hLv : 0 ≤ Lv)
    (hRef : ReferenceCurve G Ω T Y W)
    (hG : ∀ s ∈ Icc 0 T, ∀ z ∈ Ω s, ∀ w ∈ Ω s,
      ‖G s z.1 z.2 - G s w.1 w.2‖ ≤ Lx * ‖z.1 - w.1‖ + Lv * ‖z.2 - w.2‖)
    (hGood : ∀ᶠ i in l,
      IntervalIntegrable (A i) volume 0 T ∧
      (∀ s ∈ Icc 0 T, 0 ≤ A i s) ∧
      (∀ᵐ a ∂μ i, ControlledCurve G (A i) Ω T
        (fun s => X i s a) (fun s => V i s a) (fun s => f i s a)) ∧
      (∀ t ∈ Icc 0 T, AEMeasurable (X i t) (μ i)) ∧
      Integrable (fun a => ‖X i 0 a - Y 0‖) (μ i) ∧
      Integrable (fun a => ‖V i 0 a - W 0‖) (μ i))
    (hdx : Tendsto (fun i => ∫ a, ‖X i 0 a - Y 0‖ ∂μ i) l (𝓝 0))
    (hdb : Tendsto (fun i => ∫ a, ‖V i 0 a - W 0‖ ∂μ i) l (𝓝 0))
    (hJ : Tendsto (fun i => ∫ s in 0..T, A i s) l (𝓝 0)) :
    (∀ᶠ i in l, ∀ t ∈ Icc 0 T,
      eW1 ((μ i).map (X i t)) (Measure.dirac (Y t)) ≠ ∞) ∧
      TendstoUniformlyOn
        (fun i t => (eW1 ((μ i).map (X i t)) (Measure.dirac (Y t))).toReal)
        (fun _ => 0) l (Icc 0 T) ∧
      Tendsto (fun i => timeSup
        (fun t => (eW1 ((μ i).map (X i t)) (Measure.dirac (Y t))).toReal) T)
        l (𝓝 0) := by
  apply uniform_concentration_of_bound l hT.le
    (B := fun i => Real.exp (rate T Lx Lv * T) *
      ((∫ a, ‖X i 0 a - Y 0‖ ∂μ i) + T * (∫ a, ‖V i 0 a - W 0‖ ∂μ i) +
        T * ∫ s in 0..T, A i s))
  · filter_upwards [hGood] with i hi
    rcases hi with ⟨hA, hAn, hCurves, hX, ha, hb⟩
    exact finite_cost_and_bound (μ i) hT hLx hLv hRef hG hA hAn hCurves hX ha hb
  · exact source_majorant_tendsto l T Lx Lv hdx hdb hJ

end Family
end FoliationQM.WassersteinTrajectoryEstimate
