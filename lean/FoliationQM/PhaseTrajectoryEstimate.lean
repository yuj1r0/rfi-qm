module

public import FoliationQM.WeightedPhaseError
public import FoliationQM.IntegralTrajectoryBound
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Actual weighted phase paths for forced and unforced trajectories

The phase path is a fixed continuous linear image of the actual position
and velocity differences. Its derivative follows from the four coordinate
ODEs. Direct control of the acceleration field at the two endpoints gives
the weighted derivative estimate without introducing an intermediate
phase point. Almost-everywhere force control remains almost everywhere.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.PhaseTrajectoryEstimate

open WeightedPhaseError Set MeasureTheory
open scoped Topology
set_option backward.isDefEq.respectTransparency false

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The actual weighted phase difference of two position-velocity trajectories. -/
def phasePath (T : ℝ) (X Y V W : ℝ → E) (t : ℝ) : WithLp 1 (E × E) :=
  phaseMap T (X t - Y t, V t - W t)

/-- The phase derivative computed from the forced and unforced coordinate ODE right-hand sides. -/
def phaseDerivative (T : ℝ) (G : ℝ → E → E → E) (f X Y V W : ℝ → E)
    (t : ℝ) : WithLp 1 (E × E) :=
  phaseMap T (V t - W t, G t (X t) (V t) + f t - G t (Y t) (W t))

variable {G : ℝ → E → E → E} {f X Y V W : ℝ → E} {T Lx Lv : ℝ} {A : ℝ → ℝ}

/-- The four actual coordinate ODE derivatives imply the genuine derivative of the weighted phase path. -/
theorem hasDerivAt_phasePath (T : ℝ) {t : ℝ}
    (hX : HasDerivAt X (V t) t) (hY : HasDerivAt Y (W t) t)
    (hV : HasDerivAt V (G t (X t) (V t) + f t) t)
    (hW : HasDerivAt W (G t (Y t) (W t)) t) :
    HasDerivAt (phasePath T X Y V W) (phaseDerivative T G f X Y V W t) t := by
  simpa only [phasePath, phaseDerivative, Function.comp_def, Pi.sub_apply] using!
    (phaseMap (E := E) T).hasFDerivAt.comp_hasDerivAt t ((hX.sub hY).prodMk (hV.sub hW))

/-- Continuity of the actual positions and velocities gives continuity of their weighted phase path. -/
theorem continuousOn_phasePath (T : ℝ) {I : Set ℝ}
    (hX : ContinuousOn X I) (hY : ContinuousOn Y I)
    (hV : ContinuousOn V I) (hW : ContinuousOn W I) :
    ContinuousOn (phasePath T X Y V W) I :=
  (phaseMap T).continuous.comp_continuousOn ((hX.sub hY).prodMk (hV.sub hW))

/-- The phase-path norm is exactly the weighted source position and velocity error. -/
theorem norm_phasePath (hT : 0 ≤ T) (t : ℝ) :
    ‖phasePath T X Y V W t‖ = ‖X t - Y t‖ + T * ‖V t - W t‖ :=
  phaseMap_norm hT _ _

/-- A direct endpoint acceleration-field bound yields the actual phase derivative estimate with the exact forcing coefficient. -/
theorem norm_phaseDerivative_le (hT : 0 < T) {t : ℝ}
    (hG : ‖G t (X t) (V t) - G t (Y t) (W t)‖ ≤
      Lx * ‖X t - Y t‖ + Lv * ‖V t - W t‖) (hf : ‖f t‖ ≤ A t) :
    ‖phaseDerivative T G f X Y V W t‖ ≤
      rate T Lx Lv * ‖phasePath T X Y V W t‖ + T * A t := by
  apply weighted_error_le_source hT
  have he : G t (X t) (V t) + f t - G t (Y t) (W t) =
      (G t (X t) (V t) - G t (Y t) (W t)) + f t := by abel
  rw [he]
  exact (norm_add_le _ _).trans (add_le_add hG hf)

/-- Almost-everywhere force control gives the actual phase derivative bound with the same almost-everywhere qualification. -/
theorem ae_norm_phaseDerivative_le (hT : 0 < T)
    (hG : ∀ t ∈ Icc 0 T, ‖G t (X t) (V t) - G t (Y t) (W t)‖ ≤
      Lx * ‖X t - Y t‖ + Lv * ‖V t - W t‖)
    (hf : ∀ᵐ t ∂volume.restrict (Icc 0 T), ‖f t‖ ≤ A t) :
    ∀ᵐ t ∂volume.restrict (Icc 0 T), ‖phaseDerivative T G f X Y V W t‖ ≤
      rate T Lx Lv * ‖phasePath T X Y V W t‖ + T * A t := by
  filter_upwards [ae_restrict_mem measurableSet_Icc, hf] with t ht hft
  exact norm_phaseDerivative_le hT (hG t ht) hft

/-- Continuity of the actual along-curve field and force values gives continuity of the computed phase derivative. -/
theorem continuousOn_phaseDerivative (T : ℝ) {I : Set ℝ}
    (hV : ContinuousOn V I) (hW : ContinuousOn W I)
    (hGX : ContinuousOn (fun t => G t (X t) (V t)) I)
    (hGY : ContinuousOn (fun t => G t (Y t) (W t)) I) (hf : ContinuousOn f I) :
    ContinuousOn (phaseDerivative T G f X Y V W) I :=
  (phaseMap T).continuous.comp_continuousOn
    ((hV.sub hW).prodMk ((hGX.add hf).sub hGY))

/-- Integrability of the actual velocity, acceleration-field and force components gives integrability of the genuine phase derivative. -/
theorem intervalIntegrable_phaseDerivative (T : ℝ)
    (hV : IntervalIntegrable V volume 0 T) (hW : IntervalIntegrable W volume 0 T)
    (hGX : IntervalIntegrable (fun t => G t (X t) (V t)) volume 0 T)
    (hGY : IntervalIntegrable (fun t => G t (Y t) (W t)) volume 0 T)
    (hf : IntervalIntegrable f volume 0 T) :
    IntervalIntegrable (phaseDerivative T G f X Y V W) volume 0 T := by
  constructor
  · exact (phaseMap (E := E) T).integrable_comp
      ((hV.1.sub hW.1).prodMk ((hGX.1.add hf.1).sub hGY.1))
  · exact (phaseMap (E := E) T).integrable_comp
      ((hV.2.sub hW.2).prodMk ((hGX.2.add hf.2).sub hGY.2))

/-- Continuous along-curve data automatically provide the integrability needed for the actual phase derivative. -/
theorem intervalIntegrable_phaseDerivative_of_continuous (hT : 0 ≤ T)
    (hV : ContinuousOn V (Icc 0 T)) (hW : ContinuousOn W (Icc 0 T))
    (hGX : ContinuousOn (fun t => G t (X t) (V t)) (Icc 0 T))
    (hGY : ContinuousOn (fun t => G t (Y t) (W t)) (Icc 0 T))
    (hf : ContinuousOn f (Icc 0 T)) :
    IntervalIntegrable (phaseDerivative T G f X Y V W) volume 0 T :=
  (continuousOn_phaseDerivative T hV hW hGX hGY hf).intervalIntegrable_of_Icc hT

omit [NormedSpace ℝ E] in
/-- A common phase region containing both trajectories supplies the direct endpoint estimate without any mixed-state assumption. -/
theorem endpoint_bound_of_no_exit {Ω : ℝ → Set (E × E)}
    (hX : ∀ t ∈ Icc 0 T, (X t, V t) ∈ Ω t)
    (hY : ∀ t ∈ Icc 0 T, (Y t, W t) ∈ Ω t)
    (hG : ∀ t ∈ Icc 0 T, ∀ z ∈ Ω t, ∀ w ∈ Ω t,
      ‖G t z.1 z.2 - G t w.1 w.2‖ ≤ Lx * ‖z.1 - w.1‖ + Lv * ‖z.2 - w.2‖) :
    ∀ t ∈ Icc 0 T, ‖G t (X t) (V t) - G t (Y t) (W t)‖ ≤
      Lx * ‖X t - Y t‖ + Lv * ‖V t - W t‖ :=
  fun t ht => hG t ht (X t, V t) (hX t ht) (Y t, W t) (hY t ht)

variable [CompleteSpace E]

/-- Actual coordinate trajectories with integrable phase derivative obey the exact weighted Grönwall estimate under direct endpoint field control and almost-everywhere forcing. -/
theorem phase_error_bound (hT : 0 < T) (hLx : 0 ≤ Lx) (hLv : 0 ≤ Lv)
    (hXc : ContinuousOn X (Icc 0 T)) (hYc : ContinuousOn Y (Icc 0 T))
    (hVc : ContinuousOn V (Icc 0 T)) (hWc : ContinuousOn W (Icc 0 T))
    (hX' : ∀ s ∈ Ioo 0 T, HasDerivAt X (V s) s)
    (hY' : ∀ s ∈ Ioo 0 T, HasDerivAt Y (W s) s)
    (hV' : ∀ s ∈ Ioo 0 T, HasDerivAt V (G s (X s) (V s) + f s) s)
    (hW' : ∀ s ∈ Ioo 0 T, HasDerivAt W (G s (Y s) (W s)) s)
    (hi : IntervalIntegrable (phaseDerivative T G f X Y V W) volume 0 T)
    (hG : ∀ s ∈ Icc 0 T, ‖G s (X s) (V s) - G s (Y s) (W s)‖ ≤
      Lx * ‖X s - Y s‖ + Lv * ‖V s - W s‖)
    (hf : ∀ᵐ s ∂volume.restrict (Icc 0 T), ‖f s‖ ≤ A s)
    (hA : IntervalIntegrable A volume 0 T) (hAn : ∀ s ∈ Icc 0 T, 0 ≤ A s) :
    ∀ t ∈ Icc 0 T, ‖X t - Y t‖ + T * ‖V t - W t‖ ≤
      Real.exp (rate T Lx Lv * T) *
        (‖X 0 - Y 0‖ + T * ‖V 0 - W 0‖ + T * ∫ s in 0..T, A s) := by
  have H := IntegralTrajectoryBound.trajectory_bound hT.le (coefficient_nonneg hT hLx hLv)
    (continuousOn_phasePath T hXc hYc hVc hWc)
    (fun s hs => hasDerivAt_phasePath T (hX' s hs) (hY' s hs) (hV' s hs) (hW' s hs))
    hi (hA.const_mul T) (fun s hs => mul_nonneg hT.le (hAn s hs))
    (ae_norm_phaseDerivative_le hT hG hf)
  intro t ht
  simpa only [norm_phasePath hT.le, intervalIntegral.integral_const_mul] using H t ht

/-- The actual position error alone is controlled by the same explicit weighted trajectory bound. -/
theorem position_error_bound (hT : 0 < T) (hLx : 0 ≤ Lx) (hLv : 0 ≤ Lv)
    (hXc : ContinuousOn X (Icc 0 T)) (hYc : ContinuousOn Y (Icc 0 T))
    (hVc : ContinuousOn V (Icc 0 T)) (hWc : ContinuousOn W (Icc 0 T))
    (hX' : ∀ s ∈ Ioo 0 T, HasDerivAt X (V s) s)
    (hY' : ∀ s ∈ Ioo 0 T, HasDerivAt Y (W s) s)
    (hV' : ∀ s ∈ Ioo 0 T, HasDerivAt V (G s (X s) (V s) + f s) s)
    (hW' : ∀ s ∈ Ioo 0 T, HasDerivAt W (G s (Y s) (W s)) s)
    (hi : IntervalIntegrable (phaseDerivative T G f X Y V W) volume 0 T)
    (hG : ∀ s ∈ Icc 0 T, ‖G s (X s) (V s) - G s (Y s) (W s)‖ ≤
      Lx * ‖X s - Y s‖ + Lv * ‖V s - W s‖)
    (hf : ∀ᵐ s ∂volume.restrict (Icc 0 T), ‖f s‖ ≤ A s)
    (hA : IntervalIntegrable A volume 0 T) (hAn : ∀ s ∈ Icc 0 T, 0 ≤ A s) :
    ∀ t ∈ Icc 0 T, ‖X t - Y t‖ ≤ Real.exp (rate T Lx Lv * T) *
      (‖X 0 - Y 0‖ + T * ‖V 0 - W 0‖ + T * ∫ s in 0..T, A s) := by
  intro t ht
  have H := phase_error_bound hT hLx hLv hXc hYc hVc hWc hX' hY' hV' hW'
    hi hG hf hA hAn t ht
  have hp := mul_nonneg hT.le (norm_nonneg (V t - W t))
  linarith

/-- Continuous actual along-curve field and force values supply the phase-derivative integrability in the weighted trajectory estimate. -/
theorem phase_error_bound_of_continuous (hT : 0 < T) (hLx : 0 ≤ Lx) (hLv : 0 ≤ Lv)
    (hXc : ContinuousOn X (Icc 0 T)) (hYc : ContinuousOn Y (Icc 0 T))
    (hVc : ContinuousOn V (Icc 0 T)) (hWc : ContinuousOn W (Icc 0 T))
    (hX' : ∀ s ∈ Ioo 0 T, HasDerivAt X (V s) s)
    (hY' : ∀ s ∈ Ioo 0 T, HasDerivAt Y (W s) s)
    (hV' : ∀ s ∈ Ioo 0 T, HasDerivAt V (G s (X s) (V s) + f s) s)
    (hW' : ∀ s ∈ Ioo 0 T, HasDerivAt W (G s (Y s) (W s)) s)
    (hGX : ContinuousOn (fun s => G s (X s) (V s)) (Icc 0 T))
    (hGY : ContinuousOn (fun s => G s (Y s) (W s)) (Icc 0 T))
    (hfc : ContinuousOn f (Icc 0 T))
    (hG : ∀ s ∈ Icc 0 T, ‖G s (X s) (V s) - G s (Y s) (W s)‖ ≤
      Lx * ‖X s - Y s‖ + Lv * ‖V s - W s‖)
    (hf : ∀ᵐ s ∂volume.restrict (Icc 0 T), ‖f s‖ ≤ A s)
    (hA : IntervalIntegrable A volume 0 T) (hAn : ∀ s ∈ Icc 0 T, 0 ≤ A s) :
    ∀ t ∈ Icc 0 T, ‖X t - Y t‖ + T * ‖V t - W t‖ ≤
      Real.exp (rate T Lx Lv * T) *
        (‖X 0 - Y 0‖ + T * ‖V 0 - W 0‖ + T * ∫ s in 0..T, A s) :=
  phase_error_bound hT hLx hLv hXc hYc hVc hWc hX' hY' hV' hW'
    (intervalIntegrable_phaseDerivative_of_continuous hT.le hVc hWc hGX hGY hfc) hG hf hA hAn

/-- A common no-exit phase region with direct anisotropic field control yields the actual weighted trajectory estimate. -/
theorem phase_error_bound_on {Ω : ℝ → Set (E × E)}
    (hT : 0 < T) (hLx : 0 ≤ Lx) (hLv : 0 ≤ Lv)
    (hXc : ContinuousOn X (Icc 0 T)) (hYc : ContinuousOn Y (Icc 0 T))
    (hVc : ContinuousOn V (Icc 0 T)) (hWc : ContinuousOn W (Icc 0 T))
    (hX' : ∀ s ∈ Ioo 0 T, HasDerivAt X (V s) s)
    (hY' : ∀ s ∈ Ioo 0 T, HasDerivAt Y (W s) s)
    (hV' : ∀ s ∈ Ioo 0 T, HasDerivAt V (G s (X s) (V s) + f s) s)
    (hW' : ∀ s ∈ Ioo 0 T, HasDerivAt W (G s (Y s) (W s)) s)
    (hi : IntervalIntegrable (phaseDerivative T G f X Y V W) volume 0 T)
    (hXm : ∀ s ∈ Icc 0 T, (X s, V s) ∈ Ω s)
    (hYm : ∀ s ∈ Icc 0 T, (Y s, W s) ∈ Ω s)
    (hG : ∀ s ∈ Icc 0 T, ∀ z ∈ Ω s, ∀ w ∈ Ω s,
      ‖G s z.1 z.2 - G s w.1 w.2‖ ≤ Lx * ‖z.1 - w.1‖ + Lv * ‖z.2 - w.2‖)
    (hf : ∀ᵐ s ∂volume.restrict (Icc 0 T), ‖f s‖ ≤ A s)
    (hA : IntervalIntegrable A volume 0 T) (hAn : ∀ s ∈ Icc 0 T, 0 ≤ A s) :
    ∀ t ∈ Icc 0 T, ‖X t - Y t‖ + T * ‖V t - W t‖ ≤
      Real.exp (rate T Lx Lv * T) *
        (‖X 0 - Y 0‖ + T * ‖V 0 - W 0‖ + T * ∫ s in 0..T, A s) :=
  phase_error_bound hT hLx hLv hXc hYc hVc hWc hX' hY' hV' hW'
    hi (endpoint_bound_of_no_exit hXm hYm hG) hf hA hAn

end FoliationQM.PhaseTrajectoryEstimate
