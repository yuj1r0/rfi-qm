module

public import FoliationQM.CurvedCurrentConcentration
public import FoliationQM.TransportTailBound
public import Mathlib.Analysis.Asymptotics.Defs

/-!
# Width rates and tail concentration for actual geometric current

The actual initial position, velocity, and integrated-force errors give an
explicit width coefficient for finite current transport costs and their
true time supremum. Markov bounds yield uniform statistical tails. Shrinking
radii retain the separate vanishing width-to-radius ratio hypothesis.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.CurvedCurrentWidthRate

open LorentzMatrixGroup CurvedCoordinateCurrent CurvedCoordinateDynamics
  CurvedEuclideanTrajectories CurvedCurrentTransport CurvedCurrentConcentration
  ProbabilityTrajectoryEstimate WeightedPhaseError WassersteinCoupling
  UniformTransportConcentration MeasureTheory Set Filter
open scoped ENNReal Topology Matrix.Norms.Operator

private theorem uniform_and_sup_of_nonneg_bound {ι : Type*}
    {q : ι → ℝ → ℝ} {B : ι → ℝ} {T : ℝ} (l : Filter ι) (hT : 0 ≤ T)
    (h : ∀ᶠ i in l, ∀ t ∈ Icc 0 T, 0 ≤ q i t ∧ q i t ≤ B i)
    (hB : Tendsto B l (𝓝 0)) :
    TendstoUniformlyOn q (fun _ => 0) l (Icc 0 T) ∧
      Tendsto (fun i => timeSup (q i) T) l (𝓝 0) := by
  have hu : TendstoUniformlyOn q (fun _ => 0) l (Icc 0 T) := by
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro ε hε
    filter_upwards [h, hB.eventually_lt_const hε] with i hi hBi t ht
    have hlt := ((hi t ht).2).trans_lt hBi
    simpa only [Real.dist_eq, zero_sub, abs_neg, abs_of_nonneg (hi t ht).1] using hlt
  refine ⟨hu, squeeze_zero' ?_ ?_ hB⟩
  · exact h.mono fun _ hi => timeSup_nonneg hT (fun t ht => (hi t ht).1)
      (fun t ht => (hi t ht).2)
  · exact h.mono fun _ hi => timeSup_le hT (fun t ht => (hi t ht).2)

variable {ι : Type*} {T Lx Lv Cx Cv CJ : ℝ}
  {Ω : ℝ → Set (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3))}
  {Y W : ℝ → EuclideanSpace ℝ (Fin 3)}
  (P : ι → MassiveParameters) (g : Covector → Mat4)
  (amp phase : ι → Covector → ℝ)
  (Phi : ι → ℝ × (Fin 3 → ℝ) → (Fin 3 → ℝ)) (domains : ι → Set (Fin 3 → ℝ))
  (H : ∀ i, FiniteFlowData (P i) g (amp i) (phase i) (Phi i) T (domains i)) (l : Filter ι)
  {c : ℝ} (hc : ∀ i, (P i).c = c) {F : ι → ℝ → ℝ} {width : ι → ℝ}
  (hT : 0 < T) (hLx : 0 ≤ Lx) (hLv : 0 ≤ Lv)
  (hRef : ReferenceCurve (geodesic c g) Ω T Y W)
  (hG : ∀ s ∈ Icc 0 T, ∀ z ∈ Ω s, ∀ w ∈ Ω s,
    ‖geodesic c g s z.1 z.2 - geodesic c g s w.1 w.2‖ ≤
      Lx * ‖z.1 - w.1‖ + Lv * ‖z.2 - w.2‖)
  (hCx : 0 ≤ Cx) (hCv : 0 ≤ Cv) (hCJ : 0 ≤ CJ)
  (hGood : ∀ᶠ i in l,
    SourceControl (H i) Ω (F i) (Y 0) (W 0) ∧ 0 ≤ width i ∧
    (∫ a, ‖WithLp.toLp 2 a - Y 0‖ ∂(initialProbability (H i) : Measure (Fin 3 → ℝ))) ≤
      Cx * width i ∧
    (∫ a, ‖WithLp.toLp 2 (spatialVelocity (P i) g (amp i) (phase i) (0, a)) - W 0‖
      ∂(initialProbability (H i) : Measure (Fin 3 → ℝ))) ≤ Cv * width i ∧
    (∫ s in 0..T, F i s) ≤ CJ * width i)

include hc hT hLx hLv hRef hG hCx hCv hCJ hGood

/-- Literal source moments bounded by width give finite actual current costs and the same explicit bound for their genuine time supremum. -/
theorem family_width_rate :
    let ν := fun i t => (currentProbability (H i) t : Measure (EuclideanSpace ℝ (Fin 3)))
    let K := Real.exp (rate T Lx Lv * T) * (Cx + T * Cv + T * CJ)
    0 ≤ K ∧ ∀ᶠ i in l,
      (∀ t ∈ Icc 0 T, eW1 (ν i t) (Measure.dirac (Y t)) ≠ ∞ ∧
        (eW1 (ν i t) (Measure.dirac (Y t))).toReal ≤ K * width i) ∧
      0 ≤ timeSup (fun t => (eW1 (ν i t) (Measure.dirac (Y t))).toReal) T ∧
      timeSup (fun t => (eW1 (ν i t) (Measure.dirac (Y t))).toReal) T ≤ K * width i := by
  dsimp only
  refine ⟨mul_nonneg (Real.exp_pos _).le
    (add_nonneg (add_nonneg hCx (mul_nonneg hT.le hCv)) (mul_nonneg hT.le hCJ)), ?_⟩
  filter_upwards [hGood] with i hi
  rcases hi with ⟨hctrl, _, hdx, hdb, hJ⟩
  have hb : ∀ t ∈ Icc 0 T,
      eW1 (currentProbability (H i) t : Measure _) (Measure.dirac (Y t)) ≠ ∞ ∧
      (eW1 (currentProbability (H i) t : Measure _) (Measure.dirac (Y t))).toReal ≤
        (Real.exp (rate T Lx Lv * T) * (Cx + T * Cv + T * CJ)) * width i := by
    intro t ht
    rw [currentProbability_eq_density (H i) ht]
    have hd := CurvedCurrentConcentration.finite_cost_and_bound (H i) hT hLx hLv
      (by simpa only [hc i] using hRef) (by simpa only [hc i] using hG) hctrl t ht
    refine ⟨hd.1, hd.2.trans ?_⟩
    calc
      _ ≤ Real.exp (rate T Lx Lv * T) *
          (Cx * width i + T * (Cv * width i) + T * (CJ * width i)) :=
        mul_le_mul_of_nonneg_left
          (add_le_add (add_le_add hdx (mul_le_mul_of_nonneg_left hdb hT.le))
            (mul_le_mul_of_nonneg_left hJ hT.le)) (Real.exp_pos _).le
      _ = _ := by ring
  exact ⟨hb, (finite_cost_sup_bound hT.le hb).2⟩

/-- The actual current distance moment is genuinely integrable and obeys the explicit width bound at every interval time. -/
theorem family_first_moment_width_rate :
    let ν := fun i t => (currentProbability (H i) t : Measure (EuclideanSpace ℝ (Fin 3)))
    let K := Real.exp (rate T Lx Lv * T) * (Cx + T * Cv + T * CJ)
    ∀ᶠ i in l, ∀ t ∈ Icc 0 T,
      Integrable (fun x => dist x (Y t)) (ν i t) ∧
        (∫ x, dist x (Y t) ∂ν i t) ≤ K * width i := by
  dsimp only
  filter_upwards [(family_width_rate P g amp phase Phi domains H l hc hT hLx hLv
    hRef hG hCx hCv hCJ hGood).2] with i hi t ht
  have hm : WassersteinFiniteMoment.moment
      (currentProbability (H i) t : Measure _) (Y t) < ∞ := by
    rw [WassersteinFiniteMoment.moment, ← WassersteinDirac.eW1_dirac]
    exact lt_top_iff_ne_top.mpr (hi.1 t ht).1
  have hd := (WassersteinFiniteMoment.moment_lt_top_iff_integrable_dist
    (currentProbability (H i) t : Measure _) (Y t)).mp hm
  refine ⟨hd, ?_⟩
  rw [← WassersteinDirac.eW1_dirac_toReal hd]
  exact (hi.1 t ht).2

/-- The actual current transport supremum is bounded in asymptotic order by the supplied width. -/
theorem width_rate_isBigO :
    (fun i => timeSup (fun t =>
      (eW1 (currentProbability (H i) t : Measure (EuclideanSpace ℝ (Fin 3)))
        (Measure.dirac (Y t))).toReal) T) =O[l] width := by
  apply Asymptotics.IsBigO.of_bound (Real.exp (rate T Lx Lv * T) * (Cx + T * Cv + T * CJ))
  filter_upwards [(family_width_rate P g amp phase Phi domains H l hc hT hLx hLv
    hRef hG hCx hCv hCJ hGood).2, hGood] with i hi hsource
  simpa only [Real.norm_eq_abs, abs_of_nonneg hi.2.1, abs_of_nonneg hsource.2.1] using hi.2.2

/-- Vanishing width gives genuine finite current transport concentration uniformly in time and convergence of its actual supremum. -/
theorem family_concentration_of_width_tendsto (hwidth : Tendsto width l (𝓝 0)) :
    let ν := fun i t => (currentProbability (H i) t : Measure (EuclideanSpace ℝ (Fin 3)))
    (∀ᶠ i in l, ∀ t ∈ Icc 0 T, eW1 (ν i t) (Measure.dirac (Y t)) ≠ ∞) ∧
      TendstoUniformlyOn (fun i t => (eW1 (ν i t) (Measure.dirac (Y t))).toReal)
        (fun _ => 0) l (Icc 0 T) ∧
      Tendsto (fun i => timeSup (fun t => (eW1 (ν i t) (Measure.dirac (Y t))).toReal) T)
        l (𝓝 0) := by
  dsimp only
  apply uniform_concentration_of_bound l hT.le
    ((family_width_rate P g amp phase Phi domains H l hc hT hLx hLv
      hRef hG hCx hCv hCJ hGood).2.mono fun _ hi => hi.1)
  simpa only [mul_zero] using hwidth.const_mul
    (Real.exp (rate T Lx Lv * T) * (Cx + T * Cv + T * CJ))

/-- Each fixed positive radius has the exact Markov width bound, also for the actual tail-probability time supremum. -/
theorem family_tail_bound {r : ℝ} (hr : 0 < r) :
    let ν := fun i t => (currentProbability (H i) t : Measure (EuclideanSpace ℝ (Fin 3)))
    let K := Real.exp (rate T Lx Lv * T) * (Cx + T * Cv + T * CJ)
    ∀ᶠ i in l,
      (∀ t ∈ Icc 0 T, (ν i t).real {x | r < dist x (Y t)} ≤ K * width i / r) ∧
      0 ≤ timeSup (fun t => (ν i t).real {x | r < dist x (Y t)}) T ∧
      timeSup (fun t => (ν i t).real {x | r < dist x (Y t)}) T ≤ K * width i / r := by
  dsimp only
  filter_upwards [(family_width_rate P g amp phase Phi domains H l hc hT hLx hLv
    hRef hG hCx hCv hCJ hGood).2] with i hi
  have hb : ∀ t ∈ Icc 0 T,
      (currentProbability (H i) t : Measure _).real {x | r < dist x (Y t)} ≤
        (Real.exp (rate T Lx Lv * T) * (Cx + T * Cv + T * CJ)) * width i / r := by
    intro t ht
    exact (TransportTailBound.tail_real_le_cost hr (hi.1 t ht).1).trans
      (div_le_div_of_nonneg_right (hi.1 t ht).2 hr.le)
  exact ⟨hb, timeSup_nonneg hT.le (fun _ _ => measureReal_nonneg) hb, timeSup_le hT.le hb⟩

/-- At every fixed positive radius the actual tail-probability time supremum has order at most the width. -/
theorem tail_rate_isBigO {r : ℝ} (hr : 0 < r) :
    (fun i => timeSup (fun t =>
      (currentProbability (H i) t : Measure (EuclideanSpace ℝ (Fin 3))).real
        {x | r < dist x (Y t)}) T) =O[l] width := by
  apply Asymptotics.IsBigO.of_bound
    ((Real.exp (rate T Lx Lv * T) * (Cx + T * Cv + T * CJ)) / r)
  filter_upwards [family_tail_bound P g amp phase Phi domains H l hc hT hLx hLv
    hRef hG hCx hCv hCJ hGood hr, hGood] with i hi hsource
  rw [Real.norm_eq_abs, abs_of_nonneg hi.2.1, Real.norm_eq_abs, abs_of_nonneg hsource.2.1]
  exact hi.2.2.trans_eq (by ring)

/-- Vanishing width makes actual fixed-radius current tails vanish uniformly, together with their actual time supremum. -/
theorem family_tail_concentration_of_width_tendsto {r : ℝ} (hr : 0 < r)
    (hwidth : Tendsto width l (𝓝 0)) :
    let ν := fun i t => (currentProbability (H i) t : Measure (EuclideanSpace ℝ (Fin 3)))
    TendstoUniformlyOn (fun i t => (ν i t).real {x | r < dist x (Y t)})
      (fun _ => 0) l (Icc 0 T) ∧
      Tendsto (fun i => timeSup (fun t => (ν i t).real {x | r < dist x (Y t)}) T)
        l (𝓝 0) := by
  dsimp only
  apply uniform_and_sup_of_nonneg_bound l hT.le
    ((family_tail_bound P g amp phase Phi domains H l hc hT hLx hLv
      hRef hG hCx hCv hCJ hGood hr).mono fun _ hi t ht => ⟨measureReal_nonneg, hi.1 t ht⟩)
  simpa only [mul_zero, zero_div] using
    (hwidth.const_mul (Real.exp (rate T Lx Lv * T) * (Cx + T * Cv + T * CJ))).div_const r

/-- Shrinking-radius statistical concentration requires the actual width-to-radius ratio to tend to zero. -/
theorem family_shrinking_tail_concentration {radius : ι → ℝ}
    (hr : ∀ᶠ i in l, 0 < radius i)
    (hratio : Tendsto (fun i => width i / radius i) l (𝓝 0)) :
    let ν := fun i t => (currentProbability (H i) t : Measure (EuclideanSpace ℝ (Fin 3)))
    TendstoUniformlyOn (fun i t => (ν i t).real {x | radius i < dist x (Y t)})
      (fun _ => 0) l (Icc 0 T) ∧
      Tendsto (fun i => timeSup (fun t => (ν i t).real {x | radius i < dist x (Y t)}) T)
        l (𝓝 0) := by
  dsimp only
  apply uniform_and_sup_of_nonneg_bound (B := fun i =>
    (Real.exp (rate T Lx Lv * T) * (Cx + T * Cv + T * CJ)) * (width i / radius i)) l hT.le
  · filter_upwards [(family_width_rate P g amp phase Phi domains H l hc hT hLx hLv
      hRef hG hCx hCv hCJ hGood).2, hr] with i hi hri t ht
    refine ⟨measureReal_nonneg, ?_⟩
    have hb := (TransportTailBound.tail_real_le_cost hri (hi.1 t ht).1).trans
      (div_le_div_of_nonneg_right (hi.1 t ht).2 hri.le)
    exact hb.trans_eq (by ring)
  · simpa only [mul_zero] using hratio.const_mul
      (Real.exp (rate T Lx Lv * T) * (Cx + T * Cv + T * CJ))

end FoliationQM.CurvedCurrentWidthRate
