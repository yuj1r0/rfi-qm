module

public import FoliationQM.RestrictedTrajectoryMoment
public import FoliationQM.CurvedCurrentWeakConcentration
public import FoliationQM.GoodBadWeakConcentration
public import FoliationQM.GoodBadWasserstein

/-!
# Good-label dynamics and tails of the actual geometric current

Source: v13 `rem:wkb_rates_tails` and `eq:wasserstein_concentration_bound`, kinds C/D.

The full carrying domain retains the physical current and flow hypotheses
that construct its probability measure. Additional dynamical controls and
initial moments are localized to one good-label event for the entire time
interval. The finite-measure estimate retains the good mass in its forcing
term. Weak tail control and first-moment tail control remain separate.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.CurvedCurrentTailConcentration

open LorentzMatrixGroup CurvedCoordinateCurrent CurvedCoordinateDynamics
  CurvedCoordinateTrajectories CurvedEuclideanTrajectories CurvedQuantumForceCriterion
  CurvedCurrentTransport CurvedCurrentTrajectories CurvedProbabilityTrajectoryEstimate
  ProbabilityTrajectoryEstimate WeightedPhaseError WassersteinCoupling
  UniformTransportConcentration MeasureTheory Set Filter
open scoped ENNReal Topology Matrix.Norms.Operator BoundedContinuousFunction

variable {p : MassiveParameters} {g : Covector → Mat4} {R S : Covector → ℝ}
  {Phi : ℝ × (Fin 3 → ℝ) → (Fin 3 → ℝ)} {T Lx Lv : ℝ} {A : Set (Fin 3 → ℝ)}
  {Ω : ℝ → Set (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3))}
  {Y W : ℝ → EuclideanSpace ℝ (Fin 3)} {F : ℝ → ℝ}

/-- Actual good-label initial moments and one common event of physical controls; no bad-label moment is required. -/
structure GoodControl (h : FiniteFlowData p g R S Phi T A) (good : Set (Fin 3 → ℝ))
    (Ω : ℝ → Set (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)))
    (F : ℝ → ℝ) (Y0 W0 : EuclideanSpace ℝ (Fin 3)) : Prop where
  force_integrable : IntervalIntegrable F volume 0 T
  force_nonneg : ∀ s ∈ Icc 0 T, 0 ≤ F s
  label_controls : ∀ᵐ a ∂(initialProbability h : Measure (Fin 3 → ℝ)).restrict good,
    (∀ s ∈ Icc 0 T,
      (WithLp.toLp 2 (Phi (s, a)),
        WithLp.toLp 2 (spatialVelocity p g R S (s, Phi (s, a)))) ∈ Ω s) ∧
    (∀ᵐ s ∂volume.restrict (Icc 0 T), spatialForceNorm p g R S s (Phi (s, a)) ≤ F s)
  position_integrable : Integrable (fun a => ‖WithLp.toLp 2 a - Y0‖)
    ((initialProbability h : Measure (Fin 3 → ℝ)).restrict good)
  velocity_integrable : Integrable
    (fun a => ‖WithLp.toLp 2 (spatialVelocity p g R S (0, a)) - W0‖)
    ((initialProbability h : Measure (Fin 3 → ℝ)).restrict good)

/-- Actual physical good-label dynamics give genuine transported moments with the exact good-mass forcing factor. -/
theorem good_moment_bound (h : FiniteFlowData p g R S Phi T A)
    {good : Set (Fin 3 → ℝ)}
    (hT : 0 < T) (hLx : 0 ≤ Lx) (hLv : 0 ≤ Lv)
    (hRef : ReferenceCurve (geodesic p.c g) Ω T Y W)
    (hG : ∀ s ∈ Icc 0 T, ∀ z ∈ Ω s, ∀ w ∈ Ω s,
      ‖geodesic p.c g s z.1 z.2 - geodesic p.c g s w.1 w.2‖ ≤
        Lx * ‖z.1 - w.1‖ + Lv * ‖z.2 - w.2‖)
    (hGood : GoodControl h good Ω F (Y 0) (W 0)) :
    let μ := (initialProbability h : Measure (Fin 3 → ℝ))
    ∀ t ∈ Icc 0 T,
      Integrable (fun a => ‖WithLp.toLp 2 (Phi (t, a)) - Y t‖) (μ.restrict good) ∧
      (∫ a, ‖WithLp.toLp 2 (Phi (t, a)) - Y t‖ ∂μ.restrict good) ≤
        Real.exp (rate T Lx Lv * T) *
          ((∫ a, ‖WithLp.toLp 2 a - Y 0‖ ∂μ.restrict good) +
            T * (∫ a, ‖WithLp.toLp 2 (spatialVelocity p g R S (0, a)) - W 0‖
              ∂μ.restrict good) + μ.real good * (T * ∫ s in 0..T, F s)) := by
  dsimp only
  let ν := (initialProbability h : Measure (Fin 3 → ℝ)).restrict good
  have hpae : (fun a => ‖position (trajectory p Phi a) 0 - Y 0‖)
      =ᵐ[ν] (fun a => ‖WithLp.toLp 2 a - Y 0‖) :=
    ((ae_initial_position_eq h.toFlowData).fun_comp (fun x => ‖x - Y 0‖)).restrict
  have hvae : (fun a => ‖velocity p g R S (trajectory p Phi a) 0 - W 0‖)
      =ᵐ[ν] (fun a => ‖WithLp.toLp 2 (spatialVelocity p g R S (0, a)) - W 0‖) :=
    ((ae_initial_velocity_eq h.toFlowData).fun_comp (fun x => ‖x - W 0‖)).restrict
  have hDomain : ∀ᵐ a ∂ν, a ∈ A := ae_restrict_of_ae h.toFlowData.ae_mem_domain
  have hCurves : ∀ᵐ a ∂ν, ControlledCurve (geodesic p.c g) F Ω T
      (position (trajectory p Phi a)) (velocity p g R S (trajectory p Phi a))
      (force p g R S (trajectory p Phi a)) := by
    filter_upwards [hDomain, hGood.label_controls] with a ha hc
    exact controlledCurve_of_polar (polarCurveOn h.toFlowData ha hc.1)
      (by simpa only [trajectory_spatial] using hc.2)
  have hX : ∀ t ∈ Icc 0 T, AEMeasurable (fun a => position (trajectory p Phi a) t) ν :=
    fun _ ht => (h.toFlowData.aemeasurable_position ht).restrict
  have hb := RestrictedTrajectoryMoment.finite_measure_position_moment_bound ν
    hT hLx hLv hRef hG hGood.force_integrable hGood.force_nonneg hCurves hX
    (hGood.position_integrable.congr hpae.symm)
    (hGood.velocity_integrable.congr hvae.symm)
  intro t ht
  have hb' := hb t ht
  rw [integral_congr_ae hpae, integral_congr_ae hvae] at hb'
  simpa only [position_eq, ν, measureReal_restrict_apply_univ] using hb'

/-- The exact good-mass estimate is bounded by the usual source majorant because the actual good mass is at most one. -/
theorem good_moment_bound_le_source (h : FiniteFlowData p g R S Phi T A)
    {good : Set (Fin 3 → ℝ)}
    (hT : 0 < T) (hLx : 0 ≤ Lx) (hLv : 0 ≤ Lv)
    (hRef : ReferenceCurve (geodesic p.c g) Ω T Y W)
    (hG : ∀ s ∈ Icc 0 T, ∀ z ∈ Ω s, ∀ w ∈ Ω s,
      ‖geodesic p.c g s z.1 z.2 - geodesic p.c g s w.1 w.2‖ ≤
        Lx * ‖z.1 - w.1‖ + Lv * ‖z.2 - w.2‖)
    (hGood : GoodControl h good Ω F (Y 0) (W 0)) :
    let μ := (initialProbability h : Measure (Fin 3 → ℝ))
    ∀ t ∈ Icc 0 T,
      Integrable (fun a => ‖WithLp.toLp 2 (Phi (t, a)) - Y t‖) (μ.restrict good) ∧
      (∫ a, ‖WithLp.toLp 2 (Phi (t, a)) - Y t‖ ∂μ.restrict good) ≤
        Real.exp (rate T Lx Lv * T) *
          ((∫ a, ‖WithLp.toLp 2 a - Y 0‖ ∂μ.restrict good) +
            T * (∫ a, ‖WithLp.toLp 2 (spatialVelocity p g R S (0, a)) - W 0‖
              ∂μ.restrict good) + T * ∫ s in 0..T, F s) := by
  dsimp only
  intro t ht
  have hb := good_moment_bound h hT hLx hLv hRef hG hGood t ht
  refine ⟨hb.1, hb.2.trans ?_⟩
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  apply add_le_add le_rfl
  exact (mul_le_mul_of_nonneg_right (measureReal_le_one (μ := (initialProbability h : Measure (Fin 3 → ℝ))))
    (mul_nonneg hT.le (intervalIntegral.integral_nonneg hT.le hGood.force_nonneg))).trans_eq
      (one_mul _)

section Family

variable {ι : Type*}

/-- Actual restricted initial moments and force integrals produce a uniform vanishing majorant for genuine good-label transported moments. -/
theorem family_good_moment_majorant
    (P : ι → MassiveParameters) (g : Covector → Mat4)
    (amp phase : ι → Covector → ℝ)
    (Phi : ι → ℝ × (Fin 3 → ℝ) → (Fin 3 → ℝ)) (domains good : ι → Set (Fin 3 → ℝ))
    (H : ∀ i, FiniteFlowData (P i) g (amp i) (phase i) (Phi i) T (domains i)) (l : Filter ι)
    {c : ℝ} (hc : ∀ i, (P i).c = c) {F : ι → ℝ → ℝ}
    (hT : 0 < T) (hLx : 0 ≤ Lx) (hLv : 0 ≤ Lv)
    (hRef : ReferenceCurve (geodesic c g) Ω T Y W)
    (hG : ∀ s ∈ Icc 0 T, ∀ z ∈ Ω s, ∀ w ∈ Ω s,
      ‖geodesic c g s z.1 z.2 - geodesic c g s w.1 w.2‖ ≤
        Lx * ‖z.1 - w.1‖ + Lv * ‖z.2 - w.2‖)
    (hGood : ∀ᶠ i in l, GoodControl (H i) (good i) Ω (F i) (Y 0) (W 0))
    (hdx : Tendsto (fun i => ∫ a, ‖WithLp.toLp 2 a - Y 0‖
      ∂(initialProbability (H i) : Measure (Fin 3 → ℝ)).restrict (good i)) l (𝓝 0))
    (hdb : Tendsto (fun i => ∫ a,
      ‖WithLp.toLp 2 (spatialVelocity (P i) g (amp i) (phase i) (0, a)) - W 0‖
      ∂(initialProbability (H i) : Measure (Fin 3 → ℝ)).restrict (good i)) l (𝓝 0))
    (hJ : Tendsto (fun i => ∫ s in 0..T, F i s) l (𝓝 0)) :
    ∃ B : ι → ℝ, Tendsto B l (𝓝 0) ∧
      ∀ᶠ i in l, ∀ t ∈ Icc 0 T,
        Integrable (fun a => ‖WithLp.toLp 2 (Phi i (t, a)) - Y t‖)
          ((initialProbability (H i) : Measure (Fin 3 → ℝ)).restrict (good i)) ∧
        (∫ a, ‖WithLp.toLp 2 (Phi i (t, a)) - Y t‖
          ∂(initialProbability (H i) : Measure (Fin 3 → ℝ)).restrict (good i)) ≤ B i := by
  refine ⟨fun i => Real.exp (rate T Lx Lv * T) *
    ((∫ a, ‖WithLp.toLp 2 a - Y 0‖
      ∂(initialProbability (H i) : Measure (Fin 3 → ℝ)).restrict (good i)) +
    T * (∫ a, ‖WithLp.toLp 2 (spatialVelocity (P i) g (amp i) (phase i) (0, a)) - W 0‖
      ∂(initialProbability (H i) : Measure (Fin 3 → ℝ)).restrict (good i)) +
    T * ∫ s in 0..T, F i s), source_majorant_tendsto l T Lx Lv hdx hdb hJ, ?_⟩
  filter_upwards [hGood] with i hi
  exact good_moment_bound_le_source (H i) hT hLx hLv
    (by simpa only [hc i] using hRef) (by simpa only [hc i] using hG) hi

/-- Vanishing bad-label mass gives uniform bounded-continuous tests and actual weak current convergence without any bad first moment. -/
theorem family_weak_concentration_of_good_mass
    (P : ι → MassiveParameters) (g : Covector → Mat4)
    (amp phase : ι → Covector → ℝ)
    (Phi : ι → ℝ × (Fin 3 → ℝ) → (Fin 3 → ℝ)) (domains good : ι → Set (Fin 3 → ℝ))
    (H : ∀ i, FiniteFlowData (P i) g (amp i) (phase i) (Phi i) T (domains i)) (l : Filter ι)
    {c : ℝ} (hc : ∀ i, (P i).c = c) {F : ι → ℝ → ℝ}
    (hT : 0 < T) (hLx : 0 ≤ Lx) (hLv : 0 ≤ Lv)
    (hRef : ReferenceCurve (geodesic c g) Ω T Y W)
    (hG : ∀ s ∈ Icc 0 T, ∀ z ∈ Ω s, ∀ w ∈ Ω s,
      ‖geodesic c g s z.1 z.2 - geodesic c g s w.1 w.2‖ ≤
        Lx * ‖z.1 - w.1‖ + Lv * ‖z.2 - w.2‖)
    (hGood : ∀ᶠ i in l, GoodControl (H i) (good i) Ω (F i) (Y 0) (W 0))
    (hdx : Tendsto (fun i => ∫ a, ‖WithLp.toLp 2 a - Y 0‖
      ∂(initialProbability (H i) : Measure (Fin 3 → ℝ)).restrict (good i)) l (𝓝 0))
    (hdb : Tendsto (fun i => ∫ a,
      ‖WithLp.toLp 2 (spatialVelocity (P i) g (amp i) (phase i) (0, a)) - W 0‖
      ∂(initialProbability (H i) : Measure (Fin 3 → ℝ)).restrict (good i)) l (𝓝 0))
    (hJ : Tendsto (fun i => ∫ s in 0..T, F i s) l (𝓝 0))
    (hs : ∀ i, MeasurableSet (good i))
    (heta : Tendsto (fun i => (initialProbability (H i) : Measure (Fin 3 → ℝ)).real
      (good i)ᶜ) l (𝓝 0)) :
    (∀ f : EuclideanSpace ℝ (Fin 3) →ᵇ ℝ,
      TendstoUniformlyOn
        (fun i t => ∫ x, f x ∂(currentProbability (H i) t : Measure (EuclideanSpace ℝ (Fin 3))))
        (fun t => f (Y t)) l (Icc 0 T)) ∧
    (∀ t ∈ Icc 0 T, Tendsto (fun i => currentProbability (H i) t) l
      (𝓝 (Measure.dirac (Y t)).toProbabilityMeasure)) := by
  obtain ⟨B, hB, hb⟩ := family_good_moment_majorant P g amp phase Phi domains good H l hc
    hT hLx hLv hRef hG hGood hdx hdb hJ
  apply GoodBadWeakConcentration.family_uniform_weak_concentration
    (fun i => (initialProbability (H i) : Measure (Fin 3 → ℝ))) good hs
    (fun i t a => WithLp.toLp 2 (Phi i (t, a)))
    (fun i t => currentProbability (H i) t) l hRef.position_continuous ?_ hB heta
  filter_upwards [hb] with i hi t ht
  refine ⟨(H i).toFlowData.aemeasurable_position ht, ?_, ?_⟩
  · rw [currentProbability_eq_density (H i) ht]
    exact ((H i).toFlowData.euclidean_current_pushforward ht).symm
  · simpa only [dist_eq_norm] using hi t ht

/-- Additional genuine uniformly vanishing bad first moments give finite Wasserstein, time-supremum, bounded-test and weak convergence of the actual current. -/
theorem family_concentration_of_good_and_bad_moments
    (P : ι → MassiveParameters) (g : Covector → Mat4)
    (amp phase : ι → Covector → ℝ)
    (Phi : ι → ℝ × (Fin 3 → ℝ) → (Fin 3 → ℝ)) (domains good : ι → Set (Fin 3 → ℝ))
    (H : ∀ i, FiniteFlowData (P i) g (amp i) (phase i) (Phi i) T (domains i)) (l : Filter ι)
    {c : ℝ} (hc : ∀ i, (P i).c = c) {F : ι → ℝ → ℝ}
    (hT : 0 < T) (hLx : 0 ≤ Lx) (hLv : 0 ≤ Lv)
    (hRef : ReferenceCurve (geodesic c g) Ω T Y W)
    (hG : ∀ s ∈ Icc 0 T, ∀ z ∈ Ω s, ∀ w ∈ Ω s,
      ‖geodesic c g s z.1 z.2 - geodesic c g s w.1 w.2‖ ≤
        Lx * ‖z.1 - w.1‖ + Lv * ‖z.2 - w.2‖)
    (hGood : ∀ᶠ i in l, GoodControl (H i) (good i) Ω (F i) (Y 0) (W 0))
    (hdx : Tendsto (fun i => ∫ a, ‖WithLp.toLp 2 a - Y 0‖
      ∂(initialProbability (H i) : Measure (Fin 3 → ℝ)).restrict (good i)) l (𝓝 0))
    (hdb : Tendsto (fun i => ∫ a,
      ‖WithLp.toLp 2 (spatialVelocity (P i) g (amp i) (phase i) (0, a)) - W 0‖
      ∂(initialProbability (H i) : Measure (Fin 3 → ℝ)).restrict (good i)) l (𝓝 0))
    (hJ : Tendsto (fun i => ∫ s in 0..T, F i s) l (𝓝 0))
    (hs : ∀ i, MeasurableSet (good i)) {Bbad : ι → ℝ}
    (hBad : ∀ᶠ i in l, ∀ t ∈ Icc 0 T,
      Integrable (fun a => ‖WithLp.toLp 2 (Phi i (t, a)) - Y t‖)
        ((initialProbability (H i) : Measure (Fin 3 → ℝ)).restrict (good i)ᶜ) ∧
      (∫ a, ‖WithLp.toLp 2 (Phi i (t, a)) - Y t‖
        ∂(initialProbability (H i) : Measure (Fin 3 → ℝ)).restrict (good i)ᶜ) ≤ Bbad i)
    (hBb : Tendsto Bbad l (𝓝 0)) :
    CurvedCurrentWeakConcentration.Concentrates (fun i t => currentProbability (H i) t) Y T l := by
  obtain ⟨B, hB, hb⟩ := family_good_moment_majorant P g amp phase Phi domains good H l hc
    hT hLx hLv hRef hG hGood hdx hdb hJ
  have hcert : ∀ᶠ i in l, ∀ t ∈ Icc 0 T,
      AEMeasurable (fun a => WithLp.toLp 2 (Phi i (t, a)))
        (initialProbability (H i) : Measure (Fin 3 → ℝ)) ∧
      (currentProbability (H i) t : Measure (EuclideanSpace ℝ (Fin 3))) =
        (initialProbability (H i) : Measure (Fin 3 → ℝ)).map
          (fun a => WithLp.toLp 2 (Phi i (t, a))) ∧
      Integrable (fun a => dist (WithLp.toLp 2 (Phi i (t, a))) (Y t))
        ((initialProbability (H i) : Measure (Fin 3 → ℝ)).restrict (good i)) ∧
      Integrable (fun a => dist (WithLp.toLp 2 (Phi i (t, a))) (Y t))
        ((initialProbability (H i) : Measure (Fin 3 → ℝ)).restrict (good i)ᶜ) ∧
      (∫ a, dist (WithLp.toLp 2 (Phi i (t, a))) (Y t)
        ∂(initialProbability (H i) : Measure (Fin 3 → ℝ)).restrict (good i)) ≤ B i ∧
      (∫ a, dist (WithLp.toLp 2 (Phi i (t, a))) (Y t)
        ∂(initialProbability (H i) : Measure (Fin 3 → ℝ)).restrict (good i)ᶜ) ≤ Bbad i := by
    filter_upwards [hb, hBad] with i hgi hbi t ht
    refine ⟨(H i).toFlowData.aemeasurable_position ht, ?_, ?_⟩
    · rw [currentProbability_eq_density (H i) ht]
      exact ((H i).toFlowData.euclidean_current_pushforward ht).symm
    · simpa only [dist_eq_norm] using
        And.intro (hgi t ht).1 (And.intro (hbi t ht).1 (And.intro (hgi t ht).2 (hbi t ht).2))
  have h := GoodBadWasserstein.family_uniform_concentration
    (fun i => (initialProbability (H i) : Measure (Fin 3 → ℝ))) good hs
    (fun i t a => WithLp.toLp 2 (Phi i (t, a)))
    (fun i t => currentProbability (H i) t) l hT.le hcert hB hBb
  refine ⟨h.1, h.2.1, h.2.2, ?_, ?_⟩
  · exact UniformWeakConcentration.tendstoUniformlyOn_integral_of_uniform_cost
      (fun i t => currentProbability (H i) t) l hRef.position_continuous h.1 h.2.1
  · exact UniformWeakConcentration.tendsto_probabilityMeasure_of_uniform_cost
      (fun i t => currentProbability (H i) t) l hRef.position_continuous h.1 h.2.1

end Family
end FoliationQM.CurvedCurrentTailConcentration
