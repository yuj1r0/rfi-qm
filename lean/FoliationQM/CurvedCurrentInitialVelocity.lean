module

public import FoliationQM.InitialVelocityMoment
public import FoliationQM.CurvedCurrentConcentration

/-!
# Actual initial current velocity concentration

The physical velocity is expressed in Euclidean coordinates, with labels used
only as the measure domain. Flow regularity and future geometry derive its
measurability under the actual normalized initial current. Local Lipschitz
control and a functional anchor mismatch then yield genuine velocity moments.
The anchor is not required to be a carried regular physical point.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.CurvedCurrentInitialVelocity

open LorentzMatrixGroup CurvedCoordinateCurrent CurvedCurrentTransport
  CurvedCurrentConcentration CurvedQuantumForceCriterion Set Filter MeasureTheory
open scoped Topology NNReal ENNReal Matrix.Norms.Operator
set_option backward.isDefEq.respectTransparency false

/-- The defined initial coordinate velocity expressed in the actual Euclidean normed space. -/
def initialVelocity (p : MassiveParameters) (g : Covector → Mat4) (R S : Covector → ℝ)
    (y : EuclideanSpace ℝ (Fin 3)) : EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 (spatialVelocity p g R S (0, WithLp.ofLp y))

variable {p : MassiveParameters} {g : Covector → Mat4} {R S : Covector → ℝ}
  {Phi : ℝ × (Fin 3 → ℝ) → (Fin 3 → ℝ)} {T : ℝ} {A : Set (Fin 3 → ℝ)}
  {Y0 W0 : EuclideanSpace ℝ (Fin 3)}

/-- Actual flow regularity and the positive temporal denominator imply regional continuity of initial Euclidean velocity. -/
theorem continuousOn_initial_velocity (h : FlowData p g R S Phi T A) :
    ContinuousOn (fun a => WithLp.toLp 2 (spatialVelocity p g R S (0, a))) A := by
  intro a ha
  have ht : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, h.time_nonneg⟩
  have hr := h.regular a ha 0 ht
  have hq := h.normalization_pos a ha 0 ht
  have h0 := h.time_pos ha ht
  rw [h.initial_eq ha] at hr hq h0
  have hd := (contDiffAt_spatialVelocity hr hq h0.ne').differentiableAt_one.hasFDerivAt.comp a
    (hasFDerivAt_prodMk_right 0 a)
  exact ((PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ)).continuousAt.comp
    hd.continuousAt).continuousWithinAt

/-- Regional physical regularity gives actual velocity measurability under the normalized initial current. -/
theorem aemeasurable_initial_velocity (h : FlowData p g R S Phi T A) :
    AEMeasurable (fun a => WithLp.toLp 2 (spatialVelocity p g R S (0, a)))
      (normalizedInitial p g R S A) := by
  have hm : AEMeasurable (fun a => WithLp.toLp 2 (spatialVelocity p g R S (0, a)))
      ((volume : Measure (Fin 3 → ℝ)).restrict A) :=
    (continuousOn_initial_velocity h).aemeasurable h.domain_measurable
  exact (hm.mono_ac (withDensity_absolutelyContinuous (volume.restrict A)
    (fun a => ENNReal.ofReal (density p g R S (0, a))))).smul_measure
      (initialMass p g R S A)⁻¹

/-- A uniform local Lipschitz bound on the actual Euclidean velocity derives its initial-current integrability and moment estimate. -/
theorem velocity_error_bound_of_lipschitzOn
    (h : FiniteFlowData p g R S Phi T A) (L : ℝ≥0) {K : Set (EuclideanSpace ℝ (Fin 3))}
    (hx : Integrable (fun a => ‖WithLp.toLp 2 a - Y0‖)
      (initialProbability h : Measure (Fin 3 → ℝ)))
    (hK : ∀ᵐ a ∂(initialProbability h : Measure (Fin 3 → ℝ)), WithLp.toLp 2 a ∈ K)
    (hY : Y0 ∈ K) (hLip : LipschitzOnWith L (initialVelocity p g R S) K) :
    Integrable (fun a => ‖WithLp.toLp 2 (spatialVelocity p g R S (0, a)) - W0‖)
      (initialProbability h : Measure (Fin 3 → ℝ)) ∧
    (∫ a, ‖WithLp.toLp 2 (spatialVelocity p g R S (0, a)) - W0‖
      ∂(initialProbability h : Measure (Fin 3 → ℝ))) ≤
      (L : ℝ) * (∫ a, ‖WithLp.toLp 2 a - Y0‖
        ∂(initialProbability h : Measure (Fin 3 → ℝ))) + ‖initialVelocity p g R S Y0 - W0‖ := by
  exact InitialVelocityMoment.velocity_error_bound_of_lipschitzOn
    (initialProbability h : Measure (Fin 3 → ℝ)) (WithLp.toLp 2)
    (initialVelocity p g R S) L (aemeasurable_initial_velocity h.toFlowData) hx hK hY hLip

/-- Uniform local velocity control and a vanishing functional anchor mismatch derive actual initial-current velocity concentration. -/
theorem family_velocity_moment_tendsto_of_lipschitzOn
    {ι : Type*} (P : ι → MassiveParameters) (g : Covector → Mat4)
    (amp phase : ι → Covector → ℝ)
    (Phi : ι → ℝ × (Fin 3 → ℝ) → (Fin 3 → ℝ)) (domains : ι → Set (Fin 3 → ℝ))
    (H : ∀ i, FiniteFlowData (P i) g (amp i) (phase i) (Phi i) T (domains i))
    (l : Filter ι) (L : ℝ≥0) {K : ι → Set (EuclideanSpace ℝ (Fin 3))}
    (hGood : ∀ᶠ i in l,
      Integrable (fun a => ‖WithLp.toLp 2 a - Y0‖)
        (initialProbability (H i) : Measure (Fin 3 → ℝ)) ∧
      (∀ᵐ a ∂(initialProbability (H i) : Measure (Fin 3 → ℝ)), WithLp.toLp 2 a ∈ K i) ∧
      Y0 ∈ K i ∧ LipschitzOnWith L (initialVelocity (P i) g (amp i) (phase i)) (K i))
    (hdx : Tendsto (fun i => ∫ a, ‖WithLp.toLp 2 a - Y0‖
      ∂(initialProbability (H i) : Measure (Fin 3 → ℝ))) l (𝓝 0))
    (hanchor : Tendsto (fun i => ‖initialVelocity (P i) g (amp i) (phase i) Y0 - W0‖)
      l (𝓝 0)) :
    (∀ᶠ i in l, Integrable
      (fun a => ‖WithLp.toLp 2 (spatialVelocity (P i) g (amp i) (phase i) (0, a)) - W0‖)
      (initialProbability (H i) : Measure (Fin 3 → ℝ))) ∧
    Tendsto (fun i => ∫ a,
      ‖WithLp.toLp 2 (spatialVelocity (P i) g (amp i) (phase i) (0, a)) - W0‖
        ∂(initialProbability (H i) : Measure (Fin 3 → ℝ))) l (𝓝 0) := by
  apply InitialVelocityMoment.family_velocity_moment_tendsto_of_lipschitzOn
    (K := K) (x0 := Y0) (v0 := W0)
    (fun i => (initialProbability (H i) : Measure (Fin 3 → ℝ)))
    (fun _ => WithLp.toLp 2) (fun i => initialVelocity (P i) g (amp i) (phase i)) l L
    ?_ hdx hanchor
  exact hGood.mono fun i hi => ⟨aemeasurable_initial_velocity (H i).toFlowData, hi⟩

/-- Actual local Lipschitz and position-moment inputs supply the missing velocity-integrability field of physical source controls. -/
theorem sourceControl_of_lipschitzOn
    (h : FiniteFlowData p g R S Phi T A) (L : ℝ≥0) {K : Set (EuclideanSpace ℝ (Fin 3))}
    {Ω : ℝ → Set (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3))} {F : ℝ → ℝ}
    (hF : IntervalIntegrable F volume 0 T) (hFn : ∀ s ∈ Icc 0 T, 0 ≤ F s)
    (hLabels : ∀ᵐ a ∂(initialProbability h : Measure (Fin 3 → ℝ)),
      (∀ s ∈ Icc 0 T,
        (WithLp.toLp 2 (Phi (s, a)),
          WithLp.toLp 2 (spatialVelocity p g R S (s, Phi (s, a)))) ∈ Ω s) ∧
      (∀ᵐ s ∂volume.restrict (Icc 0 T), spatialForceNorm p g R S s (Phi (s, a)) ≤ F s))
    (hx : Integrable (fun a => ‖WithLp.toLp 2 a - Y0‖)
      (initialProbability h : Measure (Fin 3 → ℝ)))
    (hK : ∀ᵐ a ∂(initialProbability h : Measure (Fin 3 → ℝ)), WithLp.toLp 2 a ∈ K)
    (hY : Y0 ∈ K) (hLip : LipschitzOnWith L (initialVelocity p g R S) K) :
    SourceControl h Ω F Y0 W0 :=
  ⟨hF, hFn, hLabels, hx, (velocity_error_bound_of_lipschitzOn h L hx hK hY hLip).1⟩

end FoliationQM.CurvedCurrentInitialVelocity
